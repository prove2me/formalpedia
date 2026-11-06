-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_25
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-05T12:15:11.777186+00:00
-- url     : https://prove2.me/submissions/15b8523d-a1c4-4e25-8a84-4e5722722db5

import Mathlib
import Definitions.Def_FriendlyShadow_Gaussian_Model

set_option autoImplicit false



open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace C5747Geom

lemma mem_hull_range_iff {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (p : ι → E) (y : E) :
    y ∈ convexHull ℝ (Set.range p) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y := by
  constructor
  · intro hy
    have hsub : convexHull ℝ (Set.range p) ⊆
        {y | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        · simp
        · simp [Pi.single_apply]
      · rintro _ ⟨μ, hμ0, hμ1, rfl⟩ _ ⟨ν, hν0, hν1, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, ?_, ?_⟩
        · have := hμ0 i; have := hν0 i; positivity
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
        · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    exact hsub hy
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ p h0 h1 (fun i => Set.mem_range_self i) rfl

/-- Core: a positive convex representation of a point of an extreme set `e` forces the whole
sub-hull (intersected with `W`) into `e`. -/
lemma core_sub {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    [DecidableEq ι] {K e : Set E} (he : IsExtreme ℝ K e) (W : Submodule ℝ E) (p : ι → E)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1) (hme : ∑ i, w i • p i ∈ e)
    (hK : convexHull ℝ (Set.range p) ∩ (W : Set E) ⊆ K) (hmW : ∑ i, w i • p i ∈ W) :
    convexHull ℝ (Set.range p) ∩ (W : Set E) ⊆ e := by
  rintro y ⟨hy, hyW⟩
  by_cases hym : y = ∑ i, w i • p i
  · rw [hym]; exact hme
  obtain ⟨μ, hμ0, hμ1, hμy⟩ := (mem_hull_range_iff p y).1 hy
  have hne : (Finset.univ : Finset ι).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hw1
  set ε := Finset.univ.inf' hne w with hεdef
  have hε : 0 < ε := (Finset.lt_inf'_iff hne).2 (fun i _ => hw i)
  have hεw : ∀ i, ε ≤ w i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  have hμ1' : ∀ i, μ i ≤ 1 := fun i => by
    calc μ i ≤ ∑ j, μ j := Finset.single_le_sum (fun j _ => hμ0 j) (Finset.mem_univ i)
    _ = 1 := hμ1
  set z := ∑ i, ((1 + ε) * w i - ε * μ i) • p i with hzdef
  have hz : z ∈ convexHull ℝ (Set.range p) := by
    refine (mem_hull_range_iff p z).2 ⟨_, fun i => ?_, ?_, rfl⟩
    · nlinarith [hεw i, hμ1' i, hμ0 i, hw i]
    · rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hw1, hμ1]; ring
  have hzeq : z = (1 + ε) • (∑ i, w i • p i) - ε • y := by
    rw [hzdef, ← hμy]
    simp [sub_smul, mul_smul, Finset.smul_sum, Finset.sum_sub_distrib]
  have hzW : z ∈ W := by
    rw [hzeq]; exact W.sub_mem (W.smul_mem _ hmW) (W.smul_mem _ hyW)
  have h1 : (1 + ε) ≠ 0 := by positivity
  have hmseg : (∑ i, w i • p i) ∈ openSegment ℝ z y := by
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, by field_simp, ?_⟩
    rw [hzeq, smul_sub, smul_smul, smul_smul, one_div, inv_mul_cancel₀ h1, one_smul,
      div_eq_inv_mul]
    abel
  exact he.right_mem_of_mem_openSegment (hK ⟨hz, hzW⟩) (hK ⟨hy, hyW⟩) hme hmseg

lemma midpoint_mem_openSegment' {E : Type*} [AddCommGroup E] [Module ℝ E] (u v : E) :
    midpoint ℝ u v ∈ openSegment ℝ u v := by
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [midpoint_eq_smul_add, smul_add, invOf_eq_inv, one_div]

/-- An edge whose midpoint lies in an extreme segment lies in it. -/
lemma seg_sub_of_mid {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E} {u v u' v' : E}
    (h : Hirsch.Adj K u v) (h' : Hirsch.Adj K u' v')
    (hm : midpoint ℝ u v ∈ segment ℝ u' v') : segment ℝ u v ⊆ segment ℝ u' v' := by
  have hu : u ∈ K := h.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ K := h.2.1 (right_mem_segment ℝ u v)
  have hu' := h'.2.left_mem_of_mem_openSegment hu hv hm (midpoint_mem_openSegment' u v)
  have hv' := h'.2.right_mem_of_mem_openSegment hu hv hm (midpoint_mem_openSegment' u v)
  exact (convex_segment u' v').segment_subset hu' hv'

lemma seg_eq_of_common {E : Type*} [AddCommGroup E] [Module ℝ E] {K C : Set E} {u v u' v' : E}
    (h : Hirsch.Adj K u v) (h' : Hirsch.Adj K u' v')
    (hC : C ⊆ segment ℝ u v) (hC' : C ⊆ segment ℝ u' v')
    (hm : midpoint ℝ u v ∈ C) (hm' : midpoint ℝ u' v' ∈ C) :
    segment ℝ u v = segment ℝ u' v' :=
  le_antisymm (seg_sub_of_mid h h' (hC' hm)) (seg_sub_of_mid h' h (hC hm'))

open FriendlyShadow.Gaussian

variable {d n : ℕ}

/-- The witness predicate: the edge `e` with endpoints `u v` is pinned by the point set `t`. -/
def Pin (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (e : Set (EuclideanSpace ℝ (Fin d))) (t : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ u v, Hirsch.Adj (polygon W a) u v ∧ e = segment ℝ u v ∧
    convexHull ℝ (t : Set _) ∩ (W : Set _) ⊆ e ∧
    midpoint ℝ u v ∈ convexHull ℝ (t : Set _) ∩ (W : Set _)

lemma pin_inj (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d))
    {e₁ e₂ : Set (EuclideanSpace ℝ (Fin d))} {t : Finset (EuclideanSpace ℝ (Fin d))}
    (h₁ : Pin W a e₁ t) (h₂ : Pin W a e₂ t) : e₁ = e₂ := by
  obtain ⟨u, v, hA, rfl, hC, hm⟩ := h₁
  obtain ⟨u', v', hA', rfl, hC', hm'⟩ := h₂
  exact seg_eq_of_common hA hA' hC hC' hm hm'

set_option maxHeartbeats 1000000 in
lemma pin_exists (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) {e : Set (EuclideanSpace ℝ (Fin d))}
    (he : e ∈ edges (polygon W a)) :
    ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ Finset.univ.image a ∧ t.card ≤ d + 1 ∧
      Pin W a e t := by
  classical
  obtain ⟨u, v, hA, rfl⟩ := he
  have hu : u ∈ polygon W a := hA.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := hA.2.1 (right_mem_segment ℝ u v)
  have hmK : midpoint ℝ u v ∈ polygon W a :=
    (convex_convexHull ℝ _).inter W.convex |>.segment_subset hu hv
      (by rw [segment_eq_image_lineMap]; exact ⟨1/2, by norm_num, by
        rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num⟩)
  obtain ⟨ι, _, z, w, hz, hzi, hw0, hw1, hwm⟩ := eq_pos_convex_span_of_mem_convexHull hmK.1
  refine ⟨Finset.univ.image z, ?_, ?_, u, v, hA, rfl, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, hj⟩ := hz ⟨i, rfl⟩
    exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, hj⟩
  · calc (Finset.univ.image z).card ≤ Fintype.card ι := Finset.card_image_le.trans (by simp)
      _ ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range z)) + 1 := hzi.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) + 1 :=
          Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = d + 1 := by simp
  · have hco : ((Finset.univ.image z : Finset _) : Set (EuclideanSpace ℝ (Fin d))) = Set.range z := by
      simp
    rw [hco]
    refine core_sub hA.2 W z w hw0 hw1 ?_ ?_ ?_
    · rw [hwm]
      rw [segment_eq_image_lineMap]
      exact ⟨1/2, by norm_num, by
        rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num⟩
    · rintro x ⟨hx, hxW⟩
      exact ⟨convexHull_mono hz hx, hxW⟩
    · rw [hwm]; exact hmK.2
  · have hco : ((Finset.univ.image z : Finset _) : Set (EuclideanSpace ℝ (Fin d))) = Set.range z := by
      simp
    rw [hco]
    refine ⟨?_, hmK.2⟩
    rw [← hwm]
    exact mem_convexHull_of_exists_fintype w z (fun i => (hw0 i).le) hw1
      (fun i => Set.mem_range_self i) rfl

lemma card_small_subsets {α : Type*} [DecidableEq α] (U : Finset α) (D : ℕ) :
    (U.powerset.filter (fun t => t.card ≤ D)).card ≤ (D + 1) * (U.card + 1) ^ D := by
  have hsub : U.powerset.filter (fun t => t.card ≤ D) ⊆
      (Finset.range (D + 1)).biUnion (fun k => U.powersetCard k) := by
    intro t ht
    rw [Finset.mem_filter, Finset.mem_powerset] at ht
    rw [Finset.mem_biUnion]
    exact ⟨t.card, Finset.mem_range.2 (Nat.lt_succ_of_le ht.2),
      Finset.mem_powersetCard.2 ⟨ht.1, rfl⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (D + 1), (U.powersetCard k).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (D + 1), (U.card + 1) ^ D := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.card_powersetCard]
        calc U.card.choose k ≤ U.card ^ k := Nat.choose_le_pow _ _
          _ ≤ (U.card + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ _) _
          _ ≤ (U.card + 1) ^ D :=
              Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    _ = (D + 1) * (U.card + 1) ^ D := by simp

set_option maxHeartbeats 1000000 in
/-- Deterministic edge bound. -/
theorem edgeCount_le (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    edgeCount (polygon W a) ≤ (d + 2) * (n + 1) ^ (d + 1) := by
  classical
  set U : Finset (EuclideanSpace ℝ (Fin d)) := Finset.univ.image a
  set T : Finset (Finset (EuclideanSpace ℝ (Fin d))) := U.powerset.filter (fun t => t.card ≤ d + 1)
  let f : Set (EuclideanSpace ℝ (Fin d)) → Finset (EuclideanSpace ℝ (Fin d)) := fun e =>
    if h : ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ U ∧ t.card ≤ d + 1 ∧ Pin W a e t
    then h.choose else ∅
  have hf : ∀ e ∈ edges (polygon W a), f e ⊆ U ∧ (f e).card ≤ d + 1 ∧ Pin W a e (f e) := by
    intro e he
    have h : ∃ t : Finset (EuclideanSpace ℝ (Fin d)), t ⊆ U ∧ t.card ≤ d + 1 ∧ Pin W a e t :=
      pin_exists W a he
    have hfe : f e = h.choose := dif_pos h
    rw [hfe]
    exact h.choose_spec
  have h1 : edgeCount (polygon W a) ≤ (T : Set (Finset (EuclideanSpace ℝ (Fin d)))).ncard := by
    unfold edgeCount
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Finset.finite_toSet T)
    · intro e he
      obtain ⟨h1, h2, -⟩ := hf e he
      simp [T, Finset.mem_powerset, h1, h2]
    · intro e₁ he₁ e₂ he₂ heq
      have p1 := (hf e₁ he₁).2.2
      have p2 := (hf e₂ he₂).2.2
      rw [heq] at p1
      exact pin_inj W a p1 p2
  rw [Set.ncard_coe_finset] at h1
  have hU : U.card ≤ n := Finset.card_image_le.trans (by simp)
  calc edgeCount (polygon W a) ≤ T.card := h1
    _ ≤ (d + 1 + 1) * (U.card + 1) ^ (d + 1) := card_small_subsets U (d + 1)
    _ ≤ (d + 2) * (n + 1) ^ (d + 1) :=
        Nat.mul_le_mul (le_refl _) (Nat.pow_le_pow_left (Nat.succ_le_succ hU) _)

end C5747Geom

namespace C5747Meas

lemma mem_hull_range_iff' {E : Type*} [AddCommGroup E] [Module ℝ E] {ι : Type*} [Fintype ι]
    (p : ι → E) (y : E) :
    y ∈ convexHull ℝ (Set.range p) ↔
      ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y := by
  classical
  constructor
  · intro hy
    have hsub : convexHull ℝ (Set.range p) ⊆
        {y | ∃ μ : ι → ℝ, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∑ i, μ i • p i = y} := by
      apply convexHull_min
      · rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_, ?_, ?_⟩
        · intro i
          by_cases h : i = j
          · subst h; simp
          · simp [h]
        · simp
        · simp [Pi.single_apply]
      · rintro _ ⟨μ, hμ0, hμ1, rfl⟩ _ ⟨ν, hν0, hν1, rfl⟩ s t hs ht hst
        refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, ?_, ?_⟩
        · have := hμ0 i; have := hν0 i; positivity
        · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
        · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
    exact hsub hy
  · rintro ⟨μ, h0, h1, rfl⟩
    exact mem_convexHull_of_exists_fintype μ p h0 h1 (fun i => Set.mem_range_self i) rfl

/-- The graph of a continuously varying finite convex hull is closed. -/
lemma isClosed_hull {X : Type*} [TopologicalSpace X] {ι : Type*} [Fintype ι]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : X → ι → E) (hF : Continuous F) :
    IsClosed {p : X × E | p.2 ∈ convexHull ℝ (Set.range (F p.1))} := by
  have : CompactSpace (stdSimplex ℝ ι) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ ι)
  have hcont : Continuous (fun q : (X × E) × stdSimplex ℝ ι => ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).smul
        ((continuous_apply i).comp (hF.comp (continuous_fst.comp continuous_fst))))
  have hC : IsClosed {q : (X × E) × stdSimplex ℝ ι | ∑ i, (q.2 : ι → ℝ) i • F q.1.1 i = q.1.2} :=
    isClosed_eq hcont (continuous_snd.comp continuous_fst)
  have h := isClosedMap_fst_of_compactSpace _ hC
  convert h using 1
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_image, mem_hull_range_iff']
  constructor
  · rintro ⟨μ, h0, h1, h⟩; exact ⟨(p, ⟨μ, h0, h1⟩), h, rfl⟩
  · rintro ⟨⟨p', μ⟩, h, rfl⟩; exact ⟨μ, μ.2.1, μ.2.2, h⟩

lemma range_pair {E : Type*} (u v : E) : Set.range ![u, v] = {u, v} := by
  ext x
  simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h) <;> simp [← h]
  · rintro (h | h) <;> simp [h]

lemma isClosed_seg {X : Type*} [TopologicalSpace X] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f g : X → E) (hf : Continuous f) (hg : Continuous g) :
    IsClosed {p : X × E | p.2 ∈ segment ℝ (f p.1) (g p.1)} := by
  have h := isClosed_hull (fun x => ![f x, g x]) (by fun_prop)
  convert h using 1
  ext p; simp only [Set.mem_setOf_eq, range_pair, convexHull_pair]

/-- Images of `closed ∩ open` subsets of a σ-compact metric space are measurable. -/
lemma meas_image {Z P : Type*} [MetricSpace Z] [SigmaCompactSpace Z] [TopologicalSpace P]
    [T2Space P] [MeasurableSpace P] [OpensMeasurableSpace P] (f : Z → P) (hf : Continuous f)
    {C U : Set Z} (hC : IsClosed C) (hU : IsOpen U) : MeasurableSet (f '' (C ∩ U)) := by
  obtain ⟨F, hFc, -, hFU, -⟩ := hU.exists_iUnion_isClosed
  have hs : IsSigmaCompact (C ∩ U) := by
    rw [← hFU, Set.inter_iUnion]
    exact isSigmaCompact_iUnion _ (fun k =>
      IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hC.inter (hFc k)) (Set.subset_univ _))
  obtain ⟨K, hK, hKU⟩ := hs.image hf
  rw [← hKU]
  exact MeasurableSet.iUnion (fun k => (hK k).isClosed.measurableSet)

/-- A `∀`-clause over a σ-compact fibre with closed hypothesis and closed conclusion is measurable. -/
lemma meas_forall {B Y : Type*} [MetricSpace B] [MetricSpace Y] [SigmaCompactSpace (B × Y)]
    [MeasurableSpace B] [OpensMeasurableSpace B] (C D : Set (B × Y)) (hC : IsClosed C)
    (hD : IsClosed D) : MeasurableSet {b | ∀ y, (b, y) ∈ C → (b, y) ∈ D} := by
  have h := meas_image Prod.fst continuous_fst hC hD.isOpen_compl
  convert h.compl using 1
  ext b
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_inter_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_exists, not_and, not_not]

open FriendlyShadow.Gaussian

variable {d n : ℕ}

/-- `V_S(a) = conv(a_i : i ∈ S) ∩ W`. -/
def VS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  convexHull ℝ (Set.range (fun i : S => a i)) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))

/-- `S` pins the segment `[u, v]`: `V_S(a) ⊆ [u, v]` and the midpoint lies in `V_S(a)`. -/
def RS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :
    Prop :=
  VS W S b.1 ⊆ segment ℝ b.2.1 b.2.2 ∧ midpoint ℝ b.2.1 b.2.2 ∈ VS W S b.1

lemma isClosed_VS {X : Type*} [TopologicalSpace X] (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) (F : X → Fin n → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Continuous g) :
    IsClosed {x | g x ∈ VS W S (F x)} := by
  have h1 := (isClosed_hull (fun a : Fin n → EuclideanSpace ℝ (Fin d) => fun i : S => a i)
    (continuous_pi (fun i => continuous_apply _))).preimage (hF.prodMk hg)
  have h2 := (Submodule.closed_of_finiteDimensional W).preimage hg
  exact h1.inter h2

lemma isClosed_K {X : Type*} [TopologicalSpace X] (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (F : X → Fin n → EuclideanSpace ℝ (Fin d)) (hF : Continuous F)
    (g : X → EuclideanSpace ℝ (Fin d)) (hg : Continuous g) :
    IsClosed {x | g x ∈ polygon W (F x)} := by
  have h1 := (isClosed_hull (fun a : Fin n → EuclideanSpace ℝ (Fin d) => a) continuous_id).preimage
    (hF.prodMk hg)
  have h2 := (Submodule.closed_of_finiteDimensional W).preimage hg
  exact h1.inter h2

lemma isClosed_segm {X : Type*} [TopologicalSpace X] (f g h : X → EuclideanSpace ℝ (Fin d))
    (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    IsClosed {x | h x ∈ segment ℝ (f x) (g x)} :=
  (isClosed_seg f g hf hg).preimage (continuous_id.prodMk hh)

lemma mid_eq (u v : EuclideanSpace ℝ (Fin d)) : midpoint ℝ u v = (2 : ℝ)⁻¹ • (u + v) := by
  rw [midpoint_eq_smul_add, invOf_eq_inv]

lemma meas_RS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | RS W S b} := by
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ VS W S p.1.1} {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2}
    (isClosed_VS W S _ (by fun_prop) _ (by fun_prop)) (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
  have h2 : IsClosed {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | midpoint ℝ b.2.1 b.2.2 ∈ VS W S b.1} := by
    simp only [mid_eq]
    exact isClosed_VS W S _ (by fun_prop) _ (by fun_prop)
  convert h1.inter h2.measurableSet using 1
  ext b
  simp only [RS, Set.mem_setOf_eq, Set.mem_inter_iff]
  rfl

lemma extreme_clause_iff (K B : Set (EuclideanSpace ℝ (Fin d))) :
    (∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K → ∀ ⦃z⦄, z ∈ B → z ∈ openSegment ℝ x y → x ∈ B) ↔
      ∀ p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ,
        (p.1 ∈ K ∧ p.2.1 ∈ K ∧ (1 - p.2.2) • p.1 + p.2.2 • p.2.1 ∈ B) →
          (p.2.2 ≤ 0 ∨ 1 ≤ p.2.2 ∨ p.1 ∈ B) := by
  constructor
  · rintro H ⟨x, y, t⟩ ⟨hx, hy, hz⟩
    by_contra hc
    simp only [not_or, not_le] at hc
    obtain ⟨h0, h1, hxB⟩ := hc
    exact hxB (H hx hy hz (by rw [openSegment_eq_image]; exact ⟨t, ⟨h0, h1⟩, rfl⟩))
  · intro H x hx y hy z hz hzs
    rw [openSegment_eq_image] at hzs
    obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hzs
    rcases H (x, y, t) ⟨hx, hy, hz⟩ with h | h | h
    · exact absurd h (not_le.mpr h0)
    · exact absurd h (not_le.mpr h1)
    · exact h

set_option maxHeartbeats 1000000 in
lemma meas_Adj (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2} := by
  have h0 : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | b.2.1 ≠ b.2.2} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet.compl
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2} {p | p.2 ∈ polygon W p.1.1}
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    (isClosed_K W _ (by fun_prop) _ (by fun_prop))
  have hC : IsClosed {p : ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ) |
      p.2.1 ∈ polygon W p.1.1 ∧ p.2.2.1 ∈ polygon W p.1.1 ∧
      (1 - p.2.2.2) • p.2.1 + p.2.2.2 • p.2.2.1 ∈ segment ℝ p.1.2.1 p.1.2.2} :=
    (isClosed_K W _ (by fun_prop) _ (by fun_prop)).inter
      ((isClosed_K W _ (by fun_prop) _ (by fun_prop)).inter
        (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))
  have hD : IsClosed {p : ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) × ℝ) |
      p.2.2.2 ≤ 0 ∨ 1 ≤ p.2.2.2 ∨ p.2.1 ∈ segment ℝ p.1.2.1 p.1.2.2} := by
    simp only [Set.setOf_or]
    exact (isClosed_le (by fun_prop) continuous_const).union ((isClosed_le continuous_const (by fun_prop)).union
      (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)))
  have h2 := meas_forall _ _ hC hD
  convert h0.inter (h1.inter h2) using 1
  ext b
  simp only [Hirsch.Adj, isExtreme_iff, Set.mem_setOf_eq, Set.mem_inter_iff, extreme_clause_iff]
  rfl

end C5747Meas

namespace C5747Cnt

open FriendlyShadow.Gaussian C5747Meas C5747Geom

variable {d n : ℕ}

lemma seg_param {u v x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ segment ℝ u v) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ x = u + s • (v - u) := by
  rw [segment_eq_image'] at hx
  obtain ⟨s, ⟨h0, h1⟩, rfl⟩ := hx
  exact ⟨s, h0, h1, rfl⟩

lemma seg_ends {u v u' v' : EuclideanSpace ℝ (Fin d)} (hne : u ≠ v)
    (h : segment ℝ u v = segment ℝ u' v') : (u' = u ∧ v' = v) ∨ (u' = v ∧ v' = u) := by
  have hu' : u' ∈ segment ℝ u v := by rw [h]; exact left_mem_segment ℝ u' v'
  have hv' : v' ∈ segment ℝ u v := by rw [h]; exact right_mem_segment ℝ u' v'
  have hu : u ∈ segment ℝ u' v' := by rw [← h]; exact left_mem_segment ℝ u v
  have hv : v ∈ segment ℝ u' v' := by rw [← h]; exact right_mem_segment ℝ u v
  obtain ⟨s, hs0, hs1, hs⟩ := seg_param hu'
  obtain ⟨t, ht0, ht1, ht⟩ := seg_param hv'
  obtain ⟨p, hp0, hp1, hp⟩ := seg_param hu
  obtain ⟨q, hq0, hq1, hq⟩ := seg_param hv
  have e1 : v' - u' = (t - s) • (v - u) := by rw [ht, hs]; module
  have e2 : v - u = (q - p) • (v' - u') := by
    calc v - u = (u' + q • (v' - u')) - (u' + p • (v' - u')) := by rw [← hq, ← hp]
      _ = (q - p) • (v' - u') := by module
  have e3 : (1 - (q - p) * (t - s)) • (v - u) = 0 := by
    rw [sub_smul, one_smul, mul_smul, ← e1, ← e2, sub_self]
  have hvu : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have e4 : (q - p) * (t - s) = 1 := by
    have := (smul_eq_zero.mp e3).resolve_right hvu; linarith
  have h1 : (t - s) ^ 2 ≤ 1 := by nlinarith
  have h2 : (q - p) ^ 2 ≤ 1 := by nlinarith
  have h3 : (t - s) ^ 2 * (q - p) ^ 2 = 1 := by rw [← mul_pow, mul_comm, e4]; norm_num
  have h4 : 1 ≤ (t - s) ^ 2 := by nlinarith
  have h5 : (t - s - 1) * (t - s + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h5 with h6 | h6
  · have hs' : s = 0 := by linarith
    have ht' : t = 1 := by linarith
    left; constructor
    · rw [hs, hs']; simp
    · rw [ht, ht']; simp
  · have hs' : s = 1 := by linarith
    have ht' : t = 0 := by linarith
    right; constructor
    · rw [hs, hs']; simp
    · rw [ht, ht']; simp

/-- Lexicographic order on coordinates, used to orient each edge. -/
def lexLt (u v : EuclideanSpace ℝ (Fin d)) : Prop :=
  toLex (WithLp.ofLp u) < toLex (WithLp.ofLp v)

lemma lex_total {u v : EuclideanSpace ℝ (Fin d)} (h : u ≠ v) : lexLt u v ∨ lexLt v u := by
  unfold lexLt
  rcases lt_trichotomy (toLex (WithLp.ofLp u)) (toLex (WithLp.ofLp v)) with h1 | h1 | h1
  · exact Or.inl h1
  · exfalso
    have h2 : WithLp.ofLp u = WithLp.ofLp v := toLex.injective h1
    have := congrArg (WithLp.toLp 2) h2
    exact h (by simpa using this)
  · exact Or.inr h1

lemma lex_asymm {u v : EuclideanSpace ℝ (Fin d)} (h : lexLt u v) : ¬ lexLt v u :=
  lt_asymm h

lemma meas_lex : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
    EuclideanSpace ℝ (Fin d) | lexLt b.2.1 b.2.2} := by
  have : {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | lexLt b.2.1 b.2.2} =
      ⋃ i : Fin d, ({b | ∀ j, j < i → (WithLp.ofLp b.2.1) j = (WithLp.ofLp b.2.2) j} ∩
        {b | (WithLp.ofLp b.2.1) i < (WithLp.ofLp b.2.2) i}) := by
    ext b
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    rfl
  rw [this]
  refine MeasurableSet.iUnion fun i => MeasurableSet.inter ?_ ?_
  · refine IsClosed.measurableSet ?_
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun j => isClosed_iInter fun _ => isClosed_eq (by fun_prop) (by fun_prop)
  · exact (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet

/-- A fixed injective ranking of index sets. -/
noncomputable def rk (S : Finset (Fin n)) : ℕ := (Fintype.equivFin (Finset (Fin n)) S : ℕ)

lemma rk_inj {S S' : Finset (Fin n)} (h : rk S = rk S') : S = S' :=
  (Fintype.equivFin (Finset (Fin n))).injective (Fin.ext h)

/-- Oriented edges `(a, u, v)` minimally pinned by `S`. -/
def BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    Set ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {b | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2 ∧ RS W S b ∧
    (∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b) ∧ lexLt b.2.1 b.2.2}

lemma meas_BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet (BS W S) := by
  classical
  have hmin : MeasurableSet {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d) | ∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b} := by
    have : {b : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
        EuclideanSpace ℝ (Fin d) | ∀ S' : Finset (Fin n), rk S' < rk S → ¬ RS W S' b} =
        ⋂ S' ∈ (Finset.univ.filter (fun S' : Finset (Fin n) => rk S' < rk S)),
          {b | RS W S' b}ᶜ := by
      ext b; simp
    rw [this]
    exact Finset.measurableSet_biInter _ (fun S' _ => (meas_RS W S').compl)
  exact (meas_Adj W).inter ((meas_RS W S).inter (hmin.inter meas_lex))

lemma injOn_BS (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    Set.InjOn Prod.fst (BS W S) := by
  rintro ⟨a, u, v⟩ ⟨hA, hR, -, hL⟩ ⟨a', u', v'⟩ ⟨hA', hR', -, hL'⟩ hfst
  simp only at hfst
  subst hfst
  have hseg := seg_eq_of_common hA hA' hR.1 hR'.1 hR.2 hR'.2
  rcases seg_ends hA.1 hseg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hL' (lex_asymm hL)

lemma meas_G (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n)) :
    MeasurableSet (Prod.fst '' BS W S) :=
  (meas_BS W S).image_of_continuousOn_injOn continuous_fst.continuousOn (injOn_BS W S)

lemma RS_swap (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (S : Finset (Fin n))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (u v : EuclideanSpace ℝ (Fin d)) :
    RS W S (a, u, v) ↔ RS W S (a, v, u) := by
  simp only [RS, segment_symm ℝ u v, midpoint_comm u v]

lemma adj_swap {K : Set (EuclideanSpace ℝ (Fin d))} {u v : EuclideanSpace ℝ (Fin d)}
    (h : Hirsch.Adj K u v) : Hirsch.Adj K v u :=
  ⟨h.1.symm, by rw [segment_symm]; exact h.2⟩

set_option maxHeartbeats 1000000 in
open Classical in
lemma edgeCount_eq (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (a : Fin n → EuclideanSpace ℝ (Fin d)) :
    edgeCount (polygon W a) =
      (Finset.univ.filter (fun S : Finset (Fin n) => a ∈ Prod.fst '' BS W S)).card := by
  obtain ⟨F, hF⟩ : ∃ F : Finset (Finset (Fin n)),
      F = Finset.univ.filter (fun S : Finset (Fin n) => a ∈ Prod.fst '' BS W S) := ⟨_, rfl⟩
  rw [← hF]
  have hFmem : ∀ S, S ∈ (F : Set (Finset (Fin n))) ↔ a ∈ Prod.fst '' BS W S := by
    intro S; rw [Finset.mem_coe, hF]; simp
  let g : Finset (Fin n) → Set (EuclideanSpace ℝ (Fin d)) := fun S =>
    if h : a ∈ Prod.fst '' BS W S then segment ℝ h.choose.2.1 h.choose.2.2 else ∅
  have hgb : ∀ S b, b ∈ BS W S → b.1 = a → g S = segment ℝ b.2.1 b.2.2 := by
    intro S b hb hba
    have h : a ∈ Prod.fst '' BS W S := ⟨b, hb, hba⟩
    have h1 : g S = segment ℝ h.choose.2.1 h.choose.2.2 := dif_pos h
    rw [h1, injOn_BS W S h.choose_spec.1 hb (h.choose_spec.2.trans hba.symm)]
  have hinj : Set.InjOn g (F : Set (Finset (Fin n))) := by
    intro S1 hS1 S2 hS2 heq
    obtain ⟨b1, hb1, hb1a⟩ := (hFmem S1).1 hS1
    obtain ⟨b2, hb2, hb2a⟩ := (hFmem S2).1 hS2
    rw [hgb S1 b1 hb1 hb1a, hgb S2 b2 hb2 hb2a] at heq
    have hb : b1 = b2 := by
      rcases seg_ends hb1.1.1 heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Prod.ext (hb1a.trans hb2a.symm) (Prod.ext e1.symm e2.symm)
      · exfalso
        have h4 := hb2.2.2.2
        rw [e1, e2] at h4
        exact lex_asymm hb1.2.2.2 h4
    subst hb
    rcases lt_trichotomy (rk S1) (rk S2) with hlt | heq' | hgt
    · exact absurd hb1.2.1 (hb2.2.2.1 S1 hlt)
    · exact rk_inj heq'
    · exact absurd hb2.2.1 (hb1.2.2.1 S2 hgt)
  have himg : g '' (F : Set (Finset (Fin n))) = edges (polygon W a) := by
    ext e; constructor
    · rintro ⟨S, hS, rfl⟩
      obtain ⟨b, hb, hba⟩ := (hFmem S).1 hS
      rw [hgb S b hb hba]
      exact ⟨b.2.1, b.2.2, hba ▸ hb.1, rfl⟩
    · intro he
      obtain ⟨t, ht, -, u, v, hA, rfl, hsub, hmid⟩ := pin_exists W a he
      let S0 : Finset (Fin n) := Finset.univ.filter (fun i => a i ∈ t)
      have hrange : Set.range (fun i : S0 => a i) = (t : Set (EuclideanSpace ℝ (Fin d))) := by
        ext x; constructor
        · rintro ⟨⟨i, hi⟩, rfl⟩; exact (Finset.mem_filter.1 hi).2
        · intro hx
          obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (ht hx)
          exact ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩⟩, rfl⟩
      have hV : VS W S0 a = convexHull ℝ (t : Set (EuclideanSpace ℝ (Fin d))) ∩
          (W : Set (EuclideanSpace ℝ (Fin d))) := by
        rw [VS, hrange]
      have hex : ∃ k, ∃ S : Finset (Fin n), rk S = k ∧ ∃ u' v', Hirsch.Adj (polygon W a) u' v' ∧
          segment ℝ u v = segment ℝ u' v' ∧ RS W S (a, u', v') := by
        refine ⟨_, S0, rfl, u, v, hA, rfl, ?_⟩
        show VS W S0 a ⊆ segment ℝ u v ∧ midpoint ℝ u v ∈ VS W S0 a
        rw [hV]; exact ⟨hsub, hmid⟩
      obtain ⟨S1, hrk, u1, v1, hA1, he1, hR1⟩ := Nat.find_spec hex
      have hmin : ∀ S' : Finset (Fin n), rk S' < rk S1 → ∀ u' v',
          Hirsch.Adj (polygon W a) u' v' → segment ℝ u v = segment ℝ u' v' →
            ¬ RS W S' (a, u', v') := by
        intro S' hlt u' v' hA' he' hR'
        exact Nat.find_min hex (by rw [← hrk]; exact hlt) ⟨S', rfl, u', v', hA', he', hR'⟩
      rcases lex_total hA1.1 with hl | hl
      · have hb : ((a, u1, v1) : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d)) ∈ BS W S1 :=
          ⟨hA1, hR1, fun S' hlt hR' => hmin S' hlt u1 v1 hA1 he1 hR', hl⟩
        refine ⟨S1, (hFmem S1).2 ⟨_, hb, rfl⟩, ?_⟩
        rw [hgb S1 _ hb rfl, he1]
      · have hb : ((a, v1, u1) : (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
            EuclideanSpace ℝ (Fin d)) ∈ BS W S1 :=
          ⟨adj_swap hA1, (RS_swap W S1 a u1 v1).1 hR1,
            fun S' hlt hR' => hmin S' hlt u1 v1 hA1 he1 ((RS_swap W S' a u1 v1).2 hR'), hl⟩
        refine ⟨S1, (hFmem S1).2 ⟨_, hb, rfl⟩, ?_⟩
        rw [hgb S1 _ hb rfl, he1, segment_symm]
  unfold edgeCount
  rw [← himg, Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]

theorem measurable_edgeCount (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun a : Fin n → EuclideanSpace ℝ (Fin d) => (edgeCount (polygon W a) : ℝ≥0∞)) := by
  classical
  have h : (fun a : Fin n → EuclideanSpace ℝ (Fin d) => (edgeCount (polygon W a) : ℝ≥0∞)) =
      fun a => ∑ S : Finset (Fin n), (Prod.fst '' BS W S).indicator (fun _ => (1 : ℝ≥0∞)) a := by
    funext a
    rw [edgeCount_eq, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl (fun S _ => ?_)
    by_cases hS : a ∈ Prod.fst '' BS W S <;> simp [hS]
  rw [h]
  exact Finset.measurable_sum _ (fun S _ => measurable_const.indicator (meas_G W S))

end C5747Cnt


/-! O1a: measurability of the edge events `E_I` (Lusin–Souslin on oriented witnesses). -/
namespace FSMeasE

open FriendlyShadow.Gaussian C5747Meas C5747Cnt

variable {d n : ℕ}

/-- Oriented witnesses `(a, u, v)` of the event `E_I`. -/
def ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Set ((Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d)) :=
  {b | Hirsch.Adj (polygon W b.1) b.2.1 b.2.2 ∧
    (∀ x, x ∈ VS W I b.1 → x ∈ segment ℝ b.2.1 b.2.2) ∧
    (∀ x, x ∈ segment ℝ b.2.1 b.2.2 → x ∈ VS W I b.1) ∧ lexLt b.2.1 b.2.2}

lemma meas_ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    MeasurableSet (ES W I) := by
  have h1 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ VS W I p.1.1} {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2}
    (isClosed_VS W I _ (by fun_prop) _ (by fun_prop))
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
  have h2 := meas_forall (B := (Fin n → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin d) ×
      EuclideanSpace ℝ (Fin d)) (Y := EuclideanSpace ℝ (Fin d))
    {p | p.2 ∈ segment ℝ p.1.2.1 p.1.2.2} {p | p.2 ∈ VS W I p.1.1}
    (isClosed_segm _ _ _ (by fun_prop) (by fun_prop) (by fun_prop))
    (isClosed_VS W I _ (by fun_prop) _ (by fun_prop))
  exact (meas_Adj W).inter (h1.inter (h2.inter meas_lex))

lemma injOn_ES (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    Set.InjOn Prod.fst (ES W I) := by
  rintro ⟨a, u, v⟩ ⟨hA, h1, h2, hL⟩ ⟨a', u', v'⟩ ⟨hA', h1', h2', hL'⟩ hfst
  simp only at hfst
  subst hfst
  have hseg : segment ℝ u v = segment ℝ u' v' :=
    Set.Subset.antisymm (fun x hx => h1' x (h2 x hx)) (fun x hx => h1 x (h2' x hx))
  rcases seg_ends hA.1 hseg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact absurd hL' (lex_asymm hL)

theorem meas_edgeEvent (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (I : Finset (Fin n)) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) | edgeEvent W a I} := by
  have hV : ∀ a : Fin n → EuclideanSpace ℝ (Fin d),
      convexHull ℝ (a '' (I : Set (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = VS W I a := by
    intro a
    unfold VS
    rw [Set.image_eq_range]
    try rfl
  have hset : {a : Fin n → EuclideanSpace ℝ (Fin d) | edgeEvent W a I} = Prod.fst '' ES W I := by
    ext a
    constructor
    · rintro ⟨u, v, hA, he⟩
      rw [hV] at he
      rcases lex_total hA.1 with hl | hl
      · refine ⟨(a, u, v), ⟨hA, fun x hx => ?_, fun x hx => ?_, hl⟩, rfl⟩
        · rw [← he]; exact hx
        · rw [he]; exact hx
      · refine ⟨(a, v, u), ⟨adj_swap hA, fun x hx => ?_, fun x hx => ?_, hl⟩, rfl⟩
        · rw [segment_symm, ← he]; exact hx
        · rw [he, segment_symm]; exact hx
    · rintro ⟨⟨a', u, v⟩, ⟨hA, h1, h2, -⟩, rfl⟩
      refine ⟨u, v, hA, ?_⟩
      rw [hV]
      exact Set.Subset.antisymm (fun x hx => h1 x hx) (fun x hx => h2 x hx)
  rw [hset]
  exact (meas_ES W I).image_of_continuousOn_injOn continuous_fst.continuousOn (injOn_ES W I)

end FSMeasE


/-! O1c/O1b general position: almost surely (rows with densities)
(G1) any d+1 rows affinely span ℝᵈ, (G2) W together with any d-2 rows spans ℝᵈ. -/

namespace FSGP

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem meas_bad {d n k : ℕ} (c : (Fin n → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin n → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g) (i : Fin n) :
    MeasurableSet {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} := by
  set C : Set ((Fin k → ℝ) × (Fin n → EuclideanSpace ℝ (Fin d))) :=
    {p | ∑ j, p.1 j • g p.2 j = p.2 i - c p.2} with hCdef
  have hCc : IsClosed C := isClosed_eq (by fun_prop) (by fun_prop)
  have hC : IsSigmaCompact C := isSigmaCompact_univ.of_isClosed_subset hCc (Set.subset_univ _)
  have himg : {a : Fin n → EuclideanSpace ℝ (Fin d) |
      a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = Prod.snd '' C := by
    ext a
    simp only [Set.mem_ofPred_eq, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨f, hf⟩; exact ⟨(f, a), hf, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q.1, hq⟩
  obtain ⟨K, hK, hU⟩ := hC.image continuous_snd
  rw [himg, ← hU]
  exact MeasurableSet.iUnion fun m => (hK m).isClosed.measurableSet

theorem dens_null_coset {d k : ℕ} (hk : k < d) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (c0 : EuclideanSpace ℝ (Fin d)) (g0 : Fin k → EuclideanSpace ℝ (Fin d)) :
    densityMeasure μ {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} = 0 := by
  have hS : Submodule.span ℝ (Set.range g0) ≠ ⊤ := by
    intro h
    have h1 := finrank_range_le_card (R := ℝ) g0
    unfold Set.finrank at h1
    rw [h, finrank_top, finrank_euclideanSpace_fin, Fintype.card_fin] at h1
    omega
  have hA : AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) ≠ ⊤ := by
    intro h
    apply hS
    have := congrArg AffineSubspace.direction h
    rwa [AffineSubspace.direction_mk', AffineSubspace.direction_top] at this
  have hset : {x | x - c0 ∈ Submodule.span ℝ (Set.range g0)} =
      (AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) : Set (EuclideanSpace ℝ (Fin d))) := by
    ext x
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub]
  have h0 : volume ((AffineSubspace.mk' c0 (Submodule.span ℝ (Set.range g0)) :
      Set (EuclideanSpace ℝ (Fin d)))) = 0 :=
    Measure.addHaar_affineSubspace volume _ hA
  rw [hset]
  unfold densityMeasure
  exact withDensity_absolutelyContinuous _ _ h0

theorem one_row_null {d n k : ℕ} (hk : k < d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (i : Fin (n + 1)) (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d))
    (g : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → Fin k → EuclideanSpace ℝ (Fin d))
    (hc : Continuous c) (hg : Continuous g)
    (hci : ∀ a x, c (Function.update a i x) = c a)
    (hgi : ∀ a x, g (Function.update a i x) = g a) :
    rowLaw μ {a | a i - c a ∈ Submodule.span ℝ (Set.range (g a))} = 0 := by
  have : ∀ j, SigmaFinite (densityMeasure (μ j)) := fun j => by
    unfold densityMeasure; infer_instance
  set B := {a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) |
    a i - c a ∈ Submodule.span ℝ (Set.range (g a))} with hBdef
  have hB : MeasurableSet B := meas_bad c g hc hg i
  have hmp := MeasurePreserving.symm _
    (measurePreserving_piFinSuccAbove (fun j => densityMeasure (μ j)) i)
  unfold rowLaw
  rw [← hmp.measure_preimage_equiv B]
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ => EuclideanSpace ℝ (Fin d)) i).symm with hedef
  have hB' : MeasurableSet (e ⁻¹' B) := e.measurable hB
  rw [Measure.prod_apply_symm hB']
  have hsec : ∀ y, densityMeasure (μ i) ((fun x => (x, y)) ⁻¹' (e ⁻¹' B)) = 0 := by
    intro y
    have hset : (fun x => (x, y)) ⁻¹' (e ⁻¹' B) =
        {x | x - c (e (0, y)) ∈ Submodule.span ℝ (Set.range (g (e (0, y))))} := by
      ext x
      have h1 : e (x, y) = Function.update (e (0, y)) i x := by
        simp only [hedef, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.update_insertNth]
      simp only [Set.mem_preimage, hBdef, Set.mem_ofPred_eq]
      rw [h1, hci, hgi, Function.update_self]
    rw [hset]
    exact dens_null_coset hk _ _ _
  simp [hsec]

theorem gen_li {d n p : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin p → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w)
    (c : (Fin (n + 1) → EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin d)) (hc : Continuous c) :
    ∀ (m : ℕ) (s : Fin m → Fin (n + 1)), Function.Injective s → p + m ≤ d →
      (∀ k a x, c (Function.update a (s k) x) = c a) →
      ∀ᵐ a ∂rowLaw μ, LinearIndependent ℝ (Fin.append w (fun k => a (s k) - c a)) := by
  intro m
  induction m with
  | zero =>
    intro s _ _ _
    refine Filter.Eventually.of_forall (fun a => ?_)
    have h0 : (fun k : Fin 0 => a (s k) - c a) = Fin.elim0 := funext (fun k => k.elim0)
    rw [h0, Fin.append_elim0]
    exact hw.comp _ (Fin.cast_injective _)
  | succ m ih =>
    intro s hs hpm hcs
    have h1 := ih (s ∘ Fin.castSucc) (hs.comp (Fin.castSucc_injective m)) (by omega)
      (fun k a x => hcs _ a x)
    set i := s (Fin.last m) with hi
    have hne : ∀ k : Fin m, s k.castSucc ≠ i := fun k h =>
      (Fin.castSucc_lt_last k).ne (hs h)
    have hgc : Continuous (fun a : Fin (n + 1) → EuclideanSpace ℝ (Fin d) =>
        Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) := by
      refine continuous_pi (fun j => ?_)
      induction j using Fin.addCases with
      | left l => simp only [Fin.append_left]; exact continuous_const
      | right l => simp only [Fin.append_right]; exact (continuous_apply _).sub hc
    have h0 := one_row_null (k := p + m) (by omega) μ i c
      (fun a => Fin.append w (fun k : Fin m => a (s k.castSucc) - c a)) hc hgc
      (fun a x => hcs _ a x) (fun a x => by
        beta_reduce
        rw [hcs (Fin.last m) a x]
        congr 1
        funext k
        rw [Function.update_of_ne (hne k)])
    have h2 := measure_eq_zero_iff_ae_notMem.1 h0
    filter_upwards [h1, h2] with a ha1 ha2
    have hsn : (fun k : Fin (m + 1) => a (s k) - c a) =
        Fin.snoc (fun k : Fin m => a (s k.castSucc) - c a) (a i - c a) := by
      funext k
      induction k using Fin.lastCases with
      | last => simp [hi]
      | cast j => simp
    rw [hsn, Fin.append_snoc, linearIndependent_finSnoc]
    exact ⟨ha1, ha2⟩

/-- (G1) a.s.: for every injective `t : Fin (d+1) → Fin (n+1)` the `d` difference vectors are
linearly independent. -/
theorem g1_ae {d n : ℕ} (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d + 1) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0)) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ (Fin.elim0 : Fin 0 → EuclideanSpace ℝ (Fin d))
      (linearIndependent_empty_type) (fun a => a (t 0)) (continuous_apply _) d (t ∘ Fin.succ)
      (ht.comp (Fin.succ_injective _)) (by omega)
      (fun k a x => Function.update_of_ne (fun h => Fin.succ_ne_zero k (ht h).symm) _ _)
    filter_upwards [h] with a ha _
    rw [Fin.elim0_append] at ha
    have := ha.comp (Fin.cast (Nat.zero_add d).symm) (Fin.cast_injective _)
    simpa [Function.comp_def] using this
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

/-- (G2) a.s.: a fixed independent pair `w` together with any `d-2` distinct rows is independent. -/
theorem g2_ae {d n : ℕ} (hd : 2 ≤ d) (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ)
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hw : LinearIndependent ℝ w) :
    ∀ᵐ a ∂rowLaw μ, ∀ t : Fin (d - 2) → Fin (n + 1), Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k))) := by
  rw [ae_all_iff]
  intro t
  by_cases ht : Function.Injective t
  · have h := gen_li μ w hw (fun _ => 0) continuous_const (d - 2) t ht (by omega)
      (fun _ _ _ => rfl)
    filter_upwards [h] with a ha _
    simpa using ha
  · exact Filter.Eventually.of_forall (fun a h => absurd h ht)

end FSGP


/-! O1b/O1c deterministic part: under general position, every edge of `Q ∩ W` is
`conv(a_I) ∩ W` for a unique `I` with `|I| = d`. -/

namespace FSFace

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

/-- (G1) deterministic form: any `d+1` rows affinely span, with explicit coefficients. -/
def G1det {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ S : Finset (Fin n), d + 1 ≤ S.card → ∀ z : EuclideanSpace ℝ (Fin d),
    ∃ c : Fin n → ℝ, (∀ i, i ∉ S → c i = 0) ∧ ∑ i, c i = 0 ∧ ∑ i, c i • a i = z

/-- (G2) deterministic form: the hull of at most `d-1` rows meets `W` in at most one point. -/
def G2det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ J : Finset (Fin n), J.card + 1 ≤ d → ∀ x y : EuclideanSpace ℝ (Fin d), x ∈ W → y ∈ W →
    x ∈ convexHull ℝ (a '' ↑J) → y ∈ convexHull ℝ (a '' ↑J) → x = y

theorem hull_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ convexHull ℝ (a '' ↑J)) :
    ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧ (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧
      ∑ i, α i • a i = x := by
  classical
  have hsub : convexHull ℝ (a '' ↑J) ⊆ {y | ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧
      (∀ i, i ∉ J → α i = 0) ∧ ∑ i, α i = 1 ∧ ∑ i, α i • a i = y} := by
    apply convexHull_min
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨Pi.single j 1, fun i => ?_, fun i hi => ?_, by simp, by simp [Pi.single_apply]⟩
      · by_cases h : i = j
        · subst h; simp
        · simp [h]
      · have : i ≠ j := fun h => hi (h ▸ hj)
        simp [this]
    · rintro _ ⟨μ, hμ0, hμJ, hμ1, rfl⟩ _ ⟨ν, hν0, hνJ, hν1, rfl⟩ s t hs ht hst
      refine ⟨fun i => s * μ i + t * ν i, fun i => ?_, fun i hi => ?_, ?_, ?_⟩
      · have := hμ0 i; have := hν0 i; positivity
      · simp [hμJ i hi, hνJ i hi]
      · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hμ1, hν1, hst]
      · simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  exact hsub hx

theorem hull_of_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (J : Finset (Fin n))
    (α : Fin n → ℝ) (h0 : ∀ i, 0 ≤ α i) (hJ : ∀ i, i ∉ J → α i = 0) (h1 : ∑ i, α i = 1) :
    ∑ i, α i • a i ∈ convexHull ℝ (a '' ↑J) := by
  classical
  have e1 : ∑ i ∈ J, α i = ∑ i, α i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => hJ i hi)
  have e2 : ∑ i ∈ J, α i • a i = ∑ i, α i • a i :=
    Finset.sum_subset (Finset.subset_univ J) (fun i _ hi => by simp [hJ i hi])
  rw [← e2]
  exact (convex_convexHull ℝ _).sum_mem (fun i _ => h0 i) (e1.trans h1)
    (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem pert_eps {n : ℕ} (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (hc : ∀ i, c i ≠ 0 → 0 < wt i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, 0 ≤ wt i + ε * c i := by
  set Q := ∑ i, |c i| / wt i with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun i _ => div_nonneg (abs_nonneg _) (h0 i))
  refine ⟨1 / (1 + Q), by positivity, fun i => ?_⟩
  by_cases hci : c i = 0
  · simp [hci, h0 i]
  · have hw := hc i hci
    have hle : |c i| / wt i ≤ Q :=
      Finset.single_le_sum (f := fun i => |c i| / wt i)
        (fun j _ => div_nonneg (abs_nonneg _) (h0 j)) (Finset.mem_univ i)
    have h2 : |c i| ≤ Q * wt i := (div_le_iff₀ hw).1 hle
    have h3 := neg_abs_le (c i)
    have heq : wt i + 1 / (1 + Q) * c i = (wt i * (1 + Q) + c i) / (1 + Q) := by
      field_simp
    rw [heq]
    apply div_nonneg _ (by positivity)
    nlinarith

theorem pert_mem {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (wt c : Fin n → ℝ) (h0 : ∀ i, 0 ≤ wt i)
    (h1 : ∑ i, wt i = 1) (hc0 : ∑ i, c i = 0) (hc : ∀ i, c i ≠ 0 → 0 < wt i)
    (hmW : ∑ i, wt i • a i ∈ W) (hzW : ∑ i, c i • a i ∈ W) :
    ∃ ε : ℝ, 0 < ε ∧ ∑ i, wt i • a i + ε • ∑ i, c i • a i ∈ polygon W a := by
  obtain ⟨ε, hε, hεi⟩ := pert_eps wt c h0 hc
  refine ⟨ε, hε, ?_⟩
  show _ ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
  refine ⟨?_, W.add_mem hmW (W.smul_mem _ hzW)⟩
  have heq : ∑ i, wt i • a i + ε • ∑ i, c i • a i = ∑ i, (wt i + ε * c i) • a i := by
    simp [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun i _ => hεi i) ?_
    (fun i _ => subset_convexHull ℝ _ ⟨i, rfl⟩)
  simp [Finset.sum_add_distrib, ← Finset.mul_sum, h1, hc0]

theorem mid_mem_W {d n : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin d))}
    {a : Fin n → EuclideanSpace ℝ (Fin d)} {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) : midpoint ℝ u v ∈ W := by
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  rw [midpoint_eq_smul_add]
  exact W.smul_mem _ (W.add_mem hu.2 hv.2)

theorem mid_mem_seg {d' : ℕ} (u v : EuclideanSpace ℝ (Fin d')) : midpoint ℝ u v ∈ segment ℝ u v := by
  rw [segment_eq_image_lineMap]
  exact ⟨1/2, by norm_num, by
    rw [midpoint, AffineMap.lineMap_apply, AffineMap.lineMap_apply]; norm_num [invOf_eq_inv]⟩

/-- Key lemma (K): a positive convex representation of the midpoint of an edge uses at most `d` rows. -/
theorem key_card {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v) :
    (Finset.univ.filter (fun i => 0 < wt i)).card ≤ d := by
  classical
  by_contra hlt
  push_neg at hlt
  have hmW := mid_mem_W huv
  obtain ⟨z, hzW, hz⟩ : ∃ z ∈ W, z ∉ ℝ ∙ (v - u) := by
    by_contra h
    push_neg at h
    have hle : W ≤ ℝ ∙ (v - u) := fun z hz => h z hz
    have h1' := Submodule.finrank_mono hle
    have h2 := finrank_span_le_card (R := ℝ) ({v - u} : Set (EuclideanSpace ℝ (Fin d)))
    simp at h2
    omega
  obtain ⟨c, hcS, hc0, hcz⟩ := hG1 (Finset.univ.filter (fun i => 0 < wt i)) (by omega) z
  have hc : ∀ i, c i ≠ 0 → 0 < wt i := by
    intro i hci
    by_contra hw
    exact hci (hcS i (by simpa using hw))
  have hc' : ∀ i, (-c) i ≠ 0 → 0 < wt i := fun i h => hc i (by simpa using h)
  obtain ⟨ε₁, hε₁, hp₁⟩ := pert_mem W a wt c h0 h1 hc0 hc (hm ▸ hmW) (hcz ▸ hzW)
  obtain ⟨ε₂, hε₂, hp₂⟩ := pert_mem W a wt (-c) h0 h1 (by simp [hc0]) hc' (hm ▸ hmW)
    (by simpa [neg_smul, Finset.sum_neg_distrib, hcz] using W.neg_mem hzW)
  rw [hm, hcz] at hp₁
  have hneg : ∑ i, (-c) i • a i = -z := by simp [neg_smul, Finset.sum_neg_distrib, hcz]
  rw [hm, hneg] at hp₂
  set m := midpoint ℝ u v with hmdef
  have hopen : m ∈ openSegment ℝ (m + ε₂ • -z) (m + ε₁ • z) := by
    have hs : ε₁ + ε₂ ≠ 0 := by positivity
    have hab : ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂) = 1 := by field_simp
    have hab2 : ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂ = 0 := by ring
    refine ⟨ε₁ / (ε₁ + ε₂), ε₂ / (ε₁ + ε₂), by positivity, by positivity, hab, ?_⟩
    calc (ε₁ / (ε₁ + ε₂)) • (m + ε₂ • -z) + (ε₂ / (ε₁ + ε₂)) • (m + ε₁ • z)
        = (ε₁ / (ε₁ + ε₂) + ε₂ / (ε₁ + ε₂)) • m +
          (ε₂ / (ε₁ + ε₂) * ε₁ - ε₁ / (ε₁ + ε₂) * ε₂) • z := by module
      _ = m := by rw [hab, hab2, zero_smul, one_smul, add_zero]
  have hseg := huv.2.right_mem_of_mem_openSegment hp₂ hp₁ (mid_mem_seg u v) hopen
  rw [segment_eq_image'] at hseg
  obtain ⟨θ, _, hθ⟩ := hseg
  apply hz
  have hez : ε₁ • z = (θ - 1 / 2) • (v - u) := by
    have : m = u + (1 / 2 : ℝ) • (v - u) := by
      rw [hmdef, midpoint_eq_smul_add]; simp only [invOf_eq_inv]; module
    rw [this] at hθ
    have := congrArg (fun x => x - (u + (1 / 2 : ℝ) • (v - u))) hθ
    simp only [add_sub_cancel_left] at this
    rw [← this]; module
  have : z = ε₁⁻¹ • ((θ - 1 / 2) • (v - u)) := by
    rw [← hez, smul_smul, inv_mul_cancel₀ hε₁.ne', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem core_seg {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) {u v : EuclideanSpace ℝ (Fin d)}
    (huv : Hirsch.Adj (polygon W a) u v) (wt : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ wt i) (h1 : ∑ i, wt i = 1) (hm : ∑ i, wt i • a i = midpoint ℝ u v)
    (y : EuclideanSpace ℝ (Fin d))
    (hy : y ∈ convexHull ℝ (a '' ↑(Finset.univ.filter (fun i => 0 < wt i)))) (hyW : y ∈ W) :
    y ∈ segment ℝ u v := by
  classical
  obtain ⟨γ, hγ0, hγS, hγ1, hγy⟩ := hull_rep a _ y hy
  have hc : ∀ i, (wt - γ) i ≠ 0 → 0 < wt i := by
    intro i hi
    by_contra hw
    have hw0 : wt i = 0 := le_antisymm (not_lt.1 hw) (h0 i)
    have : γ i = 0 := hγS i (by simp [hw])
    exact hi (by simp [hw0, this])
  have hzsum : ∑ i, (wt - γ) i • a i = midpoint ℝ u v - y := by
    simp [sub_smul, Finset.sum_sub_distrib, hm, hγy]
  have hmW := mid_mem_W huv
  obtain ⟨ε, hε, hp⟩ := pert_mem W a wt (wt - γ) h0 h1
    (by simp [Finset.sum_sub_distrib, h1, hγ1]) hc (hm ▸ hmW)
    (hzsum ▸ W.sub_mem hmW hyW)
  rw [hm, hzsum] at hp
  have hyP : y ∈ polygon W a := by
    show y ∈ convexHull ℝ (Set.range a) ∩ (W : Set (EuclideanSpace ℝ (Fin d)))
    exact ⟨convexHull_mono (Set.image_subset_range _ _) hy, hyW⟩
  have hopen : midpoint ℝ u v ∈
      openSegment ℝ (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) y := by
    have hs : 1 + ε ≠ 0 := by positivity
    have hab : 1 / (1 + ε) + ε / (1 + ε) = 1 := by field_simp
    have hab1 : 1 / (1 + ε) * (1 + ε) = 1 := by field_simp
    have hab2 : ε / (1 + ε) - 1 / (1 + ε) * ε = 0 := by ring
    refine ⟨1 / (1 + ε), ε / (1 + ε), by positivity, by positivity, hab, ?_⟩
    calc (1 / (1 + ε)) • (midpoint ℝ u v + ε • (midpoint ℝ u v - y)) + (ε / (1 + ε)) • y
        = (1 / (1 + ε) * (1 + ε)) • midpoint ℝ u v + (ε / (1 + ε) - 1 / (1 + ε) * ε) • y := by
          module
      _ = midpoint ℝ u v := by rw [hab1, hab2, zero_smul, one_smul, add_zero]
  exact huv.2.right_mem_of_mem_openSegment hp hyP (mid_mem_seg u v) hopen

theorem mid_rep {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (u v : EuclideanSpace ℝ (Fin d))
    (α β : Fin n → ℝ) (hαu : ∑ i, α i • a i = u) (hβv : ∑ i, β i • a i = v) :
    ∑ i, ((α i + β i) / 2) • a i = midpoint ℝ u v := by
  have : ∑ i, ((α i + β i) / 2) • a i = (1 / 2 : ℝ) • (∑ i, α i • a i + ∑ i, β i • a i) := by
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    module
  rw [this, hαu, hβv, midpoint_eq_smul_add]
  simp only [invOf_eq_inv]
  module

theorem face_exists {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v) :
    ∃ I : Finset (Fin n), I.card = d ∧
      convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v := by
  classical
  have hu : u ∈ polygon W a := huv.2.1 (left_mem_segment ℝ u v)
  have hv : v ∈ polygon W a := huv.2.1 (right_mem_segment ℝ u v)
  have hrange : convexHull ℝ (Set.range a) = convexHull ℝ (a '' ↑(Finset.univ : Finset (Fin n))) := by
    rw [Finset.coe_univ, Set.image_univ]
  obtain ⟨α, hα0, -, hα1, hαu⟩ := hull_rep a Finset.univ u (hrange ▸ hu.1)
  obtain ⟨β, hβ0, -, hβ1, hβv⟩ := hull_rep a Finset.univ v (hrange ▸ hv.1)
  set wt : Fin n → ℝ := fun i => (α i + β i) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by have := hα0 i; have := hβ0 i; positivity
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1]; norm_num
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v α β hαu hβv
  set S := Finset.univ.filter (fun i => 0 < wt i) with hS
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hαS : ∀ i, i ∉ S → α i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have hβS : ∀ i, i ∉ S → β i = 0 := by
    intro i hi
    have : ¬ 0 < wt i := by simpa [hS] using hi
    have := hα0 i; have := hβ0 i
    simp only [hwt] at *
    linarith [not_lt.1 ‹¬ 0 < (α i + β i) / 2›]
  have huS : u ∈ convexHull ℝ (a '' ↑S) := hαu ▸ hull_of_rep a S α hα0 hαS hα1
  have hvS : v ∈ convexHull ℝ (a '' ↑S) := hβv ▸ hull_of_rep a S β hβ0 hβS hβ1
  refine ⟨S, le_antisymm hcard ?_, ?_⟩
  · by_contra hlt
    push_neg at hlt
    exact huv.1 (hG2 S (by omega) u v hu.2 hv.2 huS hvS)
  · apply Set.Subset.antisymm
    · rintro y ⟨hy, hyW⟩
      exact core_seg W a huv wt h0 h1 hm y hy hyW
    · exact ((convex_convexHull ℝ _).inter W.convex).segment_subset ⟨huS, hu.2⟩ ⟨hvS, hv.2⟩

theorem supp_cover {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG2 : G2det W a) (I : Finset (Fin n))
    (hI : I.card = d) {u v : EuclideanSpace ℝ (Fin d)} (hne : u ≠ v) (huW : u ∈ W) (hvW : v ∈ W)
    (α β : Fin n → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hαI : ∀ i, i ∉ I → α i = 0) (hα1 : ∑ i, α i = 1)
    (hαu : ∑ i, α i • a i = u) (hβ0 : ∀ i, 0 ≤ β i) (hβI : ∀ i, i ∉ I → β i = 0)
    (hβ1 : ∑ i, β i = 1) (hβv : ∑ i, β i • a i = v) :
    ∀ i ∈ I, 0 < α i + β i := by
  classical
  intro i hi
  by_contra hle
  push_neg at hle
  have hαi : α i = 0 := le_antisymm (by linarith [hβ0 i]) (hα0 i)
  have hβi : β i = 0 := le_antisymm (by linarith [hα0 i]) (hβ0 i)
  have hsub : ∀ j, j ∉ I.erase i → j = i ∨ j ∉ I := by
    intro j hj
    by_cases h : j = i
    · exact Or.inl h
    · exact Or.inr (fun hjI => hj (Finset.mem_erase.2 ⟨h, hjI⟩))
  have hu' : u ∈ convexHull ℝ (a '' ↑(I.erase i)) := hαu ▸ hull_of_rep a _ α hα0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hαi) (hαI j)) hα1
  have hv' : v ∈ convexHull ℝ (a '' ↑(I.erase i)) := hβv ▸ hull_of_rep a _ β hβ0
    (fun j hj => (hsub j hj).elim (fun h => h ▸ hβi) (hβI j)) hβ1
  have hc : (I.erase i).card + 1 ≤ d := by
    rw [Finset.card_erase_of_mem hi]; have := Finset.card_pos.2 ⟨i, hi⟩; omega
  exact hne (hG2 _ hc u v huW hvW hu' hv')

theorem face_unique {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) (I J : Finset (Fin n)) (hI : I.card = d) (hJ : J.card = d)
    {u v : EuclideanSpace ℝ (Fin d)} (huv : Hirsch.Adj (polygon W a) u v)
    (hIe : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v)
    (hJe : convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = segment ℝ u v) :
    I = J := by
  classical
  have huI : u ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ left_mem_segment ℝ u v
  have hvI : v ∈ convexHull ℝ (a '' ↑I) ∩ (W : Set _) := hIe ▸ right_mem_segment ℝ u v
  have huJ : u ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ left_mem_segment ℝ u v
  have hvJ : v ∈ convexHull ℝ (a '' ↑J) ∩ (W : Set _) := hJe ▸ right_mem_segment ℝ u v
  obtain ⟨α, hα0, hαI, hα1, hαu⟩ := hull_rep a I u huI.1
  obtain ⟨β, hβ0, hβI, hβ1, hβv⟩ := hull_rep a I v hvI.1
  obtain ⟨α', hα0', hαJ', hα1', hαu'⟩ := hull_rep a J u huJ.1
  obtain ⟨β', hβ0', hβJ', hβ1', hβv'⟩ := hull_rep a J v hvJ.1
  have hcI := supp_cover W a hG2 I hI huv.1 huI.2 hvI.2 α β hα0 hαI hα1 hαu hβ0 hβI hβ1 hβv
  have hcJ := supp_cover W a hG2 J hJ huv.1 huI.2 hvI.2 α' β' hα0' hαJ' hα1' hαu' hβ0' hβJ'
    hβ1' hβv'
  set wt : Fin n → ℝ := fun i => ((α i + α' i) / 2 + (β i + β' i) / 2) / 2 with hwt
  have h0 : ∀ i, 0 ≤ wt i := fun i => by
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i; positivity
  have hu2 : ∑ i, ((α i + α' i) / 2) • a i = u := by
    rw [mid_rep a u u α α' hαu hαu', midpoint_self]
  have hv2 : ∑ i, ((β i + β' i) / 2) • a i = v := by
    rw [mid_rep a v v β β' hβv hβv', midpoint_self]
  have hm : ∑ i, wt i • a i = midpoint ℝ u v := mid_rep a u v _ _ hu2 hv2
  have h1 : ∑ i, wt i = 1 := by
    simp only [hwt, ← Finset.sum_div, Finset.sum_add_distrib, hα1, hβ1, hα1', hβ1']; norm_num
  have hcard := key_card W hW a hG1 huv wt h0 h1 hm
  have hsub : I ∪ J ⊆ Finset.univ.filter (fun i => 0 < wt i) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := hα0 i; have := hβ0 i; have := hα0' i; have := hβ0' i
    rcases Finset.mem_union.1 hi with h | h
    · have := hcI i h; simp only [hwt]; linarith
    · have := hcJ i h; simp only [hwt]; linarith
  have hU : (I ∪ J).card ≤ d := (Finset.card_le_card hsub).trans hcard
  have h1' : I = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by omega)
  have h2' : J = I ∪ J := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  exact h1'.trans h2'.symm

theorem hA_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    (edgeCount (polygon W a) : ℝ≥0∞) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
        {a' | edgeEvent W a' I}.indicator 1 a := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator 1 a =
      ((T.filter (fun I => edgeEvent W a I)).card : ℝ≥0∞) := by
    simp [Set.indicator_apply, Finset.sum_boole]
  rw [hsum]
  have hle : edgeCount (polygon W a) ≤ (T.filter (fun I => edgeEvent W a I)).card := by
    unfold edgeCount
    let f : Set (EuclideanSpace ℝ (Fin d)) → Finset (Fin n) := fun e =>
      if h : ∃ I : Finset (Fin n), I.card = d ∧
          convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e
      then h.choose else ∅
    have hf : ∀ e ∈ edges (polygon W a), (f e).card = d ∧
        convexHull ℝ (a '' ↑(f e)) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) = e := by
      rintro e ⟨u, v, huv, rfl⟩
      have h := face_exists W hW a hG1 hG2 huv
      simp only [f, dif_pos h]
      exact h.choose_spec
    rw [← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn f ?_ ?_ (Finset.finite_toSet _)
    · intro e he
      obtain ⟨hc, heq⟩ := hf e he
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, hc⟩, ?_⟩
      obtain ⟨u, v, huv, rfl⟩ := he
      exact ⟨u, v, huv, heq⟩
    · intro e₁ he₁ e₂ he₂ h
      rw [← (hf e₁ he₁).2, ← (hf e₂ he₂).2, h]
  exact_mod_cast hle

theorem hB_det {d n : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d)) (hG1 : G1det a)
    (hG2 : G2det W a) :
    ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a ≤
        perimeter (polygon W a) := by
  classical
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hsum : ∑ I ∈ T, {a' | edgeEvent W a' I}.indicator (fun a' => edgeLen W a' I) a =
      ∑ I ∈ T.filter (fun I => edgeEvent W a I), edgeLen W a I := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun I _ => ?_)
    simp [Set.indicator_apply]
  rw [hsum, ← Finset.tsum_subtype]
  have hmem : ∀ I : (T.filter (fun I => edgeEvent W a I)),
      convexHull ℝ (a '' ↑(I : Finset (Fin n))) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) ∈
        edges (polygon W a) := by
    rintro ⟨I, hI⟩
    obtain ⟨u, v, huv, heq⟩ := (Finset.mem_filter.1 hI).2
    exact ⟨u, v, huv, heq⟩
  let φ : (T.filter (fun I => edgeEvent W a I)) → edges (polygon W a) := fun I => ⟨_, hmem I⟩
  have hφ : Function.Injective φ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
    have h' : convexHull ℝ (a '' ↑I) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) =
        convexHull ℝ (a '' ↑J) ∩ (W : Set (EuclideanSpace ℝ (Fin d))) := congrArg Subtype.val h
    obtain ⟨hIT, u, v, huv, heq⟩ := Finset.mem_filter.1 hI
    have hIc := (Finset.mem_powersetCard.1 hIT).2
    have hJc := (Finset.mem_powersetCard.1 (Finset.mem_filter.1 hJ).1).2
    exact Subtype.ext (face_unique W hW a hG1 hG2 I J hIc hJc huv heq (h' ▸ heq))
  unfold perimeter
  exact ENNReal.tsum_comp_le_tsum_of_injective hφ
    (fun e : edges (polygon W a) => Metric.ediam (e : Set (EuclideanSpace ℝ (Fin d))))

theorem bridge1 {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hLI : ∀ t : Fin (d + 1) → Fin n, Function.Injective t →
      LinearIndependent ℝ (fun k : Fin d => a (t k.succ) - a (t 0))) : G1det a := by
  classical
  intro S hS z
  obtain ⟨S', hS'S, hS'c⟩ := Finset.exists_subset_card_eq hS
  set t : Fin (d + 1) → Fin n := fun k => S'.orderEmbOfFin hS'c k with htdef
  have ht : Function.Injective t := (S'.orderEmbOfFin hS'c).injective
  have hmemt : ∀ k, t k ∈ S := fun k => hS'S (Finset.orderEmbOfFin_mem S' hS'c k)
  have hli := hLI t ht
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hz : z ∈ Submodule.span ℝ (Set.range (fun k : Fin d => a (t k.succ) - a (t 0))) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hz
  refine ⟨fun i => (∑ k : Fin d, if t k.succ = i then β k else 0) -
      (if t 0 = i then ∑ k : Fin d, β k else 0),
    ?_, ?_, ?_⟩
  · intro i hi
    have h1 : ∀ k : Fin d, t k.succ ≠ i := fun k h => hi (h ▸ hmemt _)
    have h2 : t 0 ≠ i := fun h => hi (h ▸ hmemt _)
    simp [h1, h2]
  · rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  · rw [← hβ]
    simp only [sub_smul, Finset.sum_sub_distrib, Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]

theorem bridge2 {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hW : Module.finrank ℝ W = 2) (a : Fin n → EuclideanSpace ℝ (Fin d))
    (w : Fin 2 → EuclideanSpace ℝ (Fin d)) (hwW : ∀ i, w i ∈ W)
    (hLI : ∀ t : Fin (d - 2) → Fin n, Function.Injective t →
      LinearIndependent ℝ (Fin.append w (fun k => a (t k)))) : G2det W a := by
  classical
  intro J hJ x y hxW hyW hx hy
  by_contra hxy
  obtain ⟨Jp, hJJ, -, hJc⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ J)
    (show J.card ≤ d - 1 by omega) (show d - 1 ≤ (Finset.univ : Finset (Fin n)).card by simp; omega)
  obtain ⟨j0, hj0⟩ : Jp.Nonempty := Finset.card_pos.1 (by omega)
  set J' := Jp.erase j0 with hJ'
  have hJ'c : J'.card = d - 2 := by rw [Finset.card_erase_of_mem hj0, hJc]; omega
  set t : Fin (d - 2) → Fin n := fun k => J'.orderEmbOfFin hJ'c k with htdef
  have ht : Function.Injective t := (J'.orderEmbOfFin hJ'c).injective
  have hspan := (hLI t ht).span_eq_top_of_card_eq_finrank' (by simp; omega)
  have hsubJ : convexHull ℝ (a '' ↑J) ⊆ convexHull ℝ (a '' ↑Jp) :=
    convexHull_mono (Set.image_mono (Finset.coe_subset.2 hJJ))
  obtain ⟨α, hα0, hαJ, hα1, hαx⟩ := hull_rep a Jp x (hsubJ hx)
  obtain ⟨β, hβ0, hβJ, hβ1, hβy⟩ := hull_rep a Jp y (hsubJ hy)
  set D := Submodule.span ℝ (↑(J'.image (fun i => a i - a j0)) : Set (EuclideanSpace ℝ (Fin d)))
    with hD
  have hDfin : Module.finrank ℝ D ≤ d - 2 := by
    have h := finrank_span_finset_le_card (R := ℝ) (J'.image (fun i => a i - a j0))
    unfold Set.finrank at h
    exact h.trans (Finset.card_image_le.trans hJ'c.le)
  have hdec : ∀ γ : Fin n → ℝ, (∀ i, i ∉ Jp → γ i = 0) →
      ∑ i, γ i • (a i - a j0) ∈ D := by
    intro γ hγ
    refine Submodule.sum_mem _ (fun i _ => ?_)
    by_cases hi : i ∈ J'
    · exact Submodule.smul_mem _ _ (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)))
    · by_cases hi0 : i = j0
      · rw [hi0, sub_self, smul_zero]; exact Submodule.zero_mem _
      · have : i ∉ Jp := fun h => hi (Finset.mem_erase.2 ⟨hi0, h⟩)
        rw [hγ i this, zero_smul]; exact Submodule.zero_mem _
  have hsplit : ∀ γ : Fin n → ℝ,
      ∑ i, γ i • a i = ∑ i, γ i • (a i - a j0) + (∑ i, γ i) • a j0 := by
    intro γ
    simp [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul]
  have hj0D : a j0 ∈ D ⊔ W := by
    have h := hsplit α
    rw [hαx, hα1, one_smul] at h
    have : a j0 = -(∑ i, α i • (a i - a j0)) + x := by rw [h]; abel
    rw [this]
    exact Submodule.add_mem_sup (D.neg_mem (hdec α hαJ)) hxW
  have htop : D ⊔ W = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    induction j using Fin.addCases with
    | left l =>
      rw [Fin.append_left]; exact Submodule.mem_sup_right (hwW l)
    | right k =>
      rw [Fin.append_right]
      have hk : t k ∈ J' := Finset.orderEmbOfFin_mem J' hJ'c k
      have : a (t k) = (a (t k) - a j0) + a j0 := by abel
      rw [SetLike.mem_coe, this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span
        (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)))) hj0D
  have hgr := Submodule.finrank_sup_add_finrank_inf_eq D W
  rw [htop, finrank_top, finrank_euclideanSpace_fin, hW] at hgr
  have h0 : Module.finrank ℝ ↥(D ⊓ W) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at h0
  have hyx : y - x ∈ D ⊓ W := by
    refine ⟨?_, W.sub_mem hyW hxW⟩
    have h := hsplit (fun i => β i - α i)
    have hs0 : ∑ i, (β i - α i) = 0 := by rw [Finset.sum_sub_distrib, hβ1, hα1, sub_self]
    rw [hs0, zero_smul, add_zero] at h
    have hyx' : ∑ i, (β i - α i) • a i = y - x := by
      simp [sub_smul, Finset.sum_sub_distrib, hβy, hαx]
    rw [← hyx', h]
    exact hdec _ (fun i hi => by rw [hβJ i hi, hαJ i hi, sub_self])
  rw [h0] at hyx
  exact hxy (sub_eq_zero.1 ((Submodule.mem_bot ℝ).1 hyx)).symm

end FSFace


/-! O1 reduction: lemma_25's inequality from two almost-sure statements
(A) edgeCount ≤ Σ_{|I|=d} 1[E_I] and (B) Σ_{|I|=d} 1[E_I]·edgeLen_I ≤ perimeter,
plus measurability of the events `E_I`. -/

namespace FSL25

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem sum_le_lintegral_sum {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    calc ∫⁻ a, f j a ∂μ + ∑ i ∈ s, ∫⁻ a, f i a ∂μ
        ≤ ∫⁻ a, f j a ∂μ + ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by gcongr
      _ ≤ ∫⁻ a, (f j a + ∑ i ∈ s, f i a) ∂μ := le_lintegral_add _ _
      _ = ∫⁻ a, ∑ i ∈ insert j s, f i a ∂μ := by simp_rw [Finset.sum_insert hj]

theorem lemma25_of_ae {d n : ℕ} (hdn : d ≤ n) (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (P : Measure (Fin n → EuclideanSpace ℝ (Fin d))) (m : ℝ≥0∞)
    (hmeas : ∀ I : Finset (Fin n), MeasurableSet {a | edgeEvent W a I})
    (hA : ∀ᵐ a ∂P, (edgeCount (polygon W a) : ℝ≥0∞) ≤
      ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d, {a | edgeEvent W a I}.indicator 1 a)
    (hB : ∀ᵐ a ∂P, ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard d,
      {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ≤ perimeter (polygon W a))
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ P {a | edgeEvent W a I} →
      m * P {a | edgeEvent W a I} ≤ ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P) :
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂P ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂P := by
  set T := (Finset.univ : Finset (Fin n)).powersetCard d with hT
  have hC : (0 : ℝ) < (n.choose d : ℝ) := by exact_mod_cast Nat.choose_pos hdn
  calc m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂P
      ≤ m * ∫⁻ a, ∑ I ∈ T, {a | edgeEvent W a I}.indicator 1 a ∂P :=
        mul_le_mul' le_rfl (lintegral_mono_ae hA)
    _ = ∑ I ∈ T, m * P {a | edgeEvent W a I} := by
        rw [lintegral_finsetSum _ (fun I _ => measurable_one.indicator (hmeas I)), Finset.mul_sum]
        refine Finset.sum_congr rfl (fun I _ => ?_)
        rw [lintegral_indicator_one (hmeas I)]
    _ ≤ ∑ I ∈ T, (m * ENNReal.ofReal (2 / (n.choose d : ℝ)) +
          ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P) := by
        refine Finset.sum_le_sum (fun I hI => ?_)
        by_cases h : ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ P {a | edgeEvent W a I}
        · exact le_add_left (hm I (Finset.mem_powersetCard.1 hI).2 h)
        · rw [not_le] at h
          exact le_add_right (mul_le_mul' le_rfl h.le)
    _ = (n.choose d : ℝ≥0∞) * (m * ENNReal.ofReal (2 / (n.choose d : ℝ))) +
          ∑ I ∈ T, ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P := by
        rw [Finset.sum_add_distrib, Finset.sum_const, hT, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 * m + ∫⁻ a, perimeter (polygon W a) ∂P := by
        refine add_le_add (le_of_eq ?_) ?_
        · rw [mul_comm m, ← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hC.le,
            mul_div_cancel₀ _ hC.ne', ENNReal.ofReal_ofNat]
        · calc ∑ I ∈ T, ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂P
              = ∑ I ∈ T, ∫⁻ a, {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ∂P := by
                refine Finset.sum_congr rfl (fun I _ => ?_)
                rw [lintegral_indicator (hmeas I)]
            _ ≤ ∫⁻ a, ∑ I ∈ T, {a | edgeEvent W a I}.indicator (fun a => edgeLen W a I) a ∂P :=
                sum_le_lintegral_sum P T _
            _ ≤ ∫⁻ a, perimeter (polygon W a) ∂P := lintegral_mono_ae hB

end FSL25


/-! O1 CLOSED: lemma_25's inequality (after GP, Face, Meas, L25). -/

namespace FSO1

open MeasureTheory FriendlyShadow.Gaussian
open scoped ENNReal

theorem gp_ae {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n + 1)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin (n + 1) → EuclideanSpace ℝ (Fin d) → ℝ) :
    ∀ᵐ a ∂rowLaw μ, FSFace.G1det a ∧ FSFace.G2det W a := by
  let b := Module.finBasisOfFinrankEq ℝ W hW
  have hwLI : LinearIndependent ℝ (fun i : Fin 2 => (b i : EuclideanSpace ℝ (Fin d))) :=
    b.linearIndependent.map' W.subtype W.ker_subtype
  filter_upwards [FSGP.g1_ae μ, FSGP.g2_ae (by omega) μ _ hwLI] with a h1 h2
  exact ⟨FSFace.bridge1 a h1, FSFace.bridge2 hd hdn W hW a _ (fun i => (b i).2) h2⟩

theorem lemma25_full {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (m : ℝ≥0∞)
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I} →
      m * rowLaw μ {a | edgeEvent W a I} ≤
        ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) :
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hgp := gp_ae hd hdn W hW μ
  exact FSL25.lemma25_of_ae hdn W (rowLaw μ) m (fun I => FSMeasE.meas_edgeEvent W I)
    (hgp.mono fun a ha => FSFace.hA_det W hW a ha.1 ha.2)
    (hgp.mono fun a ha => FSFace.hB_det W hW a ha.1 ha.2) hm

end FSO1

open MeasureTheory FriendlyShadow.Gaussian RealInnerProductSpace ENNReal in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (μ : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hμ : ∀ i, IsDensity (μ i)) (m : ℝ≥0∞)
    (hm : ∀ I : Finset (Fin n), I.card = d →
      ENNReal.ofReal (2 / (n.choose d : ℝ)) ≤ rowLaw μ {a | edgeEvent W a I} →
      m * rowLaw μ {a | edgeEvent W a I} ≤
        ∫⁻ a in {a | edgeEvent W a I}, edgeLen W a I ∂(rowLaw μ)) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞)) (rowLaw μ) ∧
    m * ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞) ∂(rowLaw μ) ≤
      2 * m + ∫⁻ a, perimeter (polygon W a) ∂(rowLaw μ) := by
  exact ⟨(C5747Cnt.measurable_edgeCount (n := n) W).aemeasurable,
    FSO1.lemma25_full hd hdn W hW μ m hm⟩
