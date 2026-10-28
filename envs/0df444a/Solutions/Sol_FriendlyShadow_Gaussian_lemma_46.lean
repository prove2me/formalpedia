-- Prove2me | solution 1 for FriendlyShadow.Gaussian.lemma_46
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T08:04:21.424011+00:00
-- url     : https://prove2.me/submissions/7081a239-bd11-4100-a1c6-20c5b862ed43

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

namespace C5747Anal

lemma gauss_integral (d : ℕ) {b : ℝ} (hb : 0 < b) :
    ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (-b * ‖v‖ ^ 2) = (Real.pi / b) ^ ((d : ℝ) / 2) := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]; simp

lemma gauss_integrable (d : ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun v : EuclideanSpace ℝ (Fin d) => Real.exp (-b * ‖v‖ ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [gauss_integral d hb]
  exact (Real.rpow_pos_of_pos (div_pos Real.pi_pos hb) _).ne'

lemma vol_ball_le (d : ℕ) :
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤
      Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
  have hint := (gauss_integrable d (b := 1 / 2) (by norm_num)).const_mul (Real.exp (1 / 2))
  have h1 : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
      ∫ v : EuclideanSpace ℝ (Fin d), (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator 1 v := by
    rw [integral_indicator_one measurableSet_ball]
  rw [h1]
  calc _ ≤ ∫ v : EuclideanSpace ℝ (Fin d), Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖v‖ ^ 2) := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun v => Set.indicator_nonneg (fun _ _ => zero_le_one) v)
        · exact hint
        · refine Filter.Eventually.of_forall (fun v => ?_)
          by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1
          · show (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator 1 v ≤
              Real.exp (1 / 2) * Real.exp (-(1 / 2) * ‖v‖ ^ 2)
            rw [Set.indicator_of_mem hv, Pi.one_apply, ← Real.exp_add]
            rw [Metric.mem_ball, dist_zero_right] at hv
            have : ‖v‖ ^ 2 < 1 := by nlinarith [norm_nonneg v]
            exact Real.one_le_exp (by nlinarith)
          · rw [Set.indicator_of_notMem hv]; positivity
    _ = Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) := by
        rw [integral_const_mul, gauss_integral d (by norm_num)]
        congr 2; ring

lemma integral_exp_neg_norm (d : ℕ) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-‖y‖) =
      volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (d.factorial : ℝ) := by
  have h := MeasureTheory.measure_unitBall_eq_integral_div_gamma
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (p := 1) one_pos
  simp only [Real.rpow_one, finrank_euclideanSpace, Fintype.card_fin, div_one] at h
  rw [Real.Gamma_nat_eq_factorial] at h
  have hpos : 0 ≤ (∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-‖y‖)) / (d.factorial : ℝ) :=
    div_nonneg (integral_nonneg (fun _ => (Real.exp_pos _).le)) (by positivity)
  rw [measureReal_def, h, ENNReal.toReal_ofReal hpos]
  have : (d.factorial : ℝ) ≠ 0 := by positivity
  field_simp

lemma integral_exp_neg_mul_norm_le (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(c * ‖y‖)) ≤
      Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / c ^ d := by
  have hs := MeasureTheory.Measure.integral_comp_smul
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun y => Real.exp (-‖y‖)) c
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul] at hs
  rw [hs, integral_exp_neg_norm, abs_of_pos (by positivity)]
  have hv := vol_ball_le d
  have hci : 0 < (c ^ d)⁻¹ := by positivity
  calc (c ^ d)⁻¹ * (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * d.factorial)
      ≤ (c ^ d)⁻¹ * (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * d.factorial) := by
        gcongr
    _ = _ := by rw [div_eq_mul_inv]; ring

lemma integral_exp_neg_mul_norm_eq (d : ℕ) {c : ℝ} (hc : 0 < c) :
    ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(c * ‖y‖)) =
      (c ^ d)⁻¹ * (volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * (d.factorial : ℝ)) := by
  have hs := MeasureTheory.Measure.integral_comp_smul
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (fun y => Real.exp (-‖y‖)) c
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hc, finrank_euclideanSpace,
    Fintype.card_fin, smul_eq_mul] at hs
  rw [hs, integral_exp_neg_norm, abs_of_pos (by positivity)]

lemma integrable_exp_neg_mul_norm (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : EuclideanSpace ℝ (Fin d) => Real.exp (-(c * ‖y‖))) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_exp_neg_mul_norm_eq d hc]
  have hb : 0 < volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume _ one_pos).ne' measure_ball_lt_top.ne
  have : (0:ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  positivity

end C5747Anal

namespace C5747Dens

open FriendlyShadow.Gaussian SmoothedSimplex.Shadow C5747Anal

variable {d : ℕ}

lemma lgD_meas (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ) : Measurable (lgDensity abar σ r) := by
  unfold lgDensity
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact measurableSet_le (by fun_prop) measurable_const

lemma lgD_ge (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) (r : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) ≤ lgDensity abar σ r x := by
  unfold lgDensity
  split_ifs with h
  · exact le_rfl
  · apply Real.exp_le_exp.mpr
    have key : -(‖x - abar‖ ^ 2) / (2 * σ ^ 2) - (-(‖x - abar‖ * r / σ) + r ^ 2 / 2) =
        -((‖x - abar‖ - r * σ) ^ 2) / (2 * σ ^ 2) := by
      field_simp; ring
    have : -((‖x - abar‖ - r * σ) ^ 2) / (2 * σ ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (‖x - abar‖ - r * σ)]) (by positivity)
    linarith

lemma lgD_nonneg (abar : EuclideanSpace ℝ (Fin d)) (σ r : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    0 ≤ lgDensity abar σ r x := by
  unfold lgDensity; split_ifs <;> exact (Real.exp_pos _).le

lemma lgD_le (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin d)) :
    lgDensity abar σ r x ≤ Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) +
      Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by
  unfold lgDensity
  have hp : 0 < Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by positivity
  split_ifs with h
  · linarith
  · have hgt : r * σ < ‖x - abar‖ := lt_of_not_ge h
    have h1 : Real.exp (-(‖x - abar‖ * r / σ) + r ^ 2 / 2) ≤
        Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have : r ≤ ‖x - abar‖ / σ := by rw [le_div_iff₀ hσ]; linarith
      have e1 : ‖x - abar‖ * r / σ = r * (‖x - abar‖ / σ) := by ring
      have e2 : r / (8 * σ) * ‖x - abar‖ = r * (‖x - abar‖ / σ) / 8 := by field_simp
      rw [e1, e2]; nlinarith
    linarith [Real.exp_pos (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2))]

lemma gU_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2))) := by
  have h := (gauss_integrable d (b := 1 / (2 * σ ^ 2)) (by positivity)).comp_sub_right abar
  refine h.congr (Filter.Eventually.of_forall (fun x => ?_))
  simp only; congr 1; field_simp

lemma sqrt_pow_eq (d : ℕ) {σ : ℝ} (hσ : 0 < σ) :
    (Real.pi / (1 / (2 * σ ^ 2))) ^ ((d : ℝ) / 2) = (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have ht : 0 ≤ Real.sqrt (2 * Real.pi) * σ := by positivity
  have : Real.pi / (1 / (2 * σ ^ 2)) = (Real.sqrt (2 * Real.pi) * σ) ^ (2:ℝ) := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]; field_simp
  rw [this, ← Real.rpow_mul ht, ← Real.rpow_natCast]; congr 1; ring

lemma gU_integral (abar : EuclideanSpace ℝ (Fin d)) {σ : ℝ} (hσ : 0 < σ) :
    ∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-(‖x - abar‖ ^ 2) / (2 * σ ^ 2)) =
      (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  have h := integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (fun x => Real.exp (-(1 / (2 * σ ^ 2)) * ‖x‖ ^ 2)) abar
  rw [gauss_integral d (by positivity), sqrt_pow_eq d hσ] at h
  rw [← h]; congr 1; ext x; congr 1; field_simp

lemma tail_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
      Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖x - abar‖))) :=
  ((integrable_exp_neg_mul_norm d (c := r / (8 * σ)) (by positivity)).comp_sub_right abar).const_mul _

lemma lgD_integrable (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    Integrable (lgDensity abar σ r) := by
  refine Integrable.mono' ((gU_integrable abar hσ).add (tail_integrable abar hσ hr))
    (lgD_meas abar σ r).aestronglyMeasurable (Filter.Eventually.of_forall (fun x => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (lgD_nonneg abar σ r x)]
  exact lgD_le abar hσ hr x

lemma Z_ge (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    (Real.sqrt (2 * Real.pi) * σ) ^ d ≤ ∫ y, lgDensity abar σ r y := by
  rw [← gU_integral abar hσ]
  exact integral_mono (gU_integrable abar hσ) (lgD_integrable abar hσ hr) (fun x => lgD_ge abar hσ r x)

lemma Z_le (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    ∫ y, lgDensity abar σ r y ≤ (Real.sqrt (2 * Real.pi) * σ) ^ d +
      Real.exp (-(3 * r ^ 2 / 8)) *
        (Real.exp (1 / 2) * (2 * Real.pi) ^ ((d : ℝ) / 2) * (d.factorial : ℝ) / (r / (8 * σ)) ^ d) := by
  calc ∫ y, lgDensity abar σ r y
      ≤ ∫ y, (Real.exp (-(‖y - abar‖ ^ 2) / (2 * σ ^ 2)) +
          Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (-(r / (8 * σ) * ‖y - abar‖))) :=
        integral_mono (lgD_integrable abar hσ hr)
          ((gU_integrable abar hσ).add (tail_integrable abar hσ hr)) (fun x => lgD_le abar hσ hr x)
    _ = (Real.sqrt (2 * Real.pi) * σ) ^ d + Real.exp (-(3 * r ^ 2 / 8)) *
          ∫ y : EuclideanSpace ℝ (Fin d), Real.exp (-(r / (8 * σ) * ‖y‖)) := by
        rw [integral_add (gU_integrable abar hσ) (tail_integrable abar hσ hr), gU_integral abar hσ,
          integral_const_mul]
        congr 2
        exact integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
          (fun y => Real.exp (-(r / (8 * σ) * ‖y‖))) abar
    _ ≤ _ := by
        gcongr
        exact integral_exp_neg_mul_norm_le d (by positivity)

/-- The excess factor `T = e^{-3r²/8} e^{1/2} d! (8/r)^d`. -/
noncomputable def T (d : ℕ) (r : ℝ) : ℝ :=
  Real.exp (-(3 * r ^ 2 / 8)) * Real.exp (1 / 2) * (d.factorial : ℝ) * (8 / r) ^ d

set_option maxHeartbeats 1000000 in
lemma Z_le_T (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    ∫ y, lgDensity abar σ r y ≤ (1 + T d r) * (Real.sqrt (2 * Real.pi) * σ) ^ d := by
  refine (Z_le abar hσ hr).trans (le_of_eq ?_)
  have h2 : (2 * Real.pi) ^ ((d : ℝ) / 2) = Real.sqrt (2 * Real.pi) ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; congr 1; ring
  rw [h2]; unfold T
  rw [div_pow, div_pow, mul_pow]
  field_simp
  ring

set_option maxHeartbeats 1000000 in
lemma pdf_cmp (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin d)) :
    gaussianPdf abar σ x ≤ (1 + T d r) * lgPdf abar σ r x := by
  have hZg : 0 < (Real.sqrt (2 * Real.pi) * σ) ^ d := by positivity
  have hZ : 0 < ∫ y, lgDensity abar σ r y := lt_of_lt_of_le hZg (Z_ge abar hσ hr)
  have hZT := Z_le_T abar hσ hr
  have hg := lgD_ge abar hσ r x
  have hl := lgD_nonneg abar σ r x
  have key : ∀ (Zg Z gU L t : ℝ), 0 < Zg → 0 < Z → Z ≤ t * Zg → gU ≤ L → 0 ≤ L →
      gU / Zg ≤ t * (L / Z) := by
    intro Zg Z gU L t h1 h2 h3 h4 h5
    rw [div_le_iff₀ h1]
    calc gU ≤ L := h4
      _ = L / Z * Z := by field_simp
      _ ≤ L / Z * (t * Zg) := mul_le_mul_of_nonneg_left h3 (div_nonneg h5 h2.le)
      _ = t * (L / Z) * Zg := by ring
  unfold gaussianPdf lgPdf
  rw [one_div_pow, one_div_mul_eq_div]
  exact key _ _ _ _ _ hZg hZ hZT hg hl

lemma lg_prob (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    IsProbabilityMeasure (lg abar σ r) := by
  constructor
  have hZ : 0 < ∫ y, lgDensity abar σ r y :=
    lt_of_lt_of_le (by positivity) (Z_ge abar hσ hr)
  have hint : Integrable (lgPdf abar σ r) := by
    unfold lgPdf; exact (lgD_integrable abar hσ hr).div_const _
  have hnn : 0 ≤ᵐ[volume] lgPdf abar σ r :=
    Filter.Eventually.of_forall (fun x => div_nonneg (lgD_nonneg abar σ r x) hZ.le)
  unfold lg densityMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint hnn]
  unfold lgPdf
  rw [integral_div, div_self hZ.ne', ENNReal.ofReal_one]

end C5747Dens

namespace C5747D

open FriendlyShadow.Gaussian SmoothedSimplex.Shadow C5747Dens
open scoped NNReal

lemma pi_le_of_le {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i)) (h : ∀ i, μ i ≤ ν i) : Measure.pi μ ≤ Measure.pi ν := by
  rw [Measure.le_iff]; intro s hs
  rw [Measure.pi_def, Measure.pi_def, toMeasure_apply _ _ hs, toMeasure_apply _ _ hs]
  have key : OuterMeasure.pi (fun i => (μ i).toOuterMeasure) ≤
      OuterMeasure.pi (fun i => (ν i).toOuterMeasure) := by
    rw [OuterMeasure.le_pi]
    intro t _
    refine (OuterMeasure.pi_pi_le _ t).trans (Finset.prod_le_prod' fun i _ => ?_)
    exact Measure.le_iff'.mp (h i) (t i)
  exact key s

lemma pi_smul {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
    (ν : ∀ i, Measure (α i)) [∀ i, IsFiniteMeasure (ν i)] (c : ℝ≥0) :
    Measure.pi (fun i => c • ν i) = (c ^ Fintype.card ι) • Measure.pi ν := by
  apply Measure.pi_eq; intro s hs
  simp only [Measure.smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

variable {d : ℕ}

lemma gauss_le (abar : EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    gaussian abar σ ≤ (1 + T d r).toNNReal • lg abar σ r := by
  have hT : 0 ≤ 1 + T d r := by unfold T; positivity
  rw [Measure.le_iff]; intro s hs
  rw [Measure.smul_apply, gaussian, lg, densityMeasure, withDensity_apply _ hs, withDensity_apply _ hs,
    ENNReal.smul_def, smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono; intro x
  dsimp only
  rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hT, ← ENNReal.ofReal_mul hT]
  exact ENNReal.ofReal_le_ofReal (pdf_cmp abar hσ hr x)

lemma main_ineq {n : ℕ} (abar : Fin n → EuclideanSpace ℝ (Fin d)) {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r)
    (f : (Fin n → EuclideanSpace ℝ (Fin d)) → ℝ≥0∞) (M : ℕ) (hM : ∀ a, f a ≤ M)
    (hnum : ((1 + T d r) ^ n - 1) * (M : ℝ) ≤ 1) :
    ∫⁻ a, f a ∂(Measure.pi (fun i => gaussian (abar i) σ)) ≤
      1 + ∫⁻ a, f a ∂(Measure.pi (fun i => lg (abar i) σ r)) := by
  have hT : 0 ≤ T d r := by unfold T; positivity
  have : ∀ i, IsProbabilityMeasure (lg (abar i) σ r) := fun i => lg_prob (abar i) hσ hr
  have h1 := pi_le_of_le _ _ (fun i => gauss_le (abar i) hσ hr)
  rw [pi_smul, Fintype.card_fin] at h1
  set L := ∫⁻ a, f a ∂(Measure.pi (fun i => lg (abar i) σ r))
  have hL : L ≤ M := by
    calc L ≤ ∫⁻ _a, (M : ℝ≥0∞) ∂(Measure.pi (fun i => lg (abar i) σ r)) := lintegral_mono hM
      _ = M := by rw [lintegral_const, measure_univ, mul_one]
  have hq : 1 ≤ (1 + T d r) ^ n := one_le_pow₀ (by linarith)
  have hc : ((((1 + T d r).toNNReal) ^ n : ℝ≥0) : ℝ≥0∞) =
      1 + ENNReal.ofReal ((1 + T d r) ^ n - 1) := by
    rw [ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ (by linarith),
      ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one
      (by linarith)]
    congr 1; ring
  calc ∫⁻ a, f a ∂(Measure.pi (fun i => gaussian (abar i) σ))
      ≤ ∫⁻ a, f a ∂(((1 + T d r).toNNReal ^ n) • Measure.pi (fun i => lg (abar i) σ r)) :=
        lintegral_mono' h1 le_rfl
    _ = (1 + ENNReal.ofReal ((1 + T d r) ^ n - 1)) * L := by
        rw [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul, hc]
    _ = L + ENNReal.ofReal ((1 + T d r) ^ n - 1) * L := by ring
    _ ≤ L + ENNReal.ofReal ((1 + T d r) ^ n - 1) * M := by gcongr
    _ ≤ L + 1 := by
        gcongr
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hnum
    _ = 1 + L := add_comm _ _

end C5747D

namespace C5747Num

open C5747Dens

lemma nat_bound {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) :
    4 * n * ((d + 2) * (n + 1) ^ (d + 1)) ≤ n ^ (4 * d) := by
  have hn : 3 ≤ n := le_trans hd hdn
  have h1 : 2 * (n + 1) ≤ n ^ 2 := by nlinarith
  have h2 : 2 ^ (d + 1) * (n + 1) ^ (d + 1) ≤ n ^ (2 * d + 2) := by
    rw [← mul_pow, show 2 * d + 2 = 2 * (d + 1) by ring, pow_mul]
    exact Nat.pow_le_pow_left h1 _
  have h3 : d + 2 ≤ 2 ^ d := by
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
    have := Nat.lt_two_pow_self (n := k)
    have h4 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
    omega
  have h5 : 2 ≤ n ^ (2 * d - 3) := le_trans (by omega) (Nat.le_self_pow (by omega) n)
  have h6 : n ^ (4 * d) = n ^ (2 * d + 3) * n ^ (2 * d - 3) := by
    rw [← pow_add]; congr 1; omega
  have key : 2 ^ (d + 1) * (4 * n * ((d + 2) * (n + 1) ^ (d + 1))) ≤ 2 ^ (d + 1) * n ^ (4 * d) := by
    calc 2 ^ (d + 1) * (4 * n * ((d + 2) * (n + 1) ^ (d + 1)))
        = 4 * n * (d + 2) * (2 ^ (d + 1) * (n + 1) ^ (d + 1)) := by ring
      _ ≤ 4 * n * 2 ^ d * n ^ (2 * d + 2) := by gcongr
      _ = 2 ^ (d + 1) * (2 * n ^ (2 * d + 3)) := by rw [pow_succ, pow_succ]; ring
      _ ≤ 2 ^ (d + 1) * (n ^ (2 * d - 3) * n ^ (2 * d + 3)) := by gcongr
      _ = 2 ^ (d + 1) * n ^ (4 * d) := by rw [h6]; ring
  exact Nat.le_of_mul_le_mul_left key (by positivity)

lemma T_le {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) :
    T d (4 * Real.sqrt (d * Real.log n)) ≤ 2 / (n : ℝ) ^ (4 * d) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans hd hdn
  have hn0 : (0 : ℝ) < n := by linarith
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hn0]
    have := Real.exp_one_lt_d9; linarith
  have hdl : 1 ≤ (d : ℝ) * Real.log n := by nlinarith
  set r := 4 * Real.sqrt (d * Real.log n) with hr
  have hsq : Real.sqrt (d * Real.log n) ^ 2 = d * Real.log n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ Real.sqrt (d * Real.log n) := Real.one_le_sqrt.mpr hdl
  have hr4 : 4 ≤ r := by rw [hr]; linarith
  have h8r : 8 / r ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hexp : Real.exp (-(3 * r ^ 2 / 8)) = 1 / (n : ℝ) ^ (6 * d) := by
    have : 3 * r ^ 2 / 8 = ((6 * d : ℕ) : ℝ) * Real.log n := by
      rw [hr, mul_pow, hsq]; push_cast; ring
    rw [this, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0, one_div]
  have hhalf : Real.exp (1 / 2) ≤ 2 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have hfac : (d.factorial : ℝ) ≤ (n : ℝ) ^ d := by
    have := (Nat.factorial_le_pow d).trans (Nat.pow_le_pow_left hdn d)
    exact_mod_cast this
  have hpow : (8 / r) ^ d ≤ (n : ℝ) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  have hN : (n : ℝ) ^ (6 * d) = (n : ℝ) ^ (4 * d) * (n : ℝ) ^ d * (n : ℝ) ^ d := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  unfold T
  rw [hexp]
  calc 1 / (n : ℝ) ^ (6 * d) * Real.exp (1 / 2) * (d.factorial : ℝ) * (8 / r) ^ d
      ≤ 1 / (n : ℝ) ^ (6 * d) * 2 * (n : ℝ) ^ d * (n : ℝ) ^ d := by gcongr
    _ = 2 / (n : ℝ) ^ (4 * d) := by rw [hN]; field_simp

lemma hnum {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n) :
    ((1 + T d (4 * Real.sqrt (d * Real.log n))) ^ n - 1) *
      (((d + 2) * (n + 1) ^ (d + 1) : ℕ) : ℝ) ≤ 1 := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast le_trans hd hdn
  set M : ℝ := (((d + 2) * (n + 1) ^ (d + 1) : ℕ) : ℝ) with hM
  have hM0 : 0 ≤ M := by positivity
  set ε : ℝ := 2 / (n : ℝ) ^ (4 * d) with hε
  have hnd : (0 : ℝ) < (n : ℝ) ^ (4 * d) := by positivity
  have hnat : 4 * (n : ℝ) * M ≤ (n : ℝ) ^ (4 * d) := by
    rw [hM]; exact_mod_cast nat_bound hd hdn
  have hT0 : 0 ≤ T d (4 * Real.sqrt (d * Real.log n)) := by unfold T; positivity
  have hTe := T_le hd hdn
  have hne : (n : ℝ) * ε ≤ 1 := by
    rw [hε, mul_div_assoc', div_le_one hnd]
    have : 1 ≤ M := by rw [hM]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    nlinarith
  have hq : (1 + T d (4 * Real.sqrt (d * Real.log n))) ^ n ≤ Real.exp ((n : ℝ) * ε) := by
    calc (1 + T d (4 * Real.sqrt (d * Real.log n))) ^ n ≤ (1 + ε) ^ n :=
          pow_le_pow_left₀ (by linarith) (by linarith) n
      _ ≤ Real.exp ε ^ n := pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ε]) n
      _ = Real.exp ((n : ℝ) * ε) := by rw [Real.exp_nat_mul]
  have hε0 : 0 ≤ (n : ℝ) * ε := by positivity
  have hex : Real.exp ((n : ℝ) * ε) - 1 ≤ 2 * ((n : ℝ) * ε) := by
    have := Real.abs_exp_sub_one_le (x := (n : ℝ) * ε) (by rw [abs_of_nonneg hε0]; exact hne)
    rw [abs_of_nonneg hε0] at this
    exact (le_abs_self _).trans this
  have h2 : 2 * ((n : ℝ) * ε) * M ≤ 1 := by
    rw [hε]
    have : 2 * ((n : ℝ) * (2 / (n : ℝ) ^ (4 * d))) * M = 4 * (n : ℝ) * M / (n : ℝ) ^ (4 * d) := by
      field_simp; ring
    rw [this, div_le_one hnd]; exact hnat
  calc ((1 + T d (4 * Real.sqrt (d * Real.log n))) ^ n - 1) * M
      ≤ (2 * ((n : ℝ) * ε)) * M := by gcongr; linarith
    _ ≤ 1 := h2

end C5747Num

open FriendlyShadow.Gaussian MeasureTheory ENNReal in
theorem solution {d n : ℕ} (hd : 3 ≤ d) (hdn : d ≤ n)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hW : Module.finrank ℝ W = 2)
    (abar : Fin n → EuclideanSpace ℝ (Fin d)) (σ : ℝ) (hσ : 0 < σ) :
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ∧
    AEMeasurable (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
        (Measure.pi (fun i => lg (abar i) σ (4 * Real.sqrt (d * Real.log n)))) ∧
    ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => SmoothedSimplex.Shadow.gaussian (abar i) σ)) ≤
      1 + ∫⁻ a, (edgeCount (polygon W a) : ℝ≥0∞)
        ∂(Measure.pi (fun i => lg (abar i) σ (4 * Real.sqrt (d * Real.log n)))) := by
  have hmeas := C5747Cnt.measurable_edgeCount (n := n) W
  have hn1 : (1 : ℝ) < n := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast le_trans hd hdn
    linarith
  have hd0 : (0 : ℝ) < d := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hr : 0 < 4 * Real.sqrt (d * Real.log n) := by
    have := Real.sqrt_pos.mpr (mul_pos hd0 (Real.log_pos hn1))
    linarith
  refine ⟨hmeas.aemeasurable, hmeas.aemeasurable, ?_⟩
  exact C5747D.main_ineq abar hσ hr (fun a => (edgeCount (polygon W a) : ℝ≥0∞))
    ((d + 2) * (n + 1) ^ (d + 1)) (fun a => Nat.cast_le.mpr (C5747Geom.edgeCount_le W a))
    (C5747Num.hnum hd hdn)
