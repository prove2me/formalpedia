-- Prove2me | solution 1 for DiestelGraphTheory.jordan_curve_polygon
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T15:15:35.470835+00:00
-- url     : https://prove2.me/submissions/0c11beef-9472-4e40-a6fb-74f93a4112be

import Mathlib
import Definitions.Def_DiestelGraphTheory_PolygonalArc
import Theorems.Thm_JordanCurve_jordan_curve_theorem

namespace DiestelGraphTheory
open Set

/-- A polygonal walk of `n` segments from `a` to `b` inside `U`. -/
def IsWalk (U : Set (ℝ × ℝ)) (a b : ℝ × ℝ) (n : ℕ) (x : ℕ → ℝ × ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧ ∀ i < n, segment ℝ (x i) (x (i + 1)) ⊆ U

lemma walk_trans {U : Set (ℝ × ℝ)} {a b c : ℝ × ℝ} {n m : ℕ} {x y : ℕ → ℝ × ℝ}
    (hx : IsWalk U a b n x) (hy : IsWalk U b c m y) :
    IsWalk U a c (n + m) (fun k => if k ≤ n then x k else y (k - n)) := by
  obtain ⟨hx0, hxn, hxs⟩ := hx
  obtain ⟨hy0, hym, hys⟩ := hy
  refine ⟨by simp [hx0], ?_, ?_⟩
  · by_cases hm : m = 0
    · subst hm; simp [hxn, ← hy0, hym]
    · dsimp only; rw [if_neg (by omega)]; simpa using hym
  · intro i hi; dsimp only
    by_cases h1 : i + 1 ≤ n
    · rw [if_pos (by omega), if_pos h1]; exact hxs i (by omega)
    · by_cases h2 : i = n
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega), hxn, ← hy0, show i + 1 - i = 0 + 1 by omega]
        exact hys 0 (by omega)
      · rw [if_neg (by omega), if_neg h1, show i + 1 - n = (i - n) + 1 by omega]
        exact hys _ (by omega)

lemma walk_exists {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : IsPreconnected U) {a b : ℝ × ℝ}
    (ha : a ∈ U) (hb : b ∈ U) : ∃ n x, IsWalk U a b n x := by
  refine hc.induction₂' (fun a b => ∃ n x, IsWalk U a b n x) (fun z hz => ?_)
    (fun p q r _ _ _ ⟨n, x, hx⟩ ⟨m, y, hy⟩ => ⟨_, _, walk_trans hx hy⟩) ha hb
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU z hz
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds z hr)] with w hw
  have hs1 : segment ℝ z w ⊆ U :=
    ((convex_ball z r).segment_subset (Metric.mem_ball_self hr) hw).trans hball
  have hs2 : segment ℝ w z ⊆ U := by rw [segment_symm]; exact hs1
  refine ⟨⟨1, fun k => if k = 0 then z else w, by simp, by simp, ?_⟩,
    ⟨1, fun k => if k = 0 then w else z, by simp, by simp, ?_⟩⟩
  · intro i hi; obtain rfl : i = 0 := by omega
    simpa using hs1
  · intro i hi; obtain rfl : i = 0 := by omega
    simpa using hs2

/-- Shortcut at an intersection point of segments `i < j`. -/
lemma walk_shortcut {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ} {n : ℕ} {x : ℕ → ℝ × ℝ}
    (hx : IsWalk U a b n x) {i j : ℕ} (hij : i < j) (hj : j < n) {z : ℝ × ℝ}
    (hzi : z ∈ segment ℝ (x i) (x (i + 1))) (hzj : z ∈ segment ℝ (x j) (x (j + 1))) :
    IsWalk U a b (i + 1 + (n - j))
      (fun k => if k ≤ i then x k else if k = i + 1 then z else x (k + (j - i) - 1)) := by
  obtain ⟨hx0, hxn, hxs⟩ := hx
  refine ⟨by simp [hx0], ?_, ?_⟩
  · dsimp only
    rw [if_neg (by omega), if_neg (by omega), show i + 1 + (n - j) + (j - i) - 1 = n by omega]
    exact hxn
  · intro k hk; dsimp only
    by_cases h1 : k + 1 ≤ i
    · rw [if_pos (by omega), if_pos h1]; exact hxs k (by omega)
    · by_cases h2 : k = i
      · subst h2
        rw [if_pos le_rfl, if_neg (by omega), if_pos rfl]
        exact ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) hzi).trans
          (hxs k (by omega))
      · by_cases h3 : k = i + 1
        · subst h3
          rw [if_neg (by omega), if_pos rfl, if_neg (by omega), if_neg (by omega),
            show i + 1 + 1 + (j - i) - 1 = j + 1 by omega]
          exact ((convex_segment _ _).segment_subset hzj (right_mem_segment _ _ _)).trans
            (hxs j hj)
        · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
            show k + 1 + (j - i) - 1 = (k + (j - i) - 1) + 1 by omega]
          exact hxs _ (by omega)

/-- Removing vertex `i + 1`. -/
lemma walk_remove {U : Set (ℝ × ℝ)} {a b : ℝ × ℝ} {n : ℕ} {x : ℕ → ℝ × ℝ}
    (hx : IsWalk U a b n x) {i : ℕ} (hi : i + 2 ≤ n)
    (hs : segment ℝ (x i) (x (i + 2)) ⊆ U) :
    IsWalk U a b (n - 1) (fun k => if k ≤ i then x k else x (k + 1)) := by
  obtain ⟨hx0, hxn, hxs⟩ := hx
  refine ⟨by simp [hx0], ?_, ?_⟩
  · dsimp only; rw [if_neg (by omega), show n - 1 + 1 = n by omega]; exact hxn
  · intro k hk; dsimp only
    by_cases h1 : k + 1 ≤ i
    · rw [if_pos (by omega), if_pos h1]; exact hxs k (by omega)
    · by_cases h2 : k = i
      · subst h2; rw [if_pos le_rfl, if_neg (by omega)]; exact hs
      · rw [if_neg (by omega), if_neg h1]; exact hxs (k + 1) (by omega)

lemma seg_geom {p q r z : ℝ × ℝ} (hq : z ∈ segment ℝ p q) (hr : z ∈ segment ℝ p r)
    (hz : z ≠ p) : q ∈ segment ℝ p r ∨ r ∈ segment ℝ p q := by
  rw [segment_eq_image'] at hq hr
  obtain ⟨s, ⟨hs0, hs1⟩, rfl⟩ := hq
  obtain ⟨t, ⟨ht0, ht1⟩, h⟩ := hr
  beta_reduce at hz h
  have hs : s ≠ 0 := by rintro rfl; simp at hz
  have ht : t ≠ 0 := by
    rintro rfl; apply hz; simp only [zero_smul, add_zero] at h; exact h.symm
  have h' : s • (q - p) = t • (r - p) := (add_left_cancel h).symm
  rw [segment_eq_image', segment_eq_image']
  rcases le_total t s with hts | hst
  · left
    refine ⟨t / s, ⟨div_nonneg ht0 hs0, div_le_one_of_le₀ hts hs0⟩, ?_⟩
    have : (t / s) • (r - p) = q - p := by
      calc (t / s) • (r - p) = s⁻¹ • (t • (r - p)) := by rw [smul_smul, div_eq_inv_mul]
        _ = s⁻¹ • (s • (q - p)) := by rw [h']
        _ = q - p := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    simp only [this, add_sub_cancel]
  · right
    refine ⟨s / t, ⟨div_nonneg hs0 ht0, div_le_one_of_le₀ hst ht0⟩, ?_⟩
    have : (s / t) • (q - p) = r - p := by
      calc (s / t) • (q - p) = t⁻¹ • (s • (q - p)) := by rw [smul_smul, div_eq_inv_mul]
        _ = t⁻¹ • (t • (r - p)) := by rw [h']
        _ = r - p := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    simp only [this, add_sub_cancel]

lemma path_segment_injective {a b : ℝ × ℝ} (h : a ≠ b) :
    Function.Injective (Path.segment a b) := by
  intro s t hst
  simp only [Path.segment, Path.coe_mk_mk, AffineMap.lineMap_apply, vsub_eq_sub,
    vadd_eq_add] at hst
  have h2 : ((s : ℝ) - t) • (b - a) = 0 := by rw [sub_smul]; exact sub_eq_zero.2 (add_right_cancel hst)
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact Subtype.ext (sub_eq_zero.1 h3)
  · exact absurd (sub_eq_zero.1 h3).symm h

lemma path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X} (γ₁ : Path a b)
    (γ₂ : Path b c) (h₁ : Function.Injective γ₁) (h₂ : Function.Injective γ₂)
    (h : ∀ z, z ∈ range γ₁ → z ∈ range γ₂ → z = b) : Function.Injective (γ₁.trans γ₂) := by
  have key : ∀ s t : unitInterval, (s : ℝ) ≤ 1 / 2 → ¬ (t : ℝ) ≤ 1 / 2 →
      (γ₁.trans γ₂) s ≠ (γ₁.trans γ₂) t := by
    intro s t hs ht hst
    rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_neg ht] at hst
    have hb := h _ (mem_range_self _) (by rw [hst]; exact mem_range_self _)
    rw [hst] at hb
    have := congrArg Subtype.val (h₂ (hb.trans γ₂.source.symm))
    simp at this; linarith
  intro s t hst
  by_cases hs : (s : ℝ) ≤ 1 / 2 <;> by_cases ht : (t : ℝ) ≤ 1 / 2
  · rw [Path.trans_apply, Path.trans_apply, dif_pos hs, dif_pos ht] at hst
    have := congrArg Subtype.val (h₁ hst)
    exact Subtype.ext (by simp at this; linarith)
  · exact absurd hst (key s t hs ht)
  · exact absurd hst.symm (key t s ht hs)
  · rw [Path.trans_apply, Path.trans_apply, dif_neg hs, dif_neg ht] at hst
    have := congrArg Subtype.val (h₂ hst)
    exact Subtype.ext (by simp at this; linarith)

/-- An injective path along a walk whose segments meet only as consecutive segments must. -/
lemma arc_of_walk {n : ℕ} {x : ℕ → ℝ × ℝ}
    (P1 : ∀ i j, i + 2 ≤ j → j < n →
      Disjoint (segment ℝ (x i) (x (i + 1))) (segment ℝ (x j) (x (j + 1))))
    (P2 : ∀ i, i + 1 < n →
      segment ℝ (x i) (x (i + 1)) ∩ segment ℝ (x (i + 1)) (x (i + 2)) ⊆ {x (i + 1)})
    (P3 : ∀ i < n, x i ≠ x (i + 1)) :
    ∀ k, 1 ≤ k → k ≤ n → ∃ γ : Path (x 0) (x k), Function.Injective γ ∧
      range γ = ⋃ i, ⋃ (_ : i < k), segment ℝ (x i) (x (i + 1)) := by
  intro k hk1 hkn
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine ⟨Path.segment _ _, path_segment_injective (P3 0 (by omega)), ?_⟩
      rw [Path.range_segment]; ext z; simp
    · obtain ⟨γ, hγ, hr⟩ := ih hk (by omega)
      refine ⟨γ.trans (Path.segment _ _), path_trans_injective _ _ hγ
        (path_segment_injective (P3 k (by omega))) ?_, ?_⟩
      · intro z hz1 hz2
        rw [hr] at hz1; rw [Path.range_segment] at hz2
        simp only [mem_iUnion] at hz1
        obtain ⟨i, hi, hzi⟩ := hz1
        by_cases hik : i + 1 = k
        · subst hik
          have := P2 i (by omega) ⟨hzi, hz2⟩
          simpa using this
        · exact absurd hz2 (Set.disjoint_left.1 (P1 i k (by omega) (by omega)) hzi)
      · rw [Path.trans_range, hr, Path.range_segment]
        ext z; simp only [mem_union, mem_iUnion]
        constructor
        · rintro (⟨i, hi, h⟩ | h)
          · exact ⟨i, by omega, h⟩
          · exact ⟨k, by omega, h⟩
        · rintro ⟨i, hi, h⟩
          by_cases hik : i < k
          · exact Or.inl ⟨i, hik, h⟩
          · obtain rfl : i = k := by omega
            exact Or.inr h

lemma linked_of_walk {U O : Set (ℝ × ℝ)} (hUO : U ⊆ O) {a b : ℝ × ℝ} (hab : a ≠ b)
    (hex : ∃ n x, IsWalk U a b n x) : LinkedIn O a b := by
  classical
  have hex' : ∃ n, ∃ x, IsWalk U a b n x := hex
  set n := Nat.find hex' with hn
  obtain ⟨x, hx⟩ := Nat.find_spec hex'
  have hmin : ∀ m < n, ¬ ∃ x, IsWalk U a b m x := fun m hm => Nat.find_min hex' hm
  rw [← hn] at hx
  obtain ⟨hx0, hxn, hxs⟩ := hx
  have hwalk : IsWalk U a b n x := ⟨hx0, hxn, hxs⟩
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hxn; exact absurd (hx0.symm.trans hxn) hab
    · exact h
  have P3 : ∀ i < n, x i ≠ x (i + 1) := by
    intro i hi heq
    by_cases h : i + 1 < n
    · refine hmin (n - 1) (by omega) ⟨_, walk_remove hwalk (i := i) (by omega) ?_⟩
      rw [heq]; exact hxs (i + 1) h
    · refine hmin (n - 1) (by omega) ⟨x, hx0, ?_, fun k hk => hxs k (by omega)⟩
      rw [show n - 1 = i by omega, heq, show i + 1 = n by omega, hxn]
  have P1 : ∀ i j, i + 2 ≤ j → j < n →
      Disjoint (segment ℝ (x i) (x (i + 1))) (segment ℝ (x j) (x (j + 1))) := by
    intro i j hij hj
    rw [Set.disjoint_left]
    intro z hzi hzj
    exact hmin _ (by omega) ⟨_, walk_shortcut hwalk (by omega) hj hzi hzj⟩
  have P2 : ∀ i, i + 1 < n →
      segment ℝ (x i) (x (i + 1)) ∩ segment ℝ (x (i + 1)) (x (i + 2)) ⊆ {x (i + 1)} := by
    rintro i hi z ⟨hz1, hz2⟩
    by_contra hz
    rw [segment_symm] at hz1
    refine hmin (n - 1) (by omega) ⟨_, walk_remove hwalk (i := i) (by omega) ?_⟩
    rcases seg_geom hz1 hz2 hz with h | h
    · exact ((convex_segment _ _).segment_subset h (right_mem_segment _ _ _)).trans
        (hxs (i + 1) hi)
    · rw [segment_symm] at h
      exact ((convex_segment _ _).segment_subset (left_mem_segment _ _ _) h).trans
        (hxs i (by omega))
  obtain ⟨γ, hγ, hr⟩ := arc_of_walk P1 P2 P3 n hn0 le_rfl
  right
  refine ⟨range γ, ⟨⟨n, fun i => segment ℝ (x i) (x (i + 1)), fun i => ?_, ?_⟩,
    γ, (γ.continuous.isClosedEmbedding hγ).isEmbedding, rfl, by simp [hx0], by simp [hxn]⟩, ?_⟩
  · refine ⟨x i, x (i + 1), P3 i i.2, ?_⟩
    show segment ℝ (x i) (x (i + 1)) = _
    rw [segment_eq_image']; ext z; simp [eq_comm, and_assoc]
  · rw [hr]; ext z; simp only [mem_iUnion]
    constructor
    · rintro ⟨i, hi, h⟩; exact ⟨⟨i, hi⟩, h⟩
    · rintro ⟨i, h⟩; exact ⟨i, i.2, h⟩
  · rw [hr]
    exact iUnion_subset fun i => iUnion_subset fun hi => (hxs i hi).trans hUO

lemma linked_of_connected {U O : Set (ℝ × ℝ)} (hU : IsOpen U) (hc : IsConnected U)
    (hUO : U ⊆ O) {a b : ℝ × ℝ} (ha : a ∈ U) (hb : b ∈ U) : LinkedIn O a b := by
  by_cases hab : a = b
  · exact Or.inl hab
  · exact linked_of_walk hUO hab (walk_exists hU hc.isPreconnected ha hb)

lemma mem_of_linked {I J : Set (ℝ × ℝ)} (hI : IsOpen I) (hJ : IsOpen J) (hd : Disjoint I J)
    {a b : ℝ × ℝ} (h : LinkedIn (I ∪ J) a b) (ha : a ∈ I) : b ∈ I := by
  rcases h with rfl | ⟨Q, ⟨-, φ, hφ, rfl, h0, h1⟩, hQ⟩
  · exact ha
  · rcases (isPreconnected_range hφ.continuous).subset_or_subset hI hJ hd hQ with h | h
    · exact h1 ▸ h (mem_range_self _)
    · exact absurd (h0 ▸ h (mem_range_self _)) (Set.disjoint_left.1 hd ha)

lemma regions_eq {I J : Set (ℝ × ℝ)} (hI : IsOpen I) (hJ : IsOpen J) (hIc : IsConnected I)
    (hJc : IsConnected J) (hd : Disjoint I J) : regions (I ∪ J) = {I, J} := by
  have cls : ∀ {A B : Set (ℝ × ℝ)}, IsOpen A → IsOpen B → IsConnected A → Disjoint A B →
      A ∪ B = I ∪ J → ∀ a ∈ A, {b | b ∈ I ∪ J ∧ LinkedIn (I ∪ J) a b} = A := by
    intro A B hA hB hAc hAB hU a ha
    ext b
    constructor
    · rintro ⟨-, hl⟩
      rw [← hU] at hl
      exact mem_of_linked hA hB hAB hl ha
    · intro hb
      exact ⟨hU ▸ Or.inl hb, linked_of_connected hA hAc (hU ▸ subset_union_left) ha hb⟩
  ext R
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ha | ha
    · left; exact cls hI hJ hIc hd rfl a ha
    · right; exact cls hJ hI hJc hd.symm (union_comm _ _) a ha
  · rintro (rfl | rfl)
    · obtain ⟨a, ha⟩ := hIc.nonempty
      exact ⟨a, Or.inl ha, (cls hI hJ hIc hd rfl a ha).symm⟩
    · obtain ⟨a, ha⟩ := hJc.nonempty
      exact ⟨a, Or.inr ha, (cls hJ hI hJc hd.symm (union_comm _ _) a ha).symm⟩

/-- The Jordan curve theorem transported to `ℝ × ℝ`. -/
lemma jordan_prod {P : Set (ℝ × ℝ)} (hP : Nonempty (P ≃ₜ unitCircle)) :
    ∃ I J : Set (ℝ × ℝ), IsOpen I ∧ IsOpen J ∧ IsConnected I ∧ IsConnected J ∧
      Disjoint I J ∧ I ∪ J = Pᶜ ∧ frontier I = P ∧ frontier J = P := by
  obtain ⟨h⟩ := hP
  let e : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  have he : ∀ v, e v = (v 0, v 1) := fun v => rfl
  have hnorm : ∀ v : EuclideanSpace ℝ (Fin 2), v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      e v ∈ unitCircle := by
    intro v
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two, he]
    simp only [unitCircle, mem_ofPred_eq, Real.norm_eq_abs, sq_abs]
    exact Real.sqrt_eq_one
  let γ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → EuclideanSpace ℝ (Fin 2) :=
    fun v => e.symm (h.symm ⟨e v, (hnorm v).1 v.2⟩ : P)
  have hγc : Continuous γ :=
    e.symm.continuous.comp (continuous_subtype_val.comp (h.symm.continuous.comp
      ((e.continuous.comp continuous_subtype_val).subtype_mk _)))
  have hγi : Function.Injective γ := by
    intro v w hvw
    have h1 := h.symm.injective (Subtype.ext (e.symm.injective hvw))
    exact Subtype.ext (e.injective (congrArg Subtype.val h1))
  have hrange : range γ = e ⁻¹' P := by
    ext w
    constructor
    · rintro ⟨v, rfl⟩
      simp only [γ, mem_preimage, Homeomorph.apply_symm_apply]
      exact (h.symm _).2
    · intro hw
      set q := h ⟨e w, hw⟩
      have hq : e (e.symm q.1) ∈ unitCircle := by simp
      refine ⟨⟨e.symm q.1, (hnorm _).2 hq⟩, ?_⟩
      have : (⟨e (e.symm q.1), hq⟩ : unitCircle) = q := Subtype.ext (by simp)
      simp only [γ, this, q, Homeomorph.symm_apply_apply]
  obtain ⟨I, J, hIo, hJo, hIc, hJc, -, -, hd, hU, hfI, hfJ⟩ :=
    JordanCurve.jordan_curve_theorem γ hγc hγi
  have hPP : e.symm ⁻¹' (e ⁻¹' P) = P := by ext z; simp
  refine ⟨e.symm ⁻¹' I, e.symm ⁻¹' J, hIo.preimage e.symm.continuous,
    hJo.preimage e.symm.continuous, ?_, ?_, hd.preimage _, ?_, ?_, ?_⟩
  · rw [e.preimage_symm]; exact hIc.image _ e.continuous.continuousOn
  · rw [e.preimage_symm]; exact hJc.image _ e.continuous.continuousOn
  · rw [← preimage_union, hU, hrange, preimage_compl, hPP]
  · rw [← e.symm.preimage_frontier, hfI, hrange, hPP]
  · rw [← e.symm.preimage_frontier, hfJ, hrange, hPP]

theorem jordan_curve_polygon' (P : Set (ℝ × ℝ)) (hP : IsPolygon P) :
    Nat.card (regions Pᶜ) = 2 ∧ ∀ O ∈ regions Pᶜ, frontier O = P := by
  obtain ⟨I, J, hIo, hJo, hIc, hJc, hd, hU, hfI, hfJ⟩ := jordan_prod hP.2
  rw [← hU, regions_eq hIo hJo hIc hJc hd]
  refine ⟨?_, ?_⟩
  · rw [Nat.card_coe_set_eq, Set.ncard_pair]
    intro hIJ
    obtain ⟨a, ha⟩ := hIc.nonempty
    exact Set.disjoint_left.1 hd ha (hIJ ▸ ha)
  · rintro O (rfl | rfl)
    · exact hfI
    · exact hfJ

end DiestelGraphTheory

theorem solution (P : Set (ℝ × ℝ)) (hP : DiestelGraphTheory.IsPolygon P) :
    Nat.card (DiestelGraphTheory.regions Pᶜ) = 2 ∧
      ∀ O ∈ DiestelGraphTheory.regions Pᶜ, frontier O = P :=
  DiestelGraphTheory.jordan_curve_polygon' P hP
