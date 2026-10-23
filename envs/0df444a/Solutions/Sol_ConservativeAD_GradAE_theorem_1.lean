-- Prove2me | solution 1 for ConservativeAD.GradAE.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T17:48:16.998988+00:00
-- url     : https://prove2.me/submissions/a2573d0c-83b1-48ad-bbf7-e74f039f3ef2

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField

set_option autoImplicit false

open MeasureTheory

namespace P129fecca

open ConservativeAD.GradAE

/-- Rademacher's theorem for locally Lipschitz functions on Euclidean space. -/
lemma ae_diff_of_locLip {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))), DifferentiableAt ℝ f x := by
  choose K t ht hK using hf
  obtain ⟨s, hsc, hcov⟩ := TopologicalSpace.countable_cover_nhds
    (f := fun x => interior (t x)) (fun x => interior_mem_nhds.2 (ht x))
  have h : ∀ i ∈ s, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      x ∈ interior (t i) → DifferentiableAt ℝ f x := by
    intro i _
    filter_upwards [((hK i).mono interior_subset).ae_differentiableWithinAt_of_mem] with x hx hxi
    exact (hx hxi).differentiableAt (isOpen_interior.mem_nhds hxi)
  rw [← ae_ball_iff hsc] at h
  filter_upwards [h] with x hx
  have : x ∈ ⋃ i ∈ s, interior (t i) := hcov ▸ Set.mem_univ x
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 this
  exact hx i hi hxi

/-- A measurable set whose traces on all lines in direction `u` (over `r ∈ (0, 1/2)`) are null
is null. -/
lemma null_of_lines {p : ℕ} (u : EuclideanSpace ℝ (Fin p))
    {S : Set (EuclideanSpace ℝ (Fin p))} (hS : MeasurableSet S)
    (h : ∀ y, volume ({r : ℝ | y + r • u ∈ S} ∩ Set.Ioo (0:ℝ) (1/2)) = 0) :
    volume S = 0 := by
  have hmeas : Measurable (fun z : (EuclideanSpace ℝ (Fin p)) × ℝ =>
      S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (z.1 + z.2 • u)) :=
    (measurable_one.indicator hS).comp (by fun_prop)
  have key : ∫⁻ r in Set.Ioo (0:ℝ) (1/2), ∫⁻ x, S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (x + r • u)
      = ∫⁻ x, ∫⁻ r in Set.Ioo (0:ℝ) (1/2), S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (x + r • u) := by
    apply lintegral_lintegral_swap
    exact (hmeas.comp measurable_swap).aemeasurable
  have lhs : ∀ r : ℝ, ∫⁻ x, S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (x + r • u) = volume S := by
    intro r
    rw [lintegral_add_right_eq_self (fun x => S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) x) (r • u)]
    exact lintegral_indicator_one hS
  have rhs : ∀ x, ∫⁻ r in Set.Ioo (0:ℝ) (1/2), S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (x + r • u) = 0 := by
    intro x
    have hm : MeasurableSet {r : ℝ | x + r • u ∈ S} := hS.preimage (by fun_prop)
    have : (fun r : ℝ => S.indicator (1 : EuclideanSpace ℝ (Fin p) → ENNReal) (x + r • u))
        = {r : ℝ | x + r • u ∈ S}.indicator (1 : ℝ → ENNReal) := by
      ext r; simp [Set.indicator]
    rw [this, lintegral_indicator_one hm, Measure.restrict_apply hm]
    exact h x
  simp only [lhs, rhs, lintegral_zero, setLIntegral_const, Real.volume_Ioo] at key
  rcases mul_eq_zero.1 key with h1 | h1
  · exact h1
  · norm_num at h1

lemma iint_congr_Ioo {F G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioo a b, F t = G t) :
    ∫ t in a..b, F t = ∫ t in a..b, G t := by
  apply intervalIntegral.integral_congr_ae
  have hb : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hb] with t htb ht
  rw [Set.uIoc_of_le hab] at ht
  exact h t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩

lemma iint_integrable_congr_Ioo {F G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ t ∈ Set.Ioo a b, F t = G t) (hF : IntervalIntegrable F volume a b) :
    IntervalIntegrable G volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab] at hF ⊢
  exact hF.congr_fun (fun t ht => h t ht) measurableSet_Ioo

lemma circ_of_deriv_zero {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (γ : ℝ → EuclideanSpace ℝ (Fin p)) (t : ℝ) (h : deriv γ t = 0) : circ D γ t = 0 := by
  unfold circ
  rw [h]
  simp only [inner_zero_left]
  rcases (D (γ t)).eq_empty_or_nonempty with h' | h'
  · simp [h']
  · rw [h'.image_const]; simp

/-- The path: first `0 → y` on `[0,1/2]`, rest until `1-s`, then move with velocity `u`. -/
noncomputable def pth {p : ℕ} (y u : EuclideanSpace ℝ (Fin p)) (s : ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin p) :=
  (2 * min t (1/2)) • y + (max (t - (1 - s)) 0) • u

lemma pth_ac {p : ℕ} (y u : EuclideanSpace ℝ (Fin p)) (s : ℝ) :
    AbsolutelyContinuousOnInterval (pth y u s) 0 1 := by
  have hL : LipschitzWith (2 * ‖y‖₊ + ‖u‖₊) (pth y u s) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [pth, dist_eq_norm, Real.dist_eq]
    have e : (2 * min a (1/2)) • y + (max (a - (1 - s)) 0) • u
        - ((2 * min b (1/2)) • y + (max (b - (1 - s)) 0) • u)
        = (2 * min a (1/2) - 2 * min b (1/2)) • y
          + (max (a - (1 - s)) 0 - max (b - (1 - s)) 0) • u := by
      rw [sub_smul, sub_smul]; abel
    rw [e]
    have h1 : |min a (1/2) - min b (1/2)| ≤ |a - b| := by
      simpa using abs_min_sub_min_le_max a (1/2 : ℝ) b (1/2)
    have h2 : |max (a - (1 - s)) 0 - max (b - (1 - s)) 0| ≤ |a - b| := by
      simpa using abs_max_sub_max_le_abs (a - (1 - s)) (b - (1 - s)) 0
    have h1' : |2 * min a (1/2) - 2 * min b (1/2)| ≤ 2 * |a - b| := by
      rw [← mul_sub, abs_mul]; norm_num; exact h1
    calc _ ≤ ‖(2 * min a (1/2) - 2 * min b (1/2)) • y‖
            + ‖(max (a - (1 - s)) 0 - max (b - (1 - s)) 0) • u‖ := norm_add_le _ _
      _ = |2 * min a (1/2) - 2 * min b (1/2)| * ‖y‖
            + |max (a - (1 - s)) 0 - max (b - (1 - s)) 0| * ‖u‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (2 * |a - b|) * ‖y‖ + |a - b| * ‖u‖ := by gcongr
      _ = _ := by push_cast; rw [Real.norm_eq_abs]; ring
  exact hL.lipschitzOnWith.absolutelyContinuousOnInterval

lemma uIcc_sub01 (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Set.uIcc a b ⊆ Set.uIcc 0 1 := by
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact Set.Icc_subset_Icc ha hb

lemma line_formula {p : ℕ} {D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hD : IsPotential D f) (y u : EuclideanSpace ℝ (Fin p)) :
    IntervalIntegrable (fun r : ℝ => sSup ((fun v => inner ℝ u v) '' D (y + r • u))) volume 0 (1/2)
    ∧ ∀ s ∈ Set.Icc (0:ℝ) (1/2), f (y + s • u)
        = f y + ∫ r in (0:ℝ)..s, sSup ((fun v => inner ℝ u v) '' D (y + r • u)) := by
  set g : ℝ → ℝ := fun r => sSup ((fun v => inner ℝ u v) '' D (y + r • u)) with hg
  have h0 : ∀ s : ℝ, s ≤ 1/2 → pth y u s 0 = 0 := by
    intro s hs
    rw [pth, min_eq_left (by norm_num : (0:ℝ) ≤ 1/2), max_eq_right (by linarith : (0:ℝ) - (1 - s) ≤ 0)]
    simp
  have h1 : ∀ s : ℝ, 0 ≤ s → pth y u s 1 = y + s • u := by
    intro s hs
    rw [pth, min_eq_right (by norm_num : (1/2:ℝ) ≤ 1), show (1:ℝ) - (1 - s) = s by ring,
      max_eq_left hs]
    norm_num
  have hA : ∀ s : ℝ, s ≤ 1/2 → ∀ t ∈ Set.Ioo (0:ℝ) (1/2),
      circ D (pth y u s) t = circ D (pth y u 0) t := by
    intro s hs t ht
    have he : pth y u s =ᶠ[nhds t] pth y u 0 := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
      simp only [pth]
      rw [max_eq_right (by linarith [hτ.2]), max_eq_right (by linarith [hτ.2])]
    unfold circ
    rw [he.deriv_eq, he.eq_of_nhds]
  have hB : ∀ s : ℝ, s ≤ 1/2 → ∀ t ∈ Set.Ioo (1/2:ℝ) (1 - s), circ D (pth y u s) t = 0 := by
    intro s hs t ht
    have he : pth y u s =ᶠ[nhds t] fun _ => y := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
      simp only [pth]
      rw [min_eq_right (by linarith [hτ.1]), max_eq_right (by linarith [hτ.2])]
      norm_num
    apply circ_of_deriv_zero
    rw [he.deriv_eq]; simp
  have hC : ∀ s : ℝ, s ≤ 1/2 → ∀ t ∈ Set.Ioo (1 - s) 1,
      circ D (pth y u s) t = g (t - (1 - s)) := by
    intro s hs t ht
    have he : pth y u s =ᶠ[nhds t] fun τ => y + (τ - (1 - s)) • u := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
      simp only [pth]
      rw [min_eq_right (by linarith [hτ.1]), max_eq_left (by linarith [hτ.1])]
      norm_num
    have hd : HasDerivAt (fun τ : ℝ => y + (τ - (1 - s)) • u) u t := by
      simpa using (((hasDerivAt_id t).sub_const (1 - s)).smul_const u).const_add y
    unfold circ
    rw [he.deriv_eq, hd.deriv, he.eq_of_nhds]
  refine ⟨?_, ?_⟩
  · obtain ⟨hI, -⟩ := hD.2 (y + (1/2:ℝ) • u) (pth y u (1/2)) (pth_ac y u _) (h0 _ le_rfl)
      (h1 _ (by norm_num))
    have hI' : IntervalIntegrable (circ D (pth y u (1/2))) volume (1 - 1/2) 1 :=
      hI.mono_set (uIcc_sub01 (1 - 1/2) 1 (by norm_num) (by norm_num) le_rfl)
    have hh := iint_integrable_congr_Ioo (by norm_num) (hC (1/2) le_rfl) hI'
    have := hh.comp_sub_right (-(1 - 1/2 : ℝ))
    convert this using 1
    · funext x; simp only [hg]; congr 2; ring
    · norm_num
    · norm_num
  · intro s hs
    obtain ⟨hIs, hfs⟩ := hD.2 (y + s • u) (pth y u s) (pth_ac y u _) (h0 _ hs.2) (h1 _ hs.1)
    obtain ⟨hI0, hf0⟩ := hD.2 y (pth y u 0) (pth_ac y u _) (h0 _ (by norm_num))
      (by simpa using h1 0 le_rfl)
    have hc1 : (1/2 : ℝ) ≤ 1 - s := by linarith [hs.2]
    have hc2 : 1 - s ≤ 1 := by linarith [hs.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hIs.mono_set (uIcc_sub01 0 (1/2) le_rfl (by norm_num) (by norm_num)))
        (hIs.mono_set (uIcc_sub01 (1/2) 1 (by norm_num) (by norm_num) le_rfl)),
      ← intervalIntegral.integral_add_adjacent_intervals
        (hIs.mono_set (uIcc_sub01 (1/2) (1 - s) (by norm_num) hc1 hc2))
        (hIs.mono_set (uIcc_sub01 (1 - s) 1 (by linarith) hc2 le_rfl))] at hfs
    rw [← intervalIntegral.integral_add_adjacent_intervals
        (hI0.mono_set (uIcc_sub01 0 (1/2) le_rfl (by norm_num) (by norm_num)))
        (hI0.mono_set (uIcc_sub01 (1/2) 1 (by norm_num) (by norm_num) le_rfl))] at hf0
    have hB0 : ∀ t ∈ Set.Ioo (1/2:ℝ) 1, circ D (pth y u 0) t = 0 :=
      fun t ht => hB 0 (by norm_num) t (by simpa using ht)
    rw [iint_congr_Ioo (by norm_num) (hA s hs.2), iint_congr_Ioo hc1 (hB s hs.2),
      iint_congr_Ioo hc2 (hC s hs.2), intervalIntegral.integral_comp_sub_right] at hfs
    rw [iint_congr_Ioo (by norm_num) hB0] at hf0
    simp only [intervalIntegral.integral_zero, sub_self, sub_sub_cancel] at hfs hf0
    rw [hfs, hf0]
    ring

lemma line_key {p : ℕ} {D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hD : IsPotential D f) (y u : EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Set.Ioo (0:ℝ) (1/2) → DifferentiableAt ℝ f (y + r • u) →
      ∀ v ∈ D (y + r • u), inner ℝ u v ≤ fderiv ℝ f (y + r • u) u := by
  obtain ⟨hg, hF⟩ := line_formula hD y u
  filter_upwards [hg.ae_hasDerivAt_integral] with r hr hrI hdiff v hv
  have hrI' : r ∈ Set.uIcc (0:ℝ) (1/2) := by
    rw [Set.uIcc_of_le (by norm_num)]; exact Set.Ioo_subset_Icc_self hrI
  have h1 := hr hrI' 0 (by simp [Set.mem_uIcc])
  have h2 : HasDerivAt (fun s : ℝ => f (y + s • u))
      (sSup ((fun v => inner ℝ u v) '' D (y + r • u))) r := by
    have := h1.const_add (f y)
    apply this.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hrI.1 hrI.2] with s hs
    exact hF s (Set.Ioo_subset_Icc_self hs)
  have h3 : HasDerivAt (fun s : ℝ => f (y + s • u)) (fderiv ℝ f (y + r • u) u) r := by
    have hl : HasDerivAt (fun s : ℝ => y + s • u) u r := by
      simpa using ((hasDerivAt_id r).smul_const u).const_add y
    exact hdiff.hasFDerivAt.comp_hasDerivAt r hl
  rw [h3.unique h2]
  exact le_csSup (((hD.1.2.1 _).2.image (by fun_prop)).bddAbove) (Set.mem_image_of_mem _ hv)

lemma dir_key {p : ℕ} {D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ} (hD : IsPotential D f) (u : EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))), DifferentiableAt ℝ f x →
      ∀ v ∈ D x, inner ℝ u v ≤ fderiv ℝ f x u := by
  classical
  let K : ℚ → ℕ → ℕ → Set (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p)) := fun q n m =>
    {z | z.2 ∈ D z.1} ∩ ({z | ‖z.1‖ ≤ m} ∩ ({z | ‖z.2‖ ≤ n} ∩ {z | (q:ℝ) ≤ inner ℝ u z.2}))
  let S : ℚ → ℕ → ℕ → Set (EuclideanSpace ℝ (Fin p)) := fun q n m =>
    ({x | DifferentiableAt ℝ f x} ∩ {x | fderiv ℝ f x u < q}) ∩ Prod.fst '' K q n m
  have hKc : ∀ q n m, IsCompact (K q n m) := by
    intro q n m
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hD.1.1.inter ((isClosed_le (by fun_prop) continuous_const).inter
        ((isClosed_le (by fun_prop) continuous_const).inter
          (isClosed_le continuous_const (by fun_prop))))
    · apply (Metric.isBounded_closedBall.prod Metric.isBounded_closedBall :
        Bornology.IsBounded (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) m ×ˢ
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) n)).subset
      intro z hz
      exact ⟨by simpa using hz.2.1, by simpa using hz.2.2.1⟩
  have hSm : ∀ q n m, MeasurableSet (S q n m) := by
    intro q n m
    refine ((measurableSet_of_differentiableAt (𝕜 := ℝ) (f := f)).inter
      (measurableSet_lt (measurable_fderiv_apply_const ℝ f u) measurable_const)).inter ?_
    exact ((hKc q n m).image continuous_fst).isClosed.measurableSet
  have hSnull : ∀ q n m, volume (S q n m) = 0 := by
    intro q n m
    apply null_of_lines u (hSm q n m)
    intro y
    apply measure_mono_null _ (ae_iff.1 (line_key hD y u))
    rintro r ⟨⟨⟨hd, hlt⟩, z, hz, hz1⟩, hr⟩ hcon
    have := hcon hr hd z.2 (hz1 ▸ hz.1)
    have h4 := hz.2.2.2
    simp only [Set.mem_setOf_eq] at hlt h4
    linarith
  rw [ae_iff]
  apply measure_mono_null _ (measure_iUnion_null fun q => measure_iUnion_null fun n =>
    measure_iUnion_null fun m => hSnull q n m)
  intro x hx
  simp only [Set.mem_setOf_eq, _root_.not_imp, not_forall, not_le] at hx
  obtain ⟨hd, v, hv, hlt⟩ := hx
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  obtain ⟨n, hn⟩ := exists_nat_ge ‖v‖
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  simp only [Set.mem_iUnion]
  exact ⟨q, n, m, ⟨⟨hd, hq1⟩, (x, v), ⟨hv, hm, hn, hq2.le⟩, rfl⟩⟩

lemma main {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      DifferentiableAt ℝ f x ∧ D x = {gradient f x} := by
  have h1 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))), ∀ i : Fin p,
      DifferentiableAt ℝ f x → ∀ v ∈ D x, inner ℝ (EuclideanSpace.single i (1:ℝ)) v
        ≤ fderiv ℝ f x (EuclideanSpace.single i 1) :=
    ae_all_iff.2 fun i => dir_key hD _
  have h2 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))), ∀ i : Fin p,
      DifferentiableAt ℝ f x → ∀ v ∈ D x, inner ℝ (-EuclideanSpace.single i (1:ℝ)) v
        ≤ fderiv ℝ f x (-EuclideanSpace.single i 1) :=
    ae_all_iff.2 fun i => dir_key hD _
  filter_upwards [ae_diff_of_locLip hf, h1, h2] with x hx h1 h2
  refine ⟨hx, ?_⟩
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  refine ⟨(hD.1.2.1 x).1, fun v hv => ?_⟩
  ext i
  have a1 := h1 i hx v hv
  have a2 := h2 i hx v hv
  rw [EuclideanSpace.inner_single_left] at a1
  rw [inner_neg_left, EuclideanSpace.inner_single_left, map_neg] at a2
  have hg := EuclideanSpace.inner_single_left i (1:ℝ) (gradient f x)
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply] at hg
  simp at a1 a2 hg
  unfold gradient
  linarith

end P129fecca

open MeasureTheory ConservativeAD.GradAE in
theorem solution {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      DifferentiableAt ℝ f x ∧ D x = {gradient f x} := by
  exact P129fecca.main D f hD hf
