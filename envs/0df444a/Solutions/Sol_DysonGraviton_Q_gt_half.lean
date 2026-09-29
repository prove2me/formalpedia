-- Prove2me | solution 1 for DysonGraviton.Q_gt_half
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:41:07.924083+00:00
-- url     : https://prove2.me/submissions/bc77f8cc-d320-4cc5-aa56-25beb1b06723

import Definitions.Def_DysonGraviton_Defs
import Mathlib

open MeasureTheory Filter Topology
open DysonGraviton

theorem W7b_DysonGraviton_mH : MeasurableSet halfPlane :=
  measurableSet_Ioi.prod MeasurableSet.univ

theorem W7b_DysonGraviton_restrict :
    (volume : Measure (ℝ × ℝ)).restrict halfPlane =
      ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod (volume : Measure ℝ) := by
  rw [halfPlane, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

/-- Translation in the `s` direction is quasi-measure-preserving on the half plane. -/
theorem W7b_DysonGraviton_qmp (c : ℝ) (hc : 0 < c) :
    Measure.QuasiMeasurePreserving (fun p : ℝ × ℝ => p + (c, 0))
      ((volume : Measure (ℝ × ℝ)).restrict halfPlane) ((volume : Measure (ℝ × ℝ)).restrict halfPlane) := by
  refine ⟨measurable_add_const _, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun A hA hA0 => ?_
  rw [Measure.map_apply (measurable_add_const _) hA, Measure.restrict_apply' W7b_DysonGraviton_mH]
  rw [Measure.restrict_apply' W7b_DysonGraviton_mH] at hA0
  have hsub : (fun p : ℝ × ℝ => p + (c, 0)) ⁻¹' A ∩ halfPlane ⊆
      (fun p : ℝ × ℝ => p + (c, 0)) ⁻¹' (A ∩ halfPlane) := by
    rintro p ⟨hpA, hpH⟩
    refine ⟨hpA, ?_⟩
    simp only [halfPlane, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, and_true] at hpH ⊢
    simp only [Prod.fst_add]; linarith
  refine measure_mono_null hsub ?_
  rw [(measurePreserving_add_right volume ((c, 0) : ℝ × ℝ)).measure_preimage
    (hA.inter W7b_DysonGraviton_mH).nullMeasurableSet]
  exact hA0

/-- The cross term `2 f ∂ₛf` is a.e.-strongly measurable on the half plane. -/
theorem W7b_DysonGraviton_cross_meas (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => 2 * f p.1 p.2 * dS f p.1 p.2)
      ((volume : Measure (ℝ × ℝ)).restrict halfPlane) := by
  set μ := (volume : Measure (ℝ × ℝ)).restrict halfPlane
  have hmem : ∀ᵐ p ∂μ, p ∈ halfPlane := ae_restrict_mem W7b_DysonGraviton_mH
  -- measurability of `u = f²`
  set u : ℝ × ℝ → ℝ := fun p => f p.1 p.2 ^ 2 with hu_def
  have hu : AEStronglyMeasurable u μ := by
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1⁻¹ * (p.1 * f p.1 p.2 ^ 2)) μ :=
      (measurable_fst.inv.aestronglyMeasurable).mul hf.aestronglyMeasurable
    refine h2.congr ?_
    filter_upwards [hmem] with p hp
    have : p.1 ≠ 0 := (show 0 < p.1 from hp.1).ne'
    simp only [hu_def]; field_simp
  -- difference quotients
  set D : ℕ → ℝ × ℝ → ℝ := fun n p =>
    ((n : ℝ) + 1) * (u (p + ((1 : ℝ) / ((n : ℝ) + 1), 0)) - u p) with hD
  have hDm : ∀ n, AEStronglyMeasurable (D n) μ := by
    intro n
    have hq := W7b_DysonGraviton_qmp ((1 : ℝ) / ((n : ℝ) + 1)) (by positivity)
    exact aestronglyMeasurable_const.mul ((hu.comp_quasiMeasurePreserving hq).sub hu)
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun n => D n p) atTop
      (𝓝 (2 * f p.1 p.2 * dS f p.1 p.2)) := by
    filter_upwards [hmem] with p hp
    have hs : 0 < p.1 := hp.1
    have hd := (hdiff p.2 p.1 hs).hasDerivAt.pow 2
    have hslope := hasDerivAt_iff_tendsto_slope.mp hd
    have hseq : Tendsto (fun n : ℕ => p.1 + (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[≠] p.1) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
        simpa using (tendsto_const_nhds (x := p.1)).add this
      · refine Eventually.of_forall fun n => ?_
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have := hslope.comp hseq
    convert this using 1
    · funext n
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      simp only [Function.comp, slope, vsub_eq_sub, smul_eq_mul, hD, hu_def, Prod.fst_add,
        Prod.snd_add, add_zero, Pi.pow_apply]
      rw [show p.1 + 1 / ((n : ℝ) + 1) - p.1 = 1 / ((n : ℝ) + 1) by ring, one_div, inv_inv]
    · simp [dS]
  exact aestronglyMeasurable_of_tendsto_ae atTop hDm hlim

/-- The integrand of `ineq17` is integrable on the half plane. -/
theorem W7b_DysonGraviton_integrable (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2) halfPlane := by
  set μ := (volume : Measure (ℝ × ℝ)).restrict halfPlane
  have hmem : ∀ᵐ p ∂μ, p ∈ halfPlane := ae_restrict_mem W7b_DysonGraviton_mH
  have hcross := W7b_DysonGraviton_cross_meas f hdiff hf
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2) μ := by
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2
        + p.1 ^ 2 * (2 * f p.1 p.2 * dS f p.1 p.2) + p.1 * f p.1 p.2 ^ 2) μ :=
      (hdf.aestronglyMeasurable.add
        ((measurable_fst.pow_const 2).aestronglyMeasurable.mul hcross)).add hf.aestronglyMeasurable
    refine h3.congr ?_
    filter_upwards [hmem] with p hp
    have : p.1 ≠ 0 := (show 0 < p.1 from hp.1).ne'
    field_simp; ring
  refine Integrable.mono' ((hdf.const_mul 2).add (hf.const_mul 2)) hmeas ?_
  filter_upwards [hmem] with p hp
  have hs : 0 < p.1 := hp.1
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have key : p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2 + p.1 ^ 3 * (dS f p.1 p.2 - f p.1 p.2 / p.1) ^ 2
      = 2 * (p.1 ^ 3 * dS f p.1 p.2 ^ 2) + 2 * (p.1 * f p.1 p.2 ^ 2) := by
    field_simp; ring
  have : 0 ≤ p.1 ^ 3 * (dS f p.1 p.2 - f p.1 p.2 / p.1) ^ 2 := by positivity
  simp only [Pi.add_apply]
  linarith

theorem W7b_DysonGraviton_ineq17 (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane)
    (hne : ¬ (fun p : ℝ × ℝ => f p.1 p.2) =ᵐ[volume.restrict halfPlane] 0) :
    0 < ∫ p in halfPlane, p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2 := by
  have hI := W7b_DysonGraviton_integrable f hdiff hf hdf
  have hnn : 0 ≤ᵐ[volume.restrict halfPlane]
      (fun p : ℝ × ℝ => p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2) := by
    filter_upwards [ae_restrict_mem W7b_DysonGraviton_mH] with p hp
    have hs : 0 < p.1 := hp.1
    positivity
  rcases (integral_nonneg_of_ae hnn).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  apply hne
  have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hI).mp heq.symm
  set μs := (volume : Measure ℝ).restrict (Set.Ioi 0)
  rw [W7b_DysonGraviton_restrict] at hz ⊢
  -- pointwise vanishing of `(s f)'` for a.e. `z`, a.e. `s`
  have hz' : ∀ᵐ z ∂(volume : Measure ℝ), ∀ᵐ s ∂μs,
      s ^ 3 * (dS f s z + f s z / s) ^ 2 = 0 := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := μs)).quasiMeasurePreserving.ae hz
    exact Measure.ae_ae_of_ae_prod this
  have hint : ∀ᵐ z ∂(volume : Measure ℝ), Integrable (fun s => s * f s z ^ 2) μs := by
    have h := hf
    rw [IntegrableOn, W7b_DysonGraviton_restrict] at h
    exact h.prod_left_ae
  have hgood : ∀ᵐ z ∂(volume : Measure ℝ), ∀ s, 0 < s → f s z = 0 := by
    filter_upwards [hz', hint] with z hz hiz
    -- `g(s) = s f(s,z)` has derivative zero a.e. on `(0,∞)`
    have hg : ∀ s, 0 < s → HasDerivAt (fun t => t * f t z) (f s z + s * dS f s z) s := by
      intro s hs
      exact ((hasDerivAt_id' s).mul (hdiff z s hs).hasDerivAt).congr_deriv (by rw [one_mul]; rfl)
    have hg0 : ∀ᵐ s ∂μs, f s z + s * dS f s z = 0 := by
      filter_upwards [hz, ae_restrict_mem measurableSet_Ioi] with s hs hpos
      have hp : 0 < s := hpos
      have h1 : dS f s z + f s z / s = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp hs).resolve_left (by positivity))
        exact this
      field_simp at h1
      linarith
    have hconst : ∀ s, 0 < s → s * f s z = 1 * f 1 z := by
      intro s hs
      have key : ∀ a b : ℝ, 0 < a → a ≤ b → b * f b z - a * f a z = 0 := by
        intro a b ha hab
        have hsub : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun t => t * f t z) (f x z + x * dS f x z) x :=
          fun x hx => hg x (lt_of_lt_of_le ha (by rw [Set.uIcc_of_le hab] at hx; exact hx.1))
        have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → f x z + x * dS f x z = 0 := by
          have := hg0
          rw [ae_restrict_iff' measurableSet_Ioi] at this
          filter_upwards [this] with x hx hxab
          apply hx
          rw [Set.uIoc_of_le hab] at hxab
          exact lt_trans ha hxab.1
        have hii : IntervalIntegrable (fun x => f x z + x * dS f x z) volume a b := by
          refine (intervalIntegrable_const (c := (0 : ℝ))).congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_uIoc, ae_restrict_of_ae hae] with x hx1 hx2
          exact (hx2 hx1).symm
        rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt hsub hii]
        rw [intervalIntegral.integral_congr_ae (g := fun _ => (0 : ℝ)) hae]
        simp
      rcases le_total s 1 with h | h
      · have := key s 1 hs h; linarith
      · have := key 1 s one_pos h; linarith
    -- the constant must vanish by integrability of `s f² = C²/s`
    set C := f 1 z with hC
    have hC0 : C = 0 := by
      by_contra hCne
      apply not_integrableOn_Ioi_inv (a := 0)
      have hc2 : 0 < C ^ 2 := by positivity
      have : Integrable (fun s => (C ^ 2)⁻¹ * (s * f s z ^ 2)) μs := hiz.const_mul _
      refine this.congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs' : 0 < s := hs
      have hfs : f s z = C / s := by
        have := hconst s hs'; rw [one_mul] at this
        field_simp; linarith
      rw [hfs]; field_simp
    intro s hs
    have h3 := hconst s hs
    rw [one_mul] at h3
    have h4 : s * f s z = 0 := by rw [h3]; first | exact hC0 | (rw [← hC]; exact hC0)
    exact (mul_eq_zero.mp h4).resolve_left hs.ne'
  -- conclude `f = 0` a.e. on the half plane
  rw [ae_iff] at hgood
  rw [Filter.EventuallyEq, ae_iff]
  simp only [Pi.zero_apply]
  set N := {z : ℝ | ¬ ∀ s, 0 < s → f s z = 0}
  have hsub : {p : ℝ × ℝ | ¬ f p.1 p.2 = 0} ⊆ (Set.univ ×ˢ N) ∪ (Set.Iic 0 ×ˢ Set.univ) := by
    intro p hp
    by_cases h1 : p.1 ≤ 0
    · exact Or.inr ⟨h1, trivial⟩
    · refine Or.inl ⟨trivial, fun hall => hp (hall p.1 (lt_of_not_ge h1))⟩
  refine measure_mono_null hsub (measure_union_null ?_ ?_)
  · rw [Measure.prod_prod, hgood, mul_zero]
  · rw [Measure.prod_prod]
    have : μs (Set.Iic 0) = 0 := by
      rw [Measure.restrict_apply measurableSet_Iic]
      simp [Set.Iic_inter_Ioi]
    rw [this, zero_mul]

/-- The key inequality `s⁻¹ ≤ (2/L) (s F²)` when `L/2 < s² F²`. -/
theorem W7b_DysonGraviton_inv_le (L s y : ℝ) (hL : 0 < L) (hs : 0 < s) (hy : L / 2 < s ^ 2 * y) :
    ‖s⁻¹‖ ≤ 2 / L * (s * y) := by
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
  have key : 1 ≤ 2 / L * (s ^ 2 * y) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]; linarith
  calc s⁻¹ = 1 / s := by rw [one_div]
    _ ≤ (2 / L * (s ^ 2 * y)) / s := div_le_div_of_nonneg_right key hs.le
    _ = 2 / L * (s * y) := by field_simp

/-- One-dimensional weak integration by parts on `(0, ∞)`. -/
theorem W7b_DysonGraviton_ibp (F D : ℝ → ℝ) (hF : ∀ s, 0 < s → HasDerivAt F (D s) s)
    (h1 : IntegrableOn (fun s => s * F s ^ 2) (Set.Ioi 0))
    (h2 : IntegrableOn (fun s => s ^ 2 * (2 * F s * D s)) (Set.Ioi 0)) :
    ∫ s in Set.Ioi (0 : ℝ), s ^ 2 * (2 * F s * D s) = -2 * ∫ s in Set.Ioi (0 : ℝ), s * F s ^ 2 := by
  set φ : ℝ → ℝ := fun s => s ^ 2 * F s ^ 2 with hφdef
  set ψ : ℝ → ℝ := fun s => 2 * (s * F s ^ 2) + s ^ 2 * (2 * F s * D s) with hψdef
  have hφ : ∀ s, 0 < s → HasDerivAt φ (ψ s) s := by
    intro s hs
    have := (hasDerivAt_pow 2 s).mul ((hF s hs).pow 2)
    refine this.congr_deriv ?_
    show _ = 2 * (s * F s ^ 2) + s ^ 2 * (2 * F s * D s)
    simp only [Pi.pow_apply]
    push_cast; ring
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => by positivity
  have hψ : IntegrableOn ψ (Set.Ioi 0) := (h1.const_mul 2).add h2
  -- limit at infinity
  have hlim := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (a := 1)
    (fun x hx => hφ x (lt_trans one_pos hx)) (hψ.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  set L := limUnder Filter.atTop φ with hLdef
  have hL : L = 0 := by
    have hL0 : 0 ≤ L := ge_of_tendsto hlim (Filter.Eventually.of_forall hφ0)
    by_contra hne
    have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
    obtain ⟨A, hA⟩ :=
      Filter.eventually_atTop.mp (hlim.eventually (lt_mem_nhds (half_lt_self hLpos)))
    set A' := max A 1
    apply not_integrableOn_Ioi_inv (a := A')
    have hsub : Set.Ioi A' ⊆ Set.Ioi 0 := Set.Ioi_subset_Ioi (by positivity)
    refine Integrable.mono' ((h1.mono_set hsub).const_mul (2 / L))
      (measurable_inv.aestronglyMeasurable) ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs1 : 1 ≤ s := le_trans (le_max_right _ _) (le_of_lt hs)
    have hsA : A ≤ s := le_trans (le_max_left _ _) (le_of_lt hs)
    exact W7b_DysonGraviton_inv_le L s (F s ^ 2) hLpos (by linarith) (hA s hsA)
  rw [hL] at hlim
  have hInt1 : ∫ s in Set.Ioi (1 : ℝ), ψ s = -φ 1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' (fun x hx => hφ x (lt_of_lt_of_le one_pos hx))
      (hψ.mono_set (Set.Ioi_subset_Ioi zero_le_one)) hlim]
    ring
  -- behaviour near `0`
  have hψIcc : IntegrableOn ψ (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one, integrableOn_Icc_iff_integrableOn_Ioc]
    exact hψ.mono_set Set.Ioc_subset_Ioi_self
  set G : ℝ → ℝ := fun x => ∫ t in x..1, ψ t with hGdef
  have hGc := intervalIntegral.continuousOn_primitive_interval_left hψIcc
  have hφG : ∀ s ∈ Set.Ioc (0 : ℝ) 1, φ s = φ 1 - G s := by
    intro s hs
    have hsub : Set.uIcc s 1 ⊆ Set.Ioi 0 := by
      rw [Set.uIcc_of_le hs.2]; intro t ht; exact lt_of_lt_of_le hs.1 ht.1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hφ t (hsub ht))
      ((hψ.mono_set hsub).intervalIntegrable)
    simp only [hGdef]; linarith
  set L0 := φ 1 - G 0 with hL0def
  have hlim0 : Filter.Tendsto φ (nhdsWithin 0 (Set.Ioi 0)) (nhds L0) := by
    have hG0 : Filter.Tendsto G (nhdsWithin 0 (Set.Ioi 0)) (nhds (G 0)) := by
      have := hGc 0 (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)
      rw [Set.uIcc_of_le zero_le_one] at this
      exact this.tendsto.mono_left (nhdsWithin_le_of_mem
        (Filter.mem_of_superset (Ioo_mem_nhdsGT zero_lt_one) Set.Ioo_subset_Icc_self))
    have h2 : (fun s => φ 1 - G s) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] φ := by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with s hs
      exact (hφG s ⟨hs.1, hs.2.le⟩).symm
    exact (tendsto_const_nhds.sub hG0).congr' h2
  have hL0 : L0 = 0 := by
    have hnn : 0 ≤ L0 := ge_of_tendsto hlim0 (Filter.Eventually.of_forall hφ0)
    by_contra hne
    have hpos : 0 < L0 := lt_of_le_of_ne hnn (Ne.symm hne)
    have hev := hlim0.eventually (lt_mem_nhds (half_lt_self hpos))
    obtain ⟨u, hu0, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
    set δ := min u 1 with hδdef
    have hδ : 0 < δ := lt_min hu0 one_pos
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) MeasureTheory.volume 0 δ := by
      rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hδ.le]
      refine Integrable.mono' ((h1.mono_set Set.Ioo_subset_Ioi_self).const_mul (2 / L0))
        measurable_inv.aestronglyMeasurable ?_
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun s hs => ?_
      have hφs : L0 / 2 < φ s := hu ⟨hs.1, lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
      exact W7b_DysonGraviton_inv_le L0 s (F s ^ 2) hpos hs.1 hφs
    rcases intervalIntegrable_inv_iff.mp hinv with h | h
    · linarith
    · exact h (by rw [Set.uIcc_of_le hδ.le]; exact ⟨le_rfl, hδ.le⟩)
  have hInt0 : ∫ s in Set.Ioc (0 : ℝ) 1, ψ s = φ 1 := by
    rw [← intervalIntegral.integral_of_le zero_le_one]
    show G 0 = φ 1
    linarith
  have hsplit : ∫ s in Set.Ioi (0 : ℝ), ψ s =
      (∫ s in Set.Ioc (0 : ℝ) 1, ψ s) + ∫ s in Set.Ioi (1 : ℝ), ψ s := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hψ.mono_set Set.Ioc_subset_Ioi_self) (hψ.mono_set (Set.Ioi_subset_Ioi zero_le_one))
  have hψ0 : ∫ s in Set.Ioi (0 : ℝ), ψ s = 0 := by rw [hsplit, hInt0, hInt1]; ring
  simp only [hψdef] at hψ0
  rw [integral_add (h1.const_mul 2) h2, integral_const_mul] at hψ0
  linarith

/-- The cross term `s² (2 f f')` is integrable on the half plane. -/
theorem W7b_DysonGraviton_cross_int (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 2 * (2 * f p.1 p.2 * dS f p.1 p.2)) halfPlane := by
  refine Integrable.mono' (hdf.add hf)
    ((measurable_fst.pow_const 2).aestronglyMeasurable.mul
      (W7b_DysonGraviton_cross_meas f hdiff hf)) ?_
  filter_upwards [ae_restrict_mem W7b_DysonGraviton_mH] with p hp
  have hs : 0 < p.1 := hp.1
  rw [Real.norm_eq_abs]
  simp only [Pi.add_apply]
  have h1 : 0 ≤ p.1 * (p.1 * dS f p.1 p.2 - f p.1 p.2) ^ 2 := by positivity
  have h2 : 0 ≤ p.1 * (p.1 * dS f p.1 p.2 + f p.1 p.2) ^ 2 := by positivity
  rw [abs_le]; constructor <;> nlinarith

theorem solution (f : ℝ → ℝ → ℝ)
    (hdiff : ∀ z s : ℝ, 0 < s → DifferentiableAt ℝ (fun t => f t z) s)
    (hf : IntegrableOn (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) halfPlane)
    (hdf : IntegrableOn (fun p : ℝ × ℝ => p.1 ^ 3 * dS f p.1 p.2 ^ 2) halfPlane)
    (hne : ¬ (fun p : ℝ × ℝ => f p.1 p.2) =ᵐ[volume.restrict halfPlane] 0) :
    1 / 2 < Q f := by
  have hpos := W7b_DysonGraviton_ineq17 f hdiff hf hdf hne
  have hcI := W7b_DysonGraviton_cross_int f hdiff hf hdf
  -- positivity of the denominator
  have hden : 0 < denQ f := by
    unfold denQ
    have hnn : 0 ≤ᵐ[volume.restrict halfPlane] (fun p : ℝ × ℝ => p.1 * f p.1 p.2 ^ 2) := by
      filter_upwards [ae_restrict_mem W7b_DysonGraviton_mH] with p hp
      have hs : 0 < p.1 := hp.1
      positivity
    rcases (integral_nonneg_of_ae hnn).lt_or_eq with hlt | heq
    · exact hlt
    exfalso; apply hne
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hf).mp heq.symm
    filter_upwards [hz, ae_restrict_mem W7b_DysonGraviton_mH] with p hp hpH
    have hs : 0 < p.1 := hpH.1
    simp only [Pi.zero_apply] at hp ⊢
    have := (mul_eq_zero.mp hp).resolve_left hs.ne'
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  -- expansion of the integral in `ineq17`
  have hexp : (∫ p in halfPlane, p.1 ^ 3 * (dS f p.1 p.2 + f p.1 p.2 / p.1) ^ 2) =
      numQ f + (∫ p in halfPlane, p.1 ^ 2 * (2 * f p.1 p.2 * dS f p.1 p.2)) + denQ f := by
    unfold numQ denQ
    have e1 := integral_add (μ := (volume : Measure (ℝ × ℝ)).restrict halfPlane) (hdf.add hcI) hf
    have e2 := integral_add (μ := (volume : Measure (ℝ × ℝ)).restrict halfPlane) hdf hcI
    simp only [Pi.add_apply] at e1 e2
    rw [← e2, ← e1]
    apply setIntegral_congr_fun W7b_DysonGraviton_mH
    intro p hp
    have hs : p.1 ≠ 0 := (show 0 < p.1 from hp.1).ne'
    field_simp; ring
  -- the cross term equals `-2 denQ`
  have hcross : (∫ p in halfPlane, p.1 ^ 2 * (2 * f p.1 p.2 * dS f p.1 p.2)) = -2 * denQ f := by
    unfold denQ
    have hcI' := hcI
    have hf' := hf
    rw [IntegrableOn, W7b_DysonGraviton_restrict] at hcI' hf'
    rw [W7b_DysonGraviton_restrict, integral_prod_symm _ hcI', integral_prod_symm _ hf',
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hcI'.prod_left_ae, hf'.prod_left_ae] with z hz1 hz2
    exact W7b_DysonGraviton_ibp (fun s => f s z) (fun s => dS f s z)
      (fun s hs => (hdiff z s hs).hasDerivAt) hz2 hz1
  rw [hexp, hcross] at hpos
  unfold Q
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  linarith
