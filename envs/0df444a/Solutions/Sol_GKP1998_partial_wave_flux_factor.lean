-- Prove2me | solution 1 for GKP1998.partial_wave_flux_factor
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-02T19:56:29.365948+00:00
-- url     : https://prove2.me/submissions/8c4661c7-f944-45d8-849f-bd7f927ebbdf

import Mathlib
import Definitions.Def_GKP1998_Defs

set_option autoImplicit false

open Filter Topology Asymptotics MeasureTheory Set

namespace GKP1998Flux

/-- integrand of `J a y = ∫_{u>0} u^(a-1) exp(-u - y/u) du`. -/
noncomputable def g (a y u : ℝ) : ℝ := u ^ (a - 1) * Real.exp (-u - y / u)

noncomputable def J (a y : ℝ) : ℝ := ∫ u in Ioi (0 : ℝ), g a y u

lemma g_nonneg (a y : ℝ) {u : ℝ} (hu : 0 < u) : 0 ≤ g a y u := by
  unfold g; have := Real.rpow_nonneg hu.le (a - 1); positivity

lemma g_continuousOn (a y : ℝ) : ContinuousOn (g a y) (Ioi 0) := by
  intro u hu
  have hu' : u ≠ 0 := ne_of_gt hu
  apply ContinuousAt.continuousWithinAt
  unfold g
  exact (Real.continuousAt_rpow_const u (a - 1) (Or.inl hu')).mul
    ((continuousAt_id.neg.sub (continuousAt_const.div continuousAt_id hu')).rexp)

lemma exp_neg_div_le (n : ℕ) {y u : ℝ} (hy : 0 < y) (hu : 0 < u) :
    Real.exp (-y / u) ≤ (n.factorial : ℝ) / y ^ n * u ^ n := by
  have h1 := Real.pow_div_factorial_le_exp (y / u) (by positivity) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hp : 0 < (y / u) ^ n / (n.factorial : ℝ) := by positivity
  have h2 := inv_anti₀ hp h1
  rw [neg_div, Real.exp_neg]
  calc (Real.exp (y / u))⁻¹ ≤ ((y / u) ^ n / (n.factorial : ℝ))⁻¹ := h2
    _ = (n.factorial : ℝ) / y ^ n * u ^ n := by
        rw [div_pow]; field_simp

lemma g_integrable (a : ℝ) {y : ℝ} (hy : 0 < y) : IntegrableOn (g a y) (Ioi 0) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have hs : 0 < a + n := by linarith
  have hG := (Real.GammaIntegral_convergent hs).const_mul ((n.factorial : ℝ) / y ^ n)
  refine Integrable.mono' hG ((g_continuousOn a y).aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg a y hu)]
  unfold g
  have he : Real.exp (-u - y / u) = Real.exp (-u) * Real.exp (-y / u) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]
  have hr : u ^ (a + n - 1) = u ^ (a - 1) * u ^ n := by
    rw [show a + n - 1 = (a - 1) + (n : ℝ) by ring, Real.rpow_add hu, Real.rpow_natCast]
  rw [hr]
  have h1 := exp_neg_div_le n hy hu
  have h2 : 0 ≤ u ^ (a - 1) := Real.rpow_nonneg hu.le _
  have h3 := Real.exp_pos (-u)
  calc u ^ (a - 1) * (Real.exp (-u) * Real.exp (-y / u))
      ≤ u ^ (a - 1) * (Real.exp (-u) * ((n.factorial : ℝ) / y ^ n * u ^ n)) := by gcongr
    _ = (n.factorial : ℝ) / y ^ n * (Real.exp (-u) * (u ^ (a - 1) * u ^ n)) := by ring

lemma hasDerivAt_g (a u y : ℝ) (hu : 0 < u) :
    HasDerivAt (fun y => g a y u) (-g (a - 1) y u) y := by
  have h1 : HasDerivAt (fun y : ℝ => -u - y / u) (-(1 / u)) y := by
    have := ((hasDerivAt_id' y).div_const u).const_sub (-u)
    simpa [sub_eq_add_neg] using this
  have h2 := h1.exp.const_mul (u ^ (a - 1))
  refine h2.congr_deriv ?_
  unfold g
  have : u ^ (a - 1 - 1) = u ^ (a - 1) / u := by
    rw [Real.rpow_sub hu, Real.rpow_one]
  rw [this]; field_simp

lemma g_mono_y (a : ℝ) {y y' u : ℝ} (hu : 0 < u) (hyy : y' ≤ y) : g a y u ≤ g a y' u := by
  unfold g
  have h2 : 0 ≤ u ^ (a - 1) := Real.rpow_nonneg hu.le _
  gcongr

lemma J_hasDerivAt (a : ℝ) {y₀ : ℝ} (hy₀ : 0 < y₀) :
    HasDerivAt (J a) (-J (a - 1) y₀) y₀ := by
  have hs : Ioi (y₀ / 2) ∈ 𝓝 y₀ := Ioi_mem_nhds (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun y u => g a y u) (F' := fun y u => -g (a - 1) y u)
    (bound := fun u => g (a - 1) (y₀ / 2) u)
    hs (Eventually.of_forall (fun y =>
      (g_continuousOn a y).aestronglyMeasurable measurableSet_Ioi))
    (g_integrable a hy₀)
    ((g_continuousOn (a - 1) y₀).neg.aestronglyMeasurable measurableSet_Ioi) ?_
    (g_integrable (a - 1) (by linarith)) ?_
  · have h := key.2
    unfold J
    rw [integral_neg] at h
    exact h
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) y hy => ?_)
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (g_nonneg _ _ hu)]
    exact g_mono_y (a - 1) hu (le_of_lt hy)
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) y _ => ?_)
    exact hasDerivAt_g a u y hu

lemma J_tendsto_Gamma {a : ℝ} (ha : 0 < a) :
    Tendsto (J a) (𝓝[>] 0) (𝓝 (Real.Gamma a)) := by
  rw [Real.Gamma_eq_integral ha]
  have hfe : (fun u : ℝ => Real.exp (-u) * u ^ (a - 1)) = fun u => g a 0 u := by
    funext u; unfold g; rw [zero_div, sub_zero, mul_comm]
  rw [hfe]
  apply tendsto_integral_filter_of_dominated_convergence (fun u => g a 0 u)
  · exact Eventually.of_forall (fun y =>
      (g_continuousOn a y).aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg _ _ hu)]
    exact g_mono_y a hu hy.le
  · rw [← hfe]; exact Real.GammaIntegral_convergent ha
  · refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) => ?_)
    have hc : Continuous (fun y => g a y u) := by
      unfold g; fun_prop
    exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

lemma image_mul_exp {c : ℝ} (hc : 0 < c) :
    (fun t : ℝ => c * Real.exp t) '' univ = Ioi 0 := by
  ext u
  constructor
  · rintro ⟨t, -, rfl⟩
    exact mul_pos hc (Real.exp_pos t)
  · intro (hu : 0 < u)
    refine ⟨Real.log (u / c), trivial, ?_⟩
    simp only
    rw [Real.exp_log (div_pos hu hc)]
    field_simp

/-- the substituted integrand -/
noncomputable def ψ (ν c t : ℝ) : ℝ :=
  c ^ ν * (Real.exp (ν * t) * Real.exp (-(2 * c) * Real.cosh t))

lemma psi_eq (ν : ℝ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    |c * Real.exp t| • g ν (c ^ 2) (c * Real.exp t) = ψ ν c t := by
  have he := Real.exp_pos t
  have hce : 0 < c * Real.exp t := mul_pos hc he
  rw [smul_eq_mul, abs_of_pos hce]
  unfold g ψ
  have h1 : (c * Real.exp t) ^ (ν - 1) = (c * Real.exp t) ^ ν / (c * Real.exp t) := by
    rw [Real.rpow_sub_one hce.ne']
  have h2 : (c * Real.exp t) ^ ν = c ^ ν * Real.exp (ν * t) := by
    rw [Real.mul_rpow hc.le he.le, ← Real.exp_mul, mul_comm t ν]
  have h3 : -(c * Real.exp t) - c ^ 2 / (c * Real.exp t) = -(2 * c) * Real.cosh t := by
    rw [Real.cosh_eq, Real.exp_neg]
    field_simp
    ring
  rw [h1, h2, h3]
  field_simp

lemma J_sq_eq (ν : ℝ) {c : ℝ} (hc : 0 < c) :
    J ν (c ^ 2) = 2 * c ^ ν * GKP1998.besselK ν (2 * c) := by
  have hd : ∀ t ∈ (univ : Set ℝ), HasDerivWithinAt (fun t : ℝ => c * Real.exp t)
      (c * Real.exp t) univ t := fun t _ => ((Real.hasDerivAt_exp t).const_mul c).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => c * Real.exp t) univ := by
    intro a _ b _ hab
    exact Real.exp_injective (mul_left_cancel₀ hc.ne' hab)
  have hI := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj (g ν (c ^ 2))
  have hint := (integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj
    (g ν (c ^ 2))).1
  rw [image_mul_exp hc] at hI hint
  have hint' := hint (g_integrable ν (by positivity))
  simp_rw [psi_eq ν hc] at hI hint'
  have hψ : Integrable (ψ ν c) := by
    rw [← integrableOn_univ]; exact hint'
  unfold J
  rw [hI]
  rw [← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hψ.integrableOn hψ.integrableOn]
  have hneg := integral_comp_neg_Ioi (0 : ℝ) (ψ ν c)
  rw [neg_zero] at hneg
  rw [← hneg]
  have hψn : IntegrableOn (fun t => ψ ν c (-t)) (Ioi 0) := hψ.comp_neg.integrableOn
  rw [← integral_add hψn hψ.integrableOn]
  unfold GKP1998.besselK
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
  simp only [ψ, Real.cosh_eq]
  rw [show ν * -t = -(ν * t) by ring, show -(2 * c) * ((Real.exp t + Real.exp (-t)) / 2)
    = -(2 * c) * ((Real.exp t + Real.exp (-t)) / 2) from rfl]
  ring_nf

lemma besselK_neg (a x : ℝ) : GKP1998.besselK (-a) x = GKP1998.besselK a x := by
  unfold GKP1998.besselK
  congr 1; funext t; rw [neg_mul a t, Real.cosh_neg]

lemma J_symm (a : ℝ) {y : ℝ} (hy : 0 < y) : J a y = y ^ a * J (-a) y := by
  have hc : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hsq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy.le
  have h1 := J_sq_eq a hc
  have h2 := J_sq_eq (-a) hc
  rw [hsq] at h1 h2
  rw [h1, h2, besselK_neg]
  have : y ^ a = Real.sqrt y ^ a * Real.sqrt y ^ a := by
    rw [← Real.mul_rpow hc.le hc.le, Real.mul_self_sqrt hy.le]
  rw [this, Real.rpow_neg hc.le]
  have : 0 < Real.sqrt y ^ a := Real.rpow_pos_of_pos hc a
  field_simp

lemma nonpos_of_deriv_nonpos {φ φ' : ℝ → ℝ} {δ : ℝ}
    (hd : ∀ y ∈ Ioo 0 δ, HasDerivAt φ (φ' y) y) (hneg : ∀ y ∈ Ioo 0 δ, φ' y ≤ 0)
    (hlim : Tendsto φ (𝓝[>] 0) (𝓝 0)) : ∀ y ∈ Ioo 0 δ, φ y ≤ 0 := by
  have hA : AntitoneOn φ (Ioo 0 δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ)
    · exact fun y hy => (hd y hy).continuousAt.continuousWithinAt
    · rw [interior_Ioo]; exact fun y hy => (hd y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]; intro y hy; rw [(hd y hy).deriv]; exact hneg y hy
  intro y hy
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT hy.1] with s hs
  exact hA ⟨hs.1, hs.2.trans hy.2⟩ hy hs.2.le

lemma tendsto_rpow_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => t ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma littleO_of_deriv {h e : ℝ → ℝ} {μ : ℝ} (hμ : -1 < μ)
    (hd : ∀ y > 0, HasDerivAt h (e y) y)
    (he : e =o[𝓝[>] (0:ℝ)] (fun y => y ^ μ))
    (hlim : Tendsto h (𝓝[>] 0) (𝓝 0)) :
    h =o[𝓝[>] (0:ℝ)] (fun y => y ^ (μ + 1)) := by
  have hμ1 : 0 < μ + 1 := by linarith
  rw [isLittleO_iff]
  intro c hc
  have hc' : 0 < c * (μ + 1) := mul_pos hc hμ1
  have h1 := (isLittleO_iff.1 he) hc'
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h1
  have hδ' : (0:ℝ) < δ := hδ
  have hpow : ∀ y > (0:ℝ), HasDerivAt (fun t : ℝ => t ^ (μ + 1)) ((μ + 1) * y ^ μ) y := by
    intro y hy
    have := Real.hasDerivAt_rpow_const (x := y) (p := μ + 1) (Or.inl hy.ne')
    rwa [add_sub_cancel_right] at this
  have hbd : ∀ y ∈ Ioo 0 δ, |e y| ≤ c * (μ + 1) * y ^ μ := by
    intro y hy
    have := hsub hy
    simp only [Set.mem_ofPred_eq, Real.norm_eq_abs] at this
    rwa [abs_of_pos (Real.rpow_pos_of_pos hy.1 μ)] at this
  have hT := tendsto_rpow_zero hμ1
  have hplus := nonpos_of_deriv_nonpos (φ := fun t => h t - c * t ^ (μ + 1))
    (φ' := fun y => e y - c * ((μ + 1) * y ^ μ))
    (fun y hy => (hd y hy.1).sub ((hpow y hy.1).const_mul c))
    (fun y hy => by have := hbd y hy; have := le_abs_self (e y); nlinarith)
    (by simpa using hlim.sub (hT.const_mul c))
  have hminus := nonpos_of_deriv_nonpos (φ := fun t => -h t - c * t ^ (μ + 1))
    (φ' := fun y => -e y - c * ((μ + 1) * y ^ μ))
    (fun y hy => (hd y hy.1).neg.sub ((hpow y hy.1).const_mul c))
    (fun y hy => by have := hbd y hy; have := neg_abs_le (e y); nlinarith)
    (by simpa using hlim.neg.sub (hT.const_mul c))
  filter_upwards [Ioo_mem_nhdsGT hδ'] with y hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hy.1 _)]
  have a1 : h y - c * y ^ (μ + 1) ≤ 0 := hplus y hy
  have a2 : -h y - c * y ^ (μ + 1) ≤ 0 := hminus y hy
  exact abs_le.2 ⟨by linarith, by linarith⟩

lemma g_pos (a y : ℝ) {u : ℝ} (hu : 0 < u) : 0 < g a y u := by
  unfold g; have := Real.rpow_pos_of_pos hu (a - 1); positivity

lemma J_pos (a : ℝ) {y : ℝ} (hy : 0 < y) : 0 < J a y := by
  unfold J
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun u (hu : 0 < u) => (g_nonneg a y hu)))
    (g_integrable a hy)]
  have : Function.support (g a y) ∩ Ioi 0 = Ioi 0 :=
    inter_eq_right.2 (fun u (hu : 0 < u) => Function.mem_support.2 (g_pos a y hu).ne')
  rw [this, Real.volume_Ioi]
  simp

lemma besselK_eq (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    GKP1998.besselK ν x = (1 / 2) * (x / 2) ^ (-ν) * J ν ((x / 2) ^ 2) := by
  have hc : 0 < x / 2 := by positivity
  rw [J_sq_eq ν hc, show 2 * (x / 2) = x by ring, Real.rpow_neg hc.le]
  have : 0 < (x / 2) ^ ν := Real.rpow_pos_of_pos hc ν
  field_simp

lemma besselK_pos (ν : ℝ) {x : ℝ} (hx : 0 < x) : 0 < GKP1998.besselK ν x := by
  rw [besselK_eq ν hx]
  have := J_pos ν (show 0 < (x / 2) ^ 2 by positivity)
  have := Real.rpow_pos_of_pos (show 0 < x / 2 by positivity) (-ν)
  positivity

lemma fluxFactor_eq (ν : ℝ) {k R : ℝ} (hk : 0 < k) (hR : 0 < R) :
    GKP1998.fluxFactor ν k R = (2 - ν - 2 * (k * R / 2) ^ 2 * J (ν - 1) ((k * R / 2) ^ 2)
      / J ν ((k * R / 2) ^ 2)) / R ^ 4 := by
  have hc : 0 < k * R / 2 := by positivity
  set D := R ^ 2 * GKP1998.besselK ν (k * R) with hD
  have hDpos : 0 < D := by have := besselK_pos ν (mul_pos hk hR); positivity
  set q : ℝ → ℝ := fun z => z ^ 2 * ((1 / 2) * (k * z / 2) ^ (-ν) * J ν ((k * z / 2) ^ 2)) / D
    with hq
  have hev : (fun z => Real.log (GKP1998.radialProfile ν k R z)) =ᶠ[𝓝 R]
      (fun z => Real.log (q z)) := by
    filter_upwards [Ioi_mem_nhds hR] with z (hz : 0 < z)
    simp only [GKP1998.radialProfile, hq, ← hD]
    rw [besselK_eq ν (mul_pos hk hz)]
  have hz1 : HasDerivAt (fun z : ℝ => k * z / 2) (k / 2) R := by
    simpa using ((hasDerivAt_id' R).const_mul k).div_const 2
  have hpow := (Real.hasDerivAt_rpow_const (x := k * R / 2) (p := -ν) (Or.inl hc.ne')).comp R hz1
  have hJ := (J_hasDerivAt ν (show 0 < (k * R / 2) ^ 2 by positivity)).comp R (hz1.pow 2)
  have hqd := ((((hasDerivAt_id' R).pow 2).mul ((hpow.const_mul (1 / 2)).mul hJ)).div_const D)
  have hqR : q R ≠ 0 := by
    simp only [hq]
    have := J_pos ν (show 0 < (k * R / 2) ^ 2 by positivity)
    have := Real.rpow_pos_of_pos hc (-ν)
    positivity
  have hlog := (hqd.log hqR).congr_of_eventuallyEq hev
  unfold GKP1998.fluxFactor
  rw [hlog.deriv]
  simp only [Function.comp_apply, Pi.pow_apply, Pi.mul_apply]
  have hJ0 := J_pos ν (show 0 < (k * R / 2) ^ 2 by positivity)
  have hw := Real.rpow_pos_of_pos hc (-ν)
  rw [Real.rpow_sub_one hc.ne']
  set J0 := J ν ((k * R / 2) ^ 2) with hJ0d
  set J1 := J (ν - 1) ((k * R / 2) ^ 2) with hJ1d
  set w := (k * R / 2) ^ (-ν) with hwd
  field_simp
  ring

/-! ### integer orders: logarithmic small-`y` asymptotics -/

lemma J_le_Gamma {a : ℝ} (ha : 0 < a) {y : ℝ} (hy : 0 < y) : J a y ≤ Real.Gamma a := by
  rw [Real.Gamma_eq_integral ha]
  have hfe : (fun u : ℝ => Real.exp (-u) * u ^ (a - 1)) = fun u => g a 0 u := by
    funext u; unfold g; rw [zero_div, sub_zero, mul_comm]
  rw [hfe]
  unfold J
  refine setIntegral_mono_on (g_integrable a hy) ?_ measurableSet_Ioi
    (fun u (hu : 0 < u) => g_mono_y a hu hy.le)
  have := Real.GammaIntegral_convergent ha
  rw [hfe] at this; exact this

lemma J_zero_le {y : ℝ} (hy : 0 < y) :
    J 0 y ≤ Real.Gamma (1 / 4) * (y ^ (-(1 / 4 : ℝ)) + 1) := by
  have hpt : ∀ u ∈ Ioi (0:ℝ), g 0 y u ≤ (fun u => g (-(1 / 4)) y u + g (1 / 4) y u) u := by
    intro u (hu : 0 < u)
    simp only
    unfold g
    have he := Real.exp_pos (-u - y / u)
    have key : u ^ ((0:ℝ) - 1) ≤ u ^ (-(1 / 4 : ℝ) - 1) + u ^ ((1 / 4 : ℝ) - 1) := by
      have h1 := Real.rpow_pos_of_pos hu (-(1 / 4 : ℝ) - 1)
      have h2 := Real.rpow_pos_of_pos hu ((1 / 4 : ℝ) - 1)
      rcases le_total u 1 with hu1 | hu1
      · have : u ^ ((0:ℝ) - 1) ≤ u ^ (-(1 / 4 : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_ge hu hu1 (by norm_num)
        linarith
      · have : u ^ ((0:ℝ) - 1) ≤ u ^ ((1 / 4 : ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
        linarith
    nlinarith
  have hint := setIntegral_mono_on (g_integrable 0 hy)
    ((g_integrable (-(1 / 4)) hy).add (g_integrable (1 / 4) hy)) measurableSet_Ioi hpt
  have hsum : ∫ x in Ioi (0:ℝ), (g (-(1 / 4)) y + g (1 / 4) y) x = J (-(1 / 4)) y + J (1 / 4) y := by
    unfold J; exact integral_add (g_integrable _ hy) (g_integrable _ hy)
  rw [hsum] at hint
  have hs : J (-(1 / 4)) y = y ^ (-(1 / 4 : ℝ)) * J (1 / 4) y := by
    rw [J_symm (-(1 / 4)) hy, neg_neg]
  have hG := J_le_Gamma (show (0:ℝ) < 1 / 4 by norm_num) hy
  have hp := Real.rpow_pos_of_pos hy (-(1 / 4 : ℝ))
  change J 0 y ≤ J (-(1 / 4)) y + J (1 / 4) y at hint
  rw [hs] at hint
  nlinarith

lemma J_one_sub :
    (fun y => J 1 y - 1) =o[𝓝[>] (0:ℝ)] (fun y => y ^ ((-(1 / 2) : ℝ) + 1)) := by
  apply littleO_of_deriv (μ := -(1 / 2)) (by norm_num) (e := fun y => -J 0 y)
  · intro y hy
    have := (J_hasDerivAt 1 hy).sub_const 1
    rwa [sub_self] at this
  · rw [isLittleO_iff]
    intro ε hε
    have hT : Tendsto (fun y : ℝ => Real.Gamma (1 / 4) * (y ^ (1 / 4 : ℝ) + y ^ (1 / 2 : ℝ)))
        (𝓝[>] 0) (𝓝 0) := by
      have := ((tendsto_rpow_zero (show (0:ℝ) < 1 / 4 by norm_num)).add
        (tendsto_rpow_zero (show (0:ℝ) < 1 / 2 by norm_num))).const_mul (Real.Gamma (1 / 4))
      simpa using this
    filter_upwards [hT.eventually (gt_mem_nhds hε), self_mem_nhdsWithin] with y hy1 (hy : 0 < y)
    have hJ0 := J_pos 0 hy
    have hb := J_zero_le hy
    rw [norm_neg, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hJ0,
      abs_of_pos (Real.rpow_pos_of_pos hy _)]
    have e1 : y ^ (-(1 / 4 : ℝ)) = y ^ (-(1 / 2) : ℝ) * y ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hy]; norm_num
    have e2 : (1:ℝ) = y ^ (-(1 / 2) : ℝ) * y ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hy]; norm_num
    have hp := Real.rpow_pos_of_pos hy (-(1 / 2) : ℝ)
    calc J 0 y ≤ Real.Gamma (1 / 4) * (y ^ (-(1 / 4 : ℝ)) + 1) := hb
      _ = y ^ (-(1 / 2) : ℝ) * (Real.Gamma (1 / 4) * (y ^ (1 / 4 : ℝ) + y ^ (1 / 2 : ℝ))) := by
          rw [e1]; linear_combination Real.Gamma (1 / 4) * e2
      _ ≤ y ^ (-(1 / 2) : ℝ) * ε := mul_le_mul_of_nonneg_left hy1.le hp.le
      _ = ε * y ^ (-(1 / 2) : ℝ) := by ring
  · have := J_tendsto_Gamma (show (0:ℝ) < 1 by norm_num)
    rw [Real.Gamma_one] at this
    have := this.sub_const 1
    rwa [sub_self] at this

lemma J_zero_log_tendsto :
    ∃ L : ℝ, Tendsto (fun y => J 0 y + Real.log y) (𝓝[>] 0) (𝓝 L) := by
  set F : ℝ → ℝ := fun y => J 0 y + Real.log y with hF
  have hd : ∀ y > (0:ℝ), HasDerivAt F ((1 - J 1 y) / y) y := by
    intro y hy
    have h1 := J_hasDerivAt 0 hy
    have h2 := Real.hasDerivAt_log hy.ne'
    refine (h1.add h2).congr_deriv ?_
    rw [show (0:ℝ) - 1 = -1 by norm_num, J_symm (-1) hy, neg_neg, Real.rpow_neg_one]
    field_simp
    ring
  have hd0 : ∀ y > (0:ℝ), 0 ≤ (1 - J 1 y) / y := by
    intro y hy
    have := J_le_Gamma (show (0:ℝ) < 1 by norm_num) hy
    rw [Real.Gamma_one] at this
    exact div_nonneg (by linarith) hy.le
  have hO := (isLittleO_iff.1 J_one_sub) (show (0:ℝ) < 1 by norm_num)
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hO
  have hδ' : (0:ℝ) < δ := hδ
  have hbd : ∀ y ∈ Ioo 0 δ, (1 - J 1 y) / y ≤ y ^ (-(1 / 2) : ℝ) := by
    intro y hy
    have h := hsub hy
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs, one_mul] at h
    rw [abs_of_pos (Real.rpow_pos_of_pos hy.1 _)] at h
    have h' : 1 - J 1 y ≤ y ^ ((-(1 / 2) : ℝ) + 1) := by linarith [neg_abs_le (J 1 y - 1)]
    rw [Real.rpow_add hy.1, Real.rpow_one] at h'
    rw [div_le_iff₀ hy.1]; exact h'
  have hsq : ∀ y > (0:ℝ), HasDerivAt (fun t : ℝ => 2 * t ^ (1 / 2 : ℝ)) (y ^ (-(1 / 2) : ℝ)) y := by
    intro y hy
    have := (Real.hasDerivAt_rpow_const (x := y) (p := 1 / 2) (Or.inl hy.ne')).const_mul 2
    refine this.congr_deriv ?_
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num]; ring
  have hG : ∀ y > (0:ℝ), HasDerivAt (fun t => F t - 2 * t ^ (1 / 2 : ℝ))
      ((1 - J 1 y) / y - y ^ (-(1 / 2) : ℝ)) y := fun y hy => (hd y hy).sub (hsq y hy)
  have hA : AntitoneOn (fun t => F t - 2 * t ^ (1 / 2 : ℝ)) (Ioo 0 δ) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 δ)
    · exact fun y hy => (hG y hy.1).continuousAt.continuousWithinAt
    · rw [interior_Ioo]
      exact fun y hy => (hG y hy.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]; intro y hy
      rw [(hG y hy.1).deriv]; linarith [hbd y hy]
  have hM : MonotoneOn F (Ioo 0 δ) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 δ)
    · exact fun y hy => (hd y hy.1).continuousAt.continuousWithinAt
    · rw [interior_Ioo]; exact fun y hy => (hd y hy.1).differentiableAt.differentiableWithinAt
    · rw [interior_Ioo]; intro y hy; rw [(hd y hy.1).deriv]; exact hd0 y hy.1
  have hm : δ / 2 ∈ Ioo 0 δ := ⟨by linarith, by linarith⟩
  have hbdd : BddBelow (F '' Ioo 0 δ) := by
    refine ⟨min (F (δ / 2) - 2 * (δ / 2) ^ (1 / 2 : ℝ)) (F (δ / 2)), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    rcases le_total y (δ / 2) with h | h
    · have h1 := hA hy hm h
      have h2 := Real.rpow_nonneg hy.1.le (1 / 2 : ℝ)
      simp only at h1
      exact min_le_of_left_le (by linarith)
    · exact min_le_of_right_le (hM hm hy h)
  exact ⟨_, hM.tendsto_nhdsWithin_Ioo_right ⟨δ / 2, hm⟩ hbdd⟩

/-- polynomial with coefficients `a`, degree `< n`. -/
noncomputable def S (a : ℕ → ℝ) (n : ℕ) (y : ℝ) : ℝ := ∑ j ∈ Finset.range n, a j * y ^ j

lemma S_analytic (a : ℕ → ℝ) (n : ℕ) : AnalyticAt ℝ (S a n) 0 := by
  induction n with
  | zero =>
    have : S a 0 = fun _ => 0 := by funext y; simp [S]
    rw [this]; exact analyticAt_const
  | succ n ih =>
    have : S a (n + 1) = fun y => S a n y + a n * y ^ n := by
      funext y; simp [S, Finset.sum_range_succ]
    rw [this]; exact ih.add (by fun_prop)

lemma S_zero_at (a : ℕ → ℝ) (n : ℕ) : S a (n + 1) 0 = a 0 := by
  simp [S, Finset.sum_range_succ']

/-- coefficients of `C - ∫₀^y (Σ a_j t^j) dt`. -/
noncomputable def shiftC (a : ℕ → ℝ) (C : ℝ) : ℕ → ℝ
  | 0 => C
  | j + 1 => -a j / ((j : ℝ) + 1)

lemma S_shift_hasDerivAt (a : ℕ → ℝ) (C : ℝ) (n : ℕ) (y : ℝ) :
    HasDerivAt (S (shiftC a C) (n + 1)) (-S a n y) y := by
  have hfun : S (shiftC a C) (n + 1) =
      fun y => C + ∑ j ∈ Finset.range n, (-a j / ((j:ℝ) + 1)) * y ^ (j + 1) := by
    funext y
    simp only [S]
    rw [Finset.sum_range_succ', add_comm]
    simp [shiftC]
  rw [hfun]
  have hs : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range n, (-a j / ((j:ℝ) + 1)) * y ^ (j + 1))
      (∑ j ∈ Finset.range n, -(a j * y ^ j)) y := by
    apply HasDerivAt.fun_sum
    intro j _
    have h1 := (hasDerivAt_pow (j + 1) y).const_mul (-a j / ((j:ℝ) + 1))
    refine h1.congr_deriv ?_
    have : (j:ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
  refine (hs.const_add C).congr_deriv ?_
  simp [S, Finset.sum_neg_distrib]

noncomputable def cL (n : ℕ) : ℝ := (-1) ^ (n + 1) / (n.factorial : ℝ)

noncomputable def Hn : ℕ → ℝ
  | 0 => 0
  | n + 1 => Hn n + 1 / ((n : ℝ) + 1)

/-- `J_n(y) = poly + cL n · y^n (log y - H_n) + o(y^n)`. -/
def LAsy (n : ℕ) : Prop :=
  ∃ a : ℕ → ℝ, (fun y => J n y - S a (n + 1) y - cL n * (y ^ n * (Real.log y - Hn n)))
    =o[𝓝[>] (0:ℝ)] (fun y => y ^ n)

lemma cL_succ (n : ℕ) : cL (n + 1) * ((n : ℝ) + 1) = -cL n := by
  unfold cL
  rw [Nat.factorial_succ]; push_cast
  have : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp
  ring

lemma tendsto_pow_log {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun y : ℝ => y ^ m * Real.log y) (𝓝[>] 0) (𝓝 0) := by
  have := tendsto_log_mul_rpow_nhdsGT_zero (r := (m:ℝ)) (by exact_mod_cast hm)
  refine this.congr' (Eventually.of_forall (fun y => ?_))
  simp only [Real.rpow_natCast]; ring

lemma tendsto_pow_zero {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun y : ℝ => y ^ m) (𝓝[>] 0) (𝓝 0) := by
  have := ((continuous_pow m).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
  simpa [zero_pow (by omega : m ≠ 0)] using this

lemma lasy_base : LAsy 0 := by
  obtain ⟨L, hL⟩ := J_zero_log_tendsto
  refine ⟨fun _ => L, ?_⟩
  have h : Tendsto (fun y => J ((0:ℕ):ℝ) y - S (fun _ => L) (0 + 1) y
      - cL 0 * (y ^ 0 * (Real.log y - Hn 0))) (𝓝[>] 0) (𝓝 0) := by
    have := hL.sub_const L
    rw [sub_self] at this
    refine this.congr (fun y => ?_)
    simp [S, cL, Hn]
    ring
  exact ((isLittleO_one_iff ℝ).2 h).congr' EventuallyEq.rfl
    (Eventually.of_forall (fun y => by simp))

lemma lasy_step {n : ℕ} (h : LAsy n) : LAsy (n + 1) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨shiftC a (Real.Gamma ((n:ℝ) + 1)), ?_⟩
  have key := littleO_of_deriv (μ := (n:ℝ))
    (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
    (h := fun y => J ((n + 1 : ℕ) : ℝ) y - S (shiftC a (Real.Gamma ((n:ℝ) + 1))) (n + 1 + 1) y
      - cL (n + 1) * (y ^ (n + 1) * (Real.log y - Hn (n + 1))))
    (e := fun y => -(J n y - S a (n + 1) y - cL n * (y ^ n * (Real.log y - Hn n)))) ?_ ?_ ?_
  · have e : (fun y : ℝ => y ^ ((n:ℝ) + 1)) = fun y => y ^ (n + 1) := by
      funext y; rw [← Real.rpow_natCast]; push_cast; rfl
    rw [e] at key
    exact key
  · intro y hy
    have h1 := J_hasDerivAt ((n + 1 : ℕ) : ℝ) hy
    rw [show ((n + 1 : ℕ) : ℝ) - 1 = n by push_cast; ring] at h1
    have h2 := S_shift_hasDerivAt a (Real.Gamma ((n:ℝ) + 1)) (n + 1) y
    have h3 : HasDerivAt (fun y : ℝ => y ^ (n + 1) * (Real.log y - Hn (n + 1)))
        (((n + 1 : ℕ) : ℝ) * y ^ n * (Real.log y - Hn (n + 1)) + y ^ (n + 1) * y⁻¹) y := by
      refine ((hasDerivAt_pow (n + 1) y).mul
        ((Real.hasDerivAt_log hy.ne').sub_const (Hn (n + 1)))).congr_deriv ?_
      simp
    refine ((h1.sub h2).sub (h3.const_mul (cL (n + 1)))).congr_deriv ?_
    have hc := cL_succ n
    have hy1 : y ^ (n + 1) * y⁻¹ = y ^ n := by rw [pow_succ]; field_simp
    have hH : ((n:ℝ) + 1) * Hn (n + 1) = ((n:ℝ) + 1) * Hn n + 1 := by
      simp only [Hn]; field_simp
    rw [hy1]
    push_cast
    linear_combination (-(y ^ n * Real.log y) + y ^ n * Hn n) * hc + cL (n + 1) * y ^ n * hH
  · exact ha.neg_left.congr' EventuallyEq.rfl
      (Eventually.of_forall (fun y => by simp [Real.rpow_natCast]))
  · have h1 : Tendsto (J ((n + 1 : ℕ) : ℝ)) (𝓝[>] 0) (𝓝 (Real.Gamma ((n:ℝ) + 1))) := by
      simpa using J_tendsto_Gamma (show (0:ℝ) < ((n + 1 : ℕ) : ℝ) by positivity)
    have h2 : Tendsto (S (shiftC a (Real.Gamma ((n:ℝ) + 1))) (n + 1 + 1)) (𝓝[>] 0)
        (𝓝 (Real.Gamma ((n:ℝ) + 1))) := by
      have := (S_analytic (shiftC a (Real.Gamma ((n:ℝ) + 1))) (n + 1 + 1)).continuousAt.tendsto
      rw [S_zero_at] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 : Tendsto (fun y : ℝ => y ^ (n + 1) * (Real.log y - Hn (n + 1))) (𝓝[>] 0) (𝓝 0) := by
      have t1 := tendsto_pow_log (m := n + 1) (by omega)
      have t2 := tendsto_pow_zero (m := n + 1) (by omega)
      have := t1.sub (t2.mul_const (Hn (n + 1)))
      rw [zero_mul, sub_zero] at this
      exact this.congr (fun y => by ring)
    have := (h1.sub h2).sub (h3.const_mul (cL (n + 1)))
    rw [sub_self, mul_zero, sub_zero] at this
    exact this

lemma lasy_all (n : ℕ) : LAsy n := by
  induction n with
  | zero => exact lasy_base
  | succ n ih => exact lasy_step ih

/-! ### the ratio `y J_{m}/J_{m+1}` -/

lemma key_log {J1 J2 Q1 Q2 : ℝ → ℝ} {m : ℕ} {c q d : ℝ} (hm : 1 ≤ m) (hq : q ≠ 0)
    (h1 : (fun y => J1 y - Q1 y - c * (y ^ m * Real.log y)) =o[𝓝[>] (0:ℝ)] (fun y => y ^ m))
    (h2 : (fun y => J2 y - Q2 y) =o[𝓝[>] (0:ℝ)] (fun y => y ^ m))
    (hQ1 : ContinuousAt Q1 0) (hQ2 : HasDerivAt Q2 d 0) (hQ20 : Q2 0 = q) :
    (fun y => y * J1 y / J2 y - y * Q1 y / Q2 y - c / q * (y ^ (m + 1) * Real.log y))
      =o[𝓝[>] (0:ℝ)] (fun y => y ^ (m + 1)) := by
  have hQ2lim : Tendsto Q2 (𝓝[>] 0) (𝓝 q) := by
    rw [← hQ20]; exact hQ2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hE2 : Tendsto (fun y => J2 y - Q2 y) (𝓝[>] 0) (𝓝 0) := h2.trans_tendsto (tendsto_pow_zero hm)
  have hJ2lim : Tendsto J2 (𝓝[>] 0) (𝓝 q) := by
    have := hE2.add hQ2lim
    rw [zero_add] at this
    exact this.congr (fun y => by ring)
  have hJ2ne : ∀ᶠ y in 𝓝[>] (0:ℝ), J2 y ≠ 0 := hJ2lim.eventually_ne hq
  have hQ2ne : ∀ᶠ y in 𝓝[>] (0:ℝ), Q2 y ≠ 0 := hQ2lim.eventually_ne hq
  -- term 1
  have hinvJ : (fun y => (J2 y)⁻¹) =O[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) :=
    (hJ2lim.inv₀ hq).isBigO_one ℝ
  have T1 := ((isBigO_refl (fun y : ℝ => y) (𝓝[>] (0:ℝ))).mul_isLittleO h1).mul_isBigO hinvJ
  -- term 2
  have hlogE : Tendsto (fun y => Real.log y * (J2 y - q)) (𝓝[>] 0) (𝓝 0) := by
    have hA : (fun y => Real.log y * (Q2 y - Q2 0)) =O[𝓝[>] (0:ℝ)] (fun y => Real.log y * y) := by
      have := (hQ2.isBigO_sub).mono (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
      simpa using (isBigO_refl Real.log (𝓝[>] (0:ℝ))).mul this
    have hA' : Tendsto (fun y => Real.log y * y) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_pow_log (m := 1) le_rfl).congr (fun y => by ring)
    have hB : (fun y => Real.log y * (J2 y - Q2 y)) =O[𝓝[>] (0:ℝ)]
        (fun y => Real.log y * y ^ m) :=
      (isBigO_refl Real.log (𝓝[>] (0:ℝ))).mul h2.isBigO
    have hB' : Tendsto (fun y => Real.log y * y ^ m) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_pow_log hm).congr (fun y => by ring)
    have := (hA.trans_tendsto hA').add (hB.trans_tendsto hB')
    rw [add_zero] at this
    refine this.congr (fun y => ?_)
    rw [hQ20]; ring
  have hb : Tendsto (fun y => -(c / q) * (Real.log y * (J2 y - q)) * (J2 y)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    have := (hlogE.const_mul (-(c / q))).mul (hJ2lim.inv₀ hq)
    rwa [mul_zero, zero_mul] at this
  have T2 := (isBigO_refl (fun y : ℝ => y ^ (m + 1)) (𝓝[>] (0:ℝ))).mul_isLittleO
    ((isLittleO_one_iff ℝ).2 hb)
  -- term 3
  have hbound : (fun y => Q1 y * (J2 y * Q2 y)⁻¹) =O[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) :=
    ((hQ1.tendsto.mono_left nhdsWithin_le_nhds).mul
      ((hJ2lim.mul hQ2lim).inv₀ (mul_ne_zero hq hq))).isBigO_one ℝ
  have T3 := ((isBigO_refl (fun y : ℝ => y) (𝓝[>] (0:ℝ))).mul_isLittleO h2).mul_isBigO hbound
  have T1' := T1.congr' EventuallyEq.rfl
    (Eventually.of_forall (fun y => (by ring : y * y ^ m * 1 = y ^ (m + 1))))
  have T2' := T2.congr' EventuallyEq.rfl
    (Eventually.of_forall (fun y => (by ring : y ^ (m + 1) * 1 = y ^ (m + 1))))
  have T3' := T3.congr' EventuallyEq.rfl
    (Eventually.of_forall (fun y => (by ring : y * y ^ m * 1 = y ^ (m + 1))))
  refine ((T1'.add T2').sub T3').congr' ?_ EventuallyEq.rfl
  filter_upwards [hJ2ne, hQ2ne] with y hJ hQ
  field_simp
  ring

/-! ### assembly -/

theorem main_result (l : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => GKP1998.fluxFactor ((l : ℝ) + 2) k R - A (k ^ 2)
          - (-(-1 : ℝ) ^ l / (2 ^ (2 * l + 2) * ((l + 1).factorial : ℝ) ^ 2))
              * k ^ (2 * l + 4) * R ^ (2 * l) * Real.log (k * R))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * l + 4)) := by
  obtain ⟨a1, h1⟩ := lasy_all (l + 1)
  obtain ⟨a2, h2⟩ := lasy_all (l + 2)
  set c := cL (l + 1) with hc
  set q := ((l + 1).factorial : ℝ) with hq
  have hqpos : 0 < q := Nat.cast_pos.2 (Nat.factorial_pos _)
  set Q1 : ℝ → ℝ := fun y => S a1 (l + 1 + 1) y - c * Hn (l + 1) * y ^ (l + 1) with hQ1
  set Q2 : ℝ → ℝ := S a2 (l + 2 + 1) with hQ2
  have h1' : (fun y => J ((l + 1 : ℕ) : ℝ) y - Q1 y - c * (y ^ (l + 1) * Real.log y))
      =o[𝓝[>] (0:ℝ)] (fun y => y ^ (l + 1)) :=
    h1.congr' (Eventually.of_forall (fun y => by simp only [hQ1]; ring)) EventuallyEq.rfl
  have h2' : (fun y => J ((l + 2 : ℕ) : ℝ) y - Q2 y) =o[𝓝[>] (0:ℝ)] (fun y => y ^ (l + 1)) := by
    have hlog : (fun y : ℝ => cL (l + 2) * (y ^ (l + 2) * (Real.log y - Hn (l + 2))))
        =o[𝓝[>] (0:ℝ)] (fun y => y ^ (l + 1)) := by
      have hb : Tendsto (fun y : ℝ => cL (l + 2) * (y ^ 1 * Real.log y - y * Hn (l + 2)))
          (𝓝[>] 0) (𝓝 0) := by
        have t2 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        have := ((tendsto_pow_log (m := 1) le_rfl).sub (t2.mul_const (Hn (l + 2)))).const_mul
          (cL (l + 2))
        rwa [zero_mul, sub_zero, mul_zero] at this
      have := (isBigO_refl (fun y : ℝ => y ^ (l + 1)) (𝓝[>] (0:ℝ))).mul_isLittleO
        ((isLittleO_one_iff ℝ).2 hb)
      exact this.congr' (Eventually.of_forall (fun y => by ring))
        (Eventually.of_forall (fun y => by ring))
    have hO2 : (fun y : ℝ => y ^ (l + 2)) =O[𝓝[>] (0:ℝ)] (fun y => y ^ (l + 1)) := by
      have t2 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
      have := (isBigO_refl (fun y : ℝ => y ^ (l + 1)) (𝓝[>] (0:ℝ))).mul (t2.isBigO_one ℝ)
      exact this.congr' (Eventually.of_forall (fun y => by ring))
        (Eventually.of_forall (fun y => by ring))
    have := (h2.trans_isBigO hO2).add hlog
    exact this.congr' (Eventually.of_forall (fun y => by simp only [hQ2]; ring)) EventuallyEq.rfl
  have hQ1an : AnalyticAt ℝ Q1 0 := (S_analytic a1 (l + 1 + 1)).sub (by fun_prop)
  have hQ2an : AnalyticAt ℝ Q2 0 := S_analytic a2 (l + 2 + 1)
  have hG : Real.Gamma ((l + 2 : ℕ) : ℝ) = q := by
    rw [show ((l + 2 : ℕ) : ℝ) = ((l + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
  have hQlim : Tendsto Q2 (𝓝[>] 0) (𝓝 q) := by
    have hJ := J_tendsto_Gamma (show (0:ℝ) < ((l + 2 : ℕ) : ℝ) by positivity)
    rw [hG] at hJ
    have := hJ.sub (h2'.trans_tendsto (tendsto_pow_zero (m := l + 1) (by omega)))
    rw [sub_zero] at this
    exact this.congr (fun y => by ring)
  have hQ20 : Q2 0 = q :=
    tendsto_nhds_unique (hQ2an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hQlim
  have K := key_log (m := l + 1) (by omega) hqpos.ne' h1' h2' hQ1an.continuousAt
    hQ2an.differentiableAt.hasDerivAt hQ20
  refine ⟨fun s => (2 - ((l : ℝ) + 2) - 2 * (s * R ^ 2 / 4 * Q1 (s * R ^ 2 / 4) / Q2 (s * R ^ 2 / 4))
    + 4 * c / q * Real.log 2 * (s * R ^ 2 / 4) ^ (l + 2)) / R ^ 4, ?_, ?_⟩
  · have hin : AnalyticAt ℝ (fun s : ℝ => s * R ^ 2 / 4) 0 := by fun_prop
    have hin0 : (fun s : ℝ => s * R ^ 2 / 4) 0 = 0 := by simp
    have hP1 := hQ1an.comp_of_eq hin hin0
    have hP2 := hQ2an.comp_of_eq hin hin0
    have hne : (Q2 ∘ fun s : ℝ => s * R ^ 2 / 4) 0 ≠ 0 := by
      simp only [Function.comp_apply, zero_mul, zero_div]
      rw [hQ20]; exact hqpos.ne'
    have e2 : AnalyticAt ℝ (fun s => s * R ^ 2 / 4 * Q1 (s * R ^ 2 / 4) / Q2 (s * R ^ 2 / 4)) 0 :=
      (hin.mul hP1).div hP2 hne
    exact (((analyticAt_const.sub (analyticAt_const.mul e2)).add
      (analyticAt_const.mul (hin.pow (l + 2)))).div analyticAt_const (pow_ne_zero 4 hR.ne'))
  · set u : ℝ → ℝ := fun k => (k * R / 2) ^ 2 with hu
    have hut : Tendsto u (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.2
      constructor
      · have : Continuous u := by rw [hu]; fun_prop
        have h := this.tendsto 0
        simp only [hu, zero_mul, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
        show 0 < (k * R / 2) ^ 2
        positivity
    have K2 := (K.comp_tendsto hut).const_mul_left (-2 / R ^ 4)
    have hO : (fun k => u k ^ (l + 1 + 1)) =O[𝓝[>] (0:ℝ)] (fun k : ℝ => k ^ (2 * l + 4)) := by
      have := isBigO_const_mul_self ((R / 2) ^ (2 * l + 4)) (fun k : ℝ => k ^ (2 * l + 4))
        (𝓝[>] (0:ℝ))
      refine this.congr' ?_ (Eventually.of_forall (fun _ => rfl))
      exact Eventually.of_forall (fun k => by simp only [hu]; rw [← pow_mul, ← mul_pow]; ring_nf)
    have hQu : ∀ᶠ k in 𝓝[>] (0:ℝ), Q2 (u k) ≠ 0 := (hQlim.comp hut).eventually_ne hqpos.ne'
    refine (K2.trans_isBigO hO).congr' ?_ (Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin, hQu] with k (hk : 0 < k) hQk
    simp only [Function.comp_apply, hu] at hQk ⊢
    rw [fluxFactor_eq ((l : ℝ) + 2) hk hR, show k ^ 2 * R ^ 2 / 4 = (k * R / 2) ^ 2 by ring,
      show (l : ℝ) + 2 - 1 = ((l + 1 : ℕ) : ℝ) by push_cast; ring]
    have hkR : 0 < k * R := mul_pos hk hR
    have hlogy : Real.log ((k * R / 2) ^ 2) = 2 * Real.log (k * R) - 2 * Real.log 2 := by
      rw [Real.log_pow, Real.log_div hkR.ne' (by norm_num)]; push_cast; ring
    rw [hlogy]
    have hJ := J_pos ((l : ℝ) + 2) (show 0 < (k * R / 2) ^ 2 by positivity)
    have hJ2 : J ((l + 2 : ℕ) : ℝ) ((k * R / 2) ^ 2) = J ((l : ℝ) + 2) ((k * R / 2) ^ 2) := by
      push_cast; ring_nf
    rw [hJ2]
    have hR4 : R ^ 4 ≠ 0 := pow_ne_zero 4 hR.ne'
    simp only [hc, hq, cL]
    have hf : ((l + 1).factorial : ℝ) ≠ 0 := hqpos.ne'
    have h4 : (1 / 4 : ℝ) ^ l * 2 ^ (l * 2) = 1 := by
      rw [mul_comm l 2, pow_mul, ← mul_pow]; norm_num
    field_simp
    linear_combination (2 * R ^ 4 * R ^ (l * 2) * k ^ 4 * k ^ (l * 2) * Real.log (R * k) * (-1) ^ l) * h4

end GKP1998Flux

open Filter Topology Asymptotics GKP1998 in
theorem solution (l : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => fluxFactor ((l : ℝ) + 2) k R - A (k ^ 2)
          - (-(-1 : ℝ) ^ l / (2 ^ (2 * l + 2) * ((l + 1).factorial : ℝ) ^ 2))
              * k ^ (2 * l + 4) * R ^ (2 * l) * Real.log (k * R))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * l + 4)) := by
  exact GKP1998Flux.main_result l R hR
