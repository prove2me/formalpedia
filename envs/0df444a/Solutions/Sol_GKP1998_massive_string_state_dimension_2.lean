-- Prove2me | solution 2 for GKP1998.massive_string_state_dimension
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T10:28:54.224988+00:00
-- url     : https://prove2.me/submissions/f7772e90-fd19-4f02-8632-43980d85c5f9

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

/-! ### small-`y` asymptotics of `J` -/

/-- polynomial part `Σ_{j<m} (-y)^j Γ(μ-j)/j!`. -/
noncomputable def P (μ : ℝ) (m : ℕ) (y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range m, (-y) ^ j * Real.Gamma (μ - j) / (j.factorial : ℝ)

/-- the asymptotic statement for order `μ` with `m` polynomial terms. -/
def Asy (μ : ℝ) (m : ℕ) : Prop :=
  (fun y => J μ y - P μ m y - Real.Gamma (-μ) * y ^ μ) =o[𝓝[>] (0:ℝ)] (fun y => y ^ μ)

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

lemma P_succ (μ : ℝ) (m : ℕ) (y : ℝ) :
    P (μ + 1) (m + 1) y = Real.Gamma (μ + 1) +
      ∑ j ∈ Finset.range m, (-y) ^ (j + 1) * Real.Gamma (μ - j) / ((j + 1).factorial : ℝ) := by
  unfold P
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero, Nat.factorial_zero, Nat.cast_one,
    div_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  congr 3
  push_cast; ring

lemma P_hasDerivAt (μ : ℝ) (m : ℕ) (y : ℝ) :
    HasDerivAt (P (μ + 1) (m + 1)) (-P μ m y) y := by
  have hfun : P (μ + 1) (m + 1) = fun y => Real.Gamma (μ + 1) +
      ∑ j ∈ Finset.range m, (-y) ^ (j + 1) * Real.Gamma (μ - j) / ((j + 1).factorial : ℝ) := by
    funext y; exact P_succ μ m y
  rw [hfun]
  have hs : HasDerivAt (fun y : ℝ => ∑ j ∈ Finset.range m,
      (-y) ^ (j + 1) * Real.Gamma (μ - j) / ((j + 1).factorial : ℝ))
      (∑ j ∈ Finset.range m, -((-y) ^ j * Real.Gamma (μ - j) / (j.factorial : ℝ))) y := by
    apply HasDerivAt.fun_sum
    intro j _
    have h1 : HasDerivAt (fun y : ℝ => (-y) ^ (j + 1)) (((j + 1 : ℕ) : ℝ) * (-y) ^ j * (-1)) y := by
      have := (hasDerivAt_neg y).pow (j + 1)
      refine this.congr_deriv ?_
      simp
    have h2 := (h1.mul_const (Real.Gamma (μ - j))).div_const ((j + 1).factorial : ℝ)
    refine h2.congr_deriv ?_
    rw [Nat.factorial_succ]
    push_cast
    have : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
    field_simp
  have := hs.const_add (Real.Gamma (μ + 1))
  refine this.congr_deriv ?_
  unfold P
  rw [Finset.sum_neg_distrib]

lemma P_zero (μ : ℝ) (m : ℕ) : P (μ + 1) (m + 1) 0 = Real.Gamma (μ + 1) := by
  rw [P_succ]
  simp

lemma asy_step {μ : ℝ} {m : ℕ} (hμ : -1 < μ) (h : Asy μ m) : Asy (μ + 1) (m + 1) := by
  unfold Asy at *
  have hμ1 : 0 < μ + 1 := by linarith
  have hG : Real.Gamma (-(μ + 1)) * (μ + 1) = -Real.Gamma (-μ) := by
    have h0 : -(μ + 1) ≠ 0 := by linarith
    have := Real.Gamma_add_one h0
    rw [show -(μ + 1) + 1 = -μ by ring] at this
    rw [this]; ring
  apply littleO_of_deriv hμ (e := fun y => -(J μ y - P μ m y - Real.Gamma (-μ) * y ^ μ))
  · intro y hy
    have h1 := J_hasDerivAt (μ + 1) hy
    rw [add_sub_cancel_right] at h1
    have h2 := P_hasDerivAt μ m y
    have h3 := (Real.hasDerivAt_rpow_const (x := y) (p := μ + 1) (Or.inl hy.ne')).const_mul
      (Real.Gamma (-(μ + 1)))
    rw [add_sub_cancel_right] at h3
    refine ((h1.sub h2).sub h3).congr_deriv ?_
    rw [← mul_assoc, hG]; ring
  · exact h.neg_left
  · have h1 := J_tendsto_Gamma hμ1
    have h2 : Tendsto (P (μ + 1) (m + 1)) (𝓝[>] 0) (𝓝 (Real.Gamma (μ + 1))) := by
      have := (P_hasDerivAt μ m 0).continuousAt.tendsto
      rw [P_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 := (tendsto_rpow_zero hμ1).const_mul (Real.Gamma (-(μ + 1)))
    simpa using (h1.sub h2).sub h3

lemma asy_base {θ : ℝ} (hθ : θ < 0) : Asy θ 0 := by
  unfold Asy
  have hlim := J_tendsto_Gamma (show 0 < -θ by linarith)
  have h1 : (fun y => J (-θ) y - Real.Gamma (-θ)) =o[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) :=
    (isLittleO_one_iff ℝ).2 (by simpa using hlim.sub_const (Real.Gamma (-θ)))
  have h2 := (isBigO_refl (fun y : ℝ => y ^ θ) (𝓝[>] (0:ℝ))).mul_isLittleO h1
  simp only [mul_one] at h2
  refine h2.congr' ?_ (Eventually.of_forall (fun _ => rfl))
  filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
  simp only [P, Finset.range_zero, Finset.sum_empty, sub_zero]
  rw [J_symm θ hy]; ring

lemma asy_all {θ : ℝ} (hθ1 : -1 < θ) (hθ : θ < 0) (m : ℕ) : Asy (θ + m) m := by
  induction m with
  | zero => simpa using asy_base hθ
  | succ m ih =>
    have := asy_step (show -1 < θ + m by have : (0:ℝ) ≤ m := m.cast_nonneg; linarith) ih
    rwa [show θ + ((m + 1 : ℕ) : ℝ) = θ + m + 1 by push_cast; ring]

/-! ### the flux factor in terms of `J` -/

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

/-! ### assembly -/

lemma P_analytic (μ : ℝ) (m : ℕ) : AnalyticAt ℝ (P μ m) 0 := by
  induction m with
  | zero =>
    have : P μ 0 = fun _ => 0 := by funext y; simp [P]
    rw [this]; exact analyticAt_const
  | succ m ih =>
    have : P μ (m + 1) = fun y => P μ m y +
        (-y) ^ m * Real.Gamma (μ - m) / (m.factorial : ℝ) := by
      funext y; simp [P, Finset.sum_range_succ]
    rw [this]
    refine ih.add ?_
    fun_prop

lemma P_zero' {ν : ℝ} {m : ℕ} (hm : 1 ≤ m) : P ν m 0 = Real.Gamma ν := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have := P_zero (ν - 1) n
  rwa [sub_add_cancel] at this

lemma key_asym {ν : ℝ} {m : ℕ} (hν : 0 < ν) (hm : 1 ≤ m) (h0 : Asy ν m)
    (h1 : Asy (ν - 1) (m - 1)) :
    (fun y => y * J (ν - 1) y / J ν y - y * P (ν - 1) (m - 1) y / P ν m y
      - Real.Gamma (1 - ν) / Real.Gamma ν * y ^ ν) =o[𝓝[>] (0:ℝ)] (fun y => y ^ ν) := by
  unfold Asy at h0 h1
  rw [show -(ν - 1) = 1 - ν by ring] at h1
  have hGν : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  have hJlim := J_tendsto_Gamma hν
  have hPlim : Tendsto (P ν m) (𝓝[>] 0) (𝓝 (Real.Gamma ν)) := by
    have := (P_analytic ν m).continuousAt.tendsto
    rw [P_zero' hm] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hP1lim : Tendsto (fun y => y * P (ν - 1) (m - 1) y) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun y => y * P (ν - 1) (m - 1) y) 0 :=
      continuousAt_id.mul (P_analytic (ν - 1) (m - 1)).continuousAt
    have h := hc.tendsto
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hJne : ∀ᶠ y in 𝓝[>] (0:ℝ), J ν y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    exact (J_pos ν hy).ne'
  have hPne : ∀ᶠ y in 𝓝[>] (0:ℝ), P ν m y ≠ 0 := hPlim.eventually_ne hGν
  have hpos : ∀ᶠ y in 𝓝[>] (0:ℝ), 0 < y := self_mem_nhdsWithin
  have hyy : ∀ y : ℝ, 0 < y → y * y ^ (ν - 1) = y ^ ν := by
    intro y hy
    rw [Real.rpow_sub_one hy.ne']; field_simp
  -- term 1
  have N1 := (isBigO_refl (fun y : ℝ => y) (𝓝[>] (0:ℝ))).mul_isLittleO h1
  have N1' : (fun y => y * J (ν - 1) y - y * P (ν - 1) (m - 1) y - Real.Gamma (1 - ν) * y ^ ν)
      =o[𝓝[>] (0:ℝ)] (fun y => y ^ ν) := by
    refine N1.congr' ?_ ?_
    · filter_upwards [hpos] with y hy
      rw [← hyy y hy]; ring
    · filter_upwards [hpos] with y hy
      exact hyy y hy
  have hinvJ : (fun y => (J ν y)⁻¹) =O[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) :=
    (hJlim.inv₀ hGν).isBigO_one ℝ
  have T1 := N1'.mul_isBigO hinvJ
  -- term 2
  have hT2lim : Tendsto (fun y => (Real.Gamma ν - J ν y) / (J ν y * Real.Gamma ν))
      (𝓝[>] 0) (𝓝 ((Real.Gamma ν - Real.Gamma ν) / (Real.Gamma ν * Real.Gamma ν))) :=
    ((tendsto_const_nhds (x := Real.Gamma ν)).sub hJlim).div (hJlim.mul_const (Real.Gamma ν))
      (mul_ne_zero hGν hGν)
  rw [sub_self, zero_div] at hT2lim
  have T2 := ((isBigO_refl (fun y : ℝ => y ^ ν) (𝓝[>] (0:ℝ))).const_mul_left
    (Real.Gamma (1 - ν))).mul_isLittleO ((isLittleO_one_iff ℝ).2 hT2lim)
  -- term 3
  have hc : (fun y => J ν y - P ν m y) =O[𝓝[>] (0:ℝ)] (fun y => y ^ ν) := by
    have := h0.isBigO.add ((isBigO_refl (fun y : ℝ => y ^ ν) (𝓝[>] (0:ℝ))).const_mul_left
      (Real.Gamma (-ν)))
    refine this.congr' ?_ (Eventually.of_forall (fun _ => rfl))
    exact Eventually.of_forall (fun y => by ring)
  have hinvJP : (fun y => (J ν y * P ν m y)⁻¹) =O[𝓝[>] (0:ℝ)] (fun _ => (1:ℝ)) :=
    ((hJlim.mul hPlim).inv₀ (mul_ne_zero hGν hGν)).isBigO_one ℝ
  have T3 := (((isLittleO_one_iff ℝ).2 hP1lim).neg_left.mul_isBigO hc).mul_isBigO hinvJP
  have T3' : (fun y => -(y * P (ν - 1) (m - 1) y) * (J ν y - P ν m y) * (J ν y * P ν m y)⁻¹)
      =o[𝓝[>] (0:ℝ)] (fun y => y ^ ν * 1) :=
    T3.congr' (Eventually.of_forall (fun _ => rfl)) (Eventually.of_forall (fun _ => by ring))
  have T := (T1.add T2).add T3'
  refine T.congr' ?_ ?_
  · filter_upwards [hJne, hPne] with y hJ hP
    field_simp
    ring
  · exact Eventually.of_forall (fun y => by ring)

lemma ceil_facts {ν : ℝ} (hν : 0 < ν) (hνZ : ∀ n : ℤ, ν ≠ n) :
    1 ≤ ⌈ν⌉₊ ∧ -1 < ν - ⌈ν⌉₊ ∧ ν - ⌈ν⌉₊ < 0 := by
  have h1 : ν ≤ ⌈ν⌉₊ := Nat.le_ceil ν
  have h2 : (⌈ν⌉₊ : ℝ) < ν + 1 := Nat.ceil_lt_add_one hν.le
  have h3 : ν ≠ (⌈ν⌉₊ : ℝ) := by
    have := hνZ (⌈ν⌉₊ : ℤ); simpa using this
  have h4 : ν < ⌈ν⌉₊ := lt_of_le_of_ne h1 h3
  refine ⟨?_, by linarith, by linarith⟩
  have : (0 : ℝ) < ⌈ν⌉₊ := by linarith
  exact_mod_cast this

theorem main_result (ν R : ℝ) (hν : 0 < ν) (hνZ : ∀ n : ℤ, ν ≠ n) (hR : 0 < R) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => GKP1998.fluxFactor ν k R - A (k ^ 2)
          - (-2 * ν * Real.Gamma (1 - ν) / Real.Gamma (1 + ν) * (k * R / 2) ^ (2 * ν) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * ν)) := by
  obtain ⟨hm, hθ1, hθ⟩ := ceil_facts hν hνZ
  set m := ⌈ν⌉₊ with hmd
  have h0 : Asy ν m := by
    have := asy_all hθ1 hθ m
    rwa [show ν - (m : ℝ) + m = ν by ring] at this
  have h1 : Asy (ν - 1) (m - 1) := by
    have := asy_all hθ1 hθ (m - 1)
    rwa [show ν - (m : ℝ) + ((m - 1 : ℕ) : ℝ) = ν - 1 by
      rw [Nat.cast_sub hm, Nat.cast_one]; ring] at this
  have K := key_asym hν hm h0 h1
  have hGν : Real.Gamma ν ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
  refine ⟨fun s => (2 - ν - 2 * (s * R ^ 2 / 4) * P (ν - 1) (m - 1) (s * R ^ 2 / 4)
    / P ν m (s * R ^ 2 / 4)) / R ^ 4, ?_, ?_⟩
  · have hin : AnalyticAt ℝ (fun s : ℝ => s * R ^ 2 / 4) 0 := by fun_prop
    have hin0 : (fun s : ℝ => s * R ^ 2 / 4) 0 = 0 := by simp
    have hP := (P_analytic ν m).comp_of_eq hin hin0
    have hP1 := (P_analytic (ν - 1) (m - 1)).comp_of_eq hin hin0
    have hne : (P ν m ∘ fun s : ℝ => s * R ^ 2 / 4) 0 ≠ 0 := by
      simp only [Function.comp_apply, zero_mul, zero_div]
      rw [P_zero' hm]; exact hGν
    have e1 : AnalyticAt ℝ (fun s => 2 * (s * R ^ 2 / 4) * P (ν - 1) (m - 1) (s * R ^ 2 / 4)) 0 :=
      (analyticAt_const.mul hin).mul hP1
    have e2 : AnalyticAt ℝ (fun s => 2 * (s * R ^ 2 / 4) * P (ν - 1) (m - 1) (s * R ^ 2 / 4)
        / P ν m (s * R ^ 2 / 4)) 0 := e1.div hP hne
    have e3 : AnalyticAt ℝ (fun s => 2 - ν - 2 * (s * R ^ 2 / 4) * P (ν - 1) (m - 1) (s * R ^ 2 / 4)
        / P ν m (s * R ^ 2 / 4)) 0 := analyticAt_const.sub e2
    exact e3.div analyticAt_const (pow_ne_zero 4 hR.ne')
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
    have hO : (fun k => u k ^ ν) =O[𝓝[>] (0:ℝ)] (fun k : ℝ => k ^ (2 * ν)) := by
      have := isBigO_const_mul_self ((R / 2) ^ (2 * ν)) (fun k : ℝ => k ^ (2 * ν)) (𝓝[>] (0:ℝ))
      refine this.congr' ?_ (Eventually.of_forall (fun _ => rfl))
      filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
      simp only [hu]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show k * R / 2 = (R / 2) * k by ring, Real.mul_rpow (by positivity) hk.le]
      push_cast; ring_nf
    refine (K2.trans_isBigO hO).congr' ?_ (Eventually.of_forall (fun _ => rfl))
    filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
    simp only [Function.comp_apply, hu]
    rw [fluxFactor_eq ν hk hR, show k ^ 2 * R ^ 2 / 4 = (k * R / 2) ^ 2 by ring,
      show (1 + ν) = ν + 1 by ring, Real.Gamma_add_one hν.ne']
    have hc : 0 < k * R / 2 := by positivity
    rw [show (k * R / 2) ^ (2 * ν) = ((k * R / 2) ^ 2) ^ ν by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; push_cast; ring_nf]
    have hJ := J_pos ν (show 0 < (k * R / 2) ^ 2 by positivity)
    have hR4 : R ^ 4 ≠ 0 := pow_ne_zero 4 hR.ne'
    field_simp
    ring

end GKP1998Flux

namespace GKP1998Glue

open GKP1998 in
theorem mass_radius (n : ℕ) (N gYM α' m R : ℝ) (hN : 0 < N) (hg : 0 < gYM)
    (hα : 0 < α') (hm : 0 < m) (hR : 0 < R) (hmass : m ^ 2 = 4 * n / α')
    (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2) :
    (m * R) ^ 2 = 4 * n * gYM * Real.sqrt (2 * N) := by
  have hs : 0 ≤ Real.sqrt (2 * N) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (2 * N) ^ 2 = 2 * N := Real.sq_sqrt (by positivity)
  have hR2 : R ^ 2 = gYM * α' * Real.sqrt (2 * N) := by
    have h1 : (R ^ 2) ^ 2 = (gYM * α' * Real.sqrt (2 * N)) ^ 2 := by
      rw [← pow_mul, hradius]
      have : (gYM * α' * Real.sqrt (2 * N)) ^ 2 = gYM ^ 2 * α' ^ 2 * Real.sqrt (2 * N) ^ 2 := by
        ring
      rw [this, hs2]
      ring
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).1 h1
  rw [mul_pow, hmass, hR2]
  field_simp

open Filter Topology Asymptotics GKP1998 in
theorem scaling_asym (n : ℕ) (hn : 1 ≤ n) (N : ℝ) (hN : 0 < N) :
    Tendsto (fun gYM : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * gYM * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by
  set c : ℝ := (n : ℝ) * Real.sqrt (2 * N) with hc_def
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (2 * N) := Real.sqrt_pos.mpr (by linarith)
  have hc : 0 < c := mul_pos hn' hs
  -- t = 1/(c g) → 0
  have ht : Tendsto (fun g : ℝ => (c * g)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hc tendsto_id)
  have hcont : Continuous (fun t : ℝ => Real.sqrt t + Real.sqrt (t + 1)) := by
    fun_prop
  have hlim : Tendsto (fun g : ℝ => Real.sqrt ((c * g)⁻¹) + Real.sqrt ((c * g)⁻¹ + 1))
      atTop (𝓝 1) := by
    have := (hcont.tendsto 0).comp ht
    have h1 : Real.sqrt 0 + Real.sqrt (0 + 1) = 1 := by simp
    rw [h1] at this
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with g hg
  have hcg : 0 < c * g := mul_pos hc hg
  have e1 : (n : ℝ) * g * Real.sqrt (2 * N) = c * g := by rw [hc_def]; ring
  have e2 : 4 + 4 * (n : ℝ) * g * Real.sqrt (2 * N) = 4 * (c * g + 1) := by rw [hc_def]; ring
  simp only [scalingDimension]
  rw [e1, e2]
  have hsq : 0 < Real.sqrt (c * g) := Real.sqrt_pos.mpr hcg
  have h4 : Real.sqrt (4 * (c * g + 1)) = 2 * Real.sqrt (c * g + 1) := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hinv : Real.sqrt ((c * g)⁻¹) = (Real.sqrt (c * g))⁻¹ := Real.sqrt_inv _
  have hdiv : Real.sqrt ((c * g)⁻¹ + 1) = Real.sqrt (c * g + 1) / Real.sqrt (c * g) := by
    rw [← Real.sqrt_div' _ hcg.le]
    congr 1
    field_simp
    ring
  rw [h4, hinv, hdiv]
  field_simp

open Filter Topology Asymptotics GKP1998 in
theorem glue (n : ℕ) (hn : 1 ≤ n) (N gYM α' m R : ℝ)
    (hN : 0 < N) (hg : 0 < gYM) (hα : 0 < α') (hm : 0 < m) (hR : 0 < R)
    (hmass : m ^ 2 = 4 * n / α') (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2)
    (hνZ : ∀ j : ℤ, massiveOrder m R ≠ j) :
    (∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => twoPointFunction N (massiveOrder m R) k R - A (k ^ 2)
          - (-(N ^ 2 / (8 * Real.pi ^ 2)) * Real.Gamma (1 - massiveOrder m R)
              / Real.Gamma (massiveOrder m R) * (k * R / 2) ^ (2 * massiveOrder m R) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * massiveOrder m R))) ∧
    scalingDimension (massiveOrder m R) = 2 + Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)) ∧
    Tendsto (fun g : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * g * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * g * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by
  have hν : 0 < massiveOrder m R := by
    unfold massiveOrder; exact Real.sqrt_pos.2 (by positivity)
  obtain ⟨A, hA, ho⟩ := GKP1998Flux.main_result (massiveOrder m R) R hν hνZ hR
  refine ⟨⟨fun s => N ^ 2 / (16 * Real.pi ^ 2) * A s, analyticAt_const.mul hA, ?_⟩, ?_,
    scaling_asym n hn N hN⟩
  · refine (ho.const_mul_left (N ^ 2 / (16 * Real.pi ^ 2))).congr' ?_
      (Eventually.of_forall (fun _ => rfl))
    refine Eventually.of_forall (fun k => ?_)
    have hG : Real.Gamma (massiveOrder m R) ≠ 0 := (Real.Gamma_pos_of_pos hν).ne'
    simp only [twoPointFunction]
    rw [show 1 + massiveOrder m R = massiveOrder m R + 1 by ring, Real.Gamma_add_one hν.ne']
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  · unfold scalingDimension massiveOrder
    rw [mass_radius n N gYM α' m R hN hg hα hm hR hmass hradius]

end GKP1998Glue

open Filter Topology Asymptotics GKP1998 in
theorem solution (n : ℕ) (hn : 1 ≤ n) (N gYM α' m R : ℝ)
    (hN : 0 < N) (hg : 0 < gYM) (hα : 0 < α') (hm : 0 < m) (hR : 0 < R)
    (hmass : m ^ 2 = 4 * n / α') (hradius : R ^ 4 = 2 * N * gYM ^ 2 * α' ^ 2)
    (hνZ : ∀ j : ℤ, massiveOrder m R ≠ j) :
    (∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => twoPointFunction N (massiveOrder m R) k R - A (k ^ 2)
          - (-(N ^ 2 / (8 * Real.pi ^ 2)) * Real.Gamma (1 - massiveOrder m R)
              / Real.Gamma (massiveOrder m R) * (k * R / 2) ^ (2 * massiveOrder m R) / R ^ 4))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * massiveOrder m R))) ∧
    scalingDimension (massiveOrder m R) = 2 + Real.sqrt (4 + 4 * n * gYM * Real.sqrt (2 * N)) ∧
    Tendsto (fun g : ℝ =>
        scalingDimension (Real.sqrt (4 + 4 * n * g * Real.sqrt (2 * N)))
          / (2 * Real.sqrt (n * g * Real.sqrt (2 * N))))
      atTop (𝓝 1) := by
  exact GKP1998Glue.glue n hn N gYM α' m R hN hg hα hm hR hmass hradius hνZ
