-- Prove2me | solution 1 for Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/344b3bdd-c6ee-5021-97f2-a5ec5acbd7b2

import Mathlib
import Theorems.Thm_Complex_integral_inv_sub_mul_dbar_eq_neg_pi_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

p2m_open "Complex P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.Complex MeasureTheory Filter Set Metric"
open scoped Real Topology Manifold ContDiff

namespace Complex
p2m_export "Complex" "contDiffAt_log hasDerivAt_exp finrank_real_complex ofRealCLM slitPlane_ne_zero mem_slitPlane_of_norm_lt_one exp exp_log log ext I I_mul_I slitPlane integral_inv_sub_mul_dbar_eq_neg_pi_mul"
namespace WedgeArgument
p2m_open "Complex"

theorem continuous_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgV : tsupport g ⊆ V) :
    Continuous fun z => f z * g z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ V
  · exact (hf.continuousAt (hV.mem_nhds hz)).mul hg.continuousAt
  · have hz' : z ∉ tsupport g := fun h' => hz (hgV h')
    have h0 : g =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : (fun w => f w * g w) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [hw]
    exact (continuousAt_congr this).2 continuousAt_const

theorem integrable_mul_of_tsupport_subset {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun z => f z * g z :=
  (continuous_mul_of_tsupport_subset hV hf hg hgV).integrable_of_hasCompactSupport hgs.mul_left

theorem integrable_mul_of_tsupport_subset' {V : Set ℂ} {f g : ℂ → ℂ} (hV : IsOpen V)
    (hf : ContinuousOn f V) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hgV : tsupport g ⊆ V) : Integrable fun z => g z * f z := by
  simpa only [mul_comm] using integrable_mul_of_tsupport_subset hV hf hg hgs hgV

theorem mul_eq_of_tsupport_subset {V : Set ℂ} {f f' g : ℂ → ℂ} (hgV : tsupport g ⊆ V)
    (hff' : ∀ z ∈ V, f z = f' z) (z : ℂ) : f z * g z = f' z * g z := by
  by_cases hz : z ∈ V
  · rw [hff' z hz]
  · rw [image_eq_zero_of_notMem_tsupport fun h => hz (hgV h), mul_zero, mul_zero]

theorem fderiv_apply_props {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hψs : HasCompactSupport ψ) (v : ℂ) :
    Continuous (fun z => fderiv ℝ ψ z v) ∧ HasCompactSupport (fun z => fderiv ℝ ψ z v) ∧
      tsupport (fun z => fderiv ℝ ψ z v) ⊆ tsupport ψ :=
  ⟨(hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const, hψs.fderiv_apply ℝ v,
    tsupport_fderiv_apply_subset ℝ v⟩

theorem contDiff_fderiv_apply {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (w : ℂ) :
    ContDiff ℝ 1 fun z => fderiv ℝ v z w := by
  have h : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (m := 1) (by norm_num)
  exact h.clm_apply contDiff_const

theorem mixed_partials_symm {v : ℂ → ℂ} (hv : ContDiff ℝ 2 v) (z a b : ℂ) :
    fderiv ℝ (fun w => fderiv ℝ v w a) z b = fderiv ℝ (fun w => fderiv ℝ v w b) z a := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) z :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  have hs : IsSymmSndFDerivAt ℝ v z :=
    hv.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  exact hs.eq b a

theorem integral_wedge_eq_zero {O : Set ℂ} (hO : IsOpen O) {u v : ℂ → ℂ}
    (hu : ContDiffOn ℝ 1 u O) (hv : ContDiff ℝ 2 v) (hvs : HasCompactSupport v)
    (hvO : tsupport v ⊆ O) :
    ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z I - fderiv ℝ u z I * fderiv ℝ v z 1) = 0 := by

  set vx : ℂ → ℂ := fun z => fderiv ℝ v z 1 with hvx
  set vy : ℂ → ℂ := fun z => fderiv ℝ v z I with hvy
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  obtain ⟨hvxc, hvxs, hvxt⟩ := fderiv_apply_props hv1 hvs 1
  obtain ⟨hvyc, hvys, hvyt⟩ := fderiv_apply_props hv1 hvs I
  have hvxO : tsupport vx ⊆ O := hvxt.trans hvO
  have hvyO : tsupport vy ⊆ O := hvyt.trans hvO
  have hvxd : ContDiff ℝ 1 vx := contDiff_fderiv_apply hv 1
  have hvyd : ContDiff ℝ 1 vy := contDiff_fderiv_apply hv I

  have huc : ContinuousOn u O := hu.continuousOn
  have hu' : ContinuousOn (fderiv ℝ u) O := hu.continuousOn_fderiv_of_isOpen hO le_rfl
  have hux : ContinuousOn (fun z => fderiv ℝ u z 1) O := hu'.clm_apply continuousOn_const
  have huy : ContinuousOn (fun z => fderiv ℝ u z I) O := hu'.clm_apply continuousOn_const
  have hud : ∀ z ∈ O, DifferentiableAt ℝ u z := fun z hz =>
    (hu.differentiableOn one_ne_zero z hz).differentiableAt (hO.mem_nhds hz)

  obtain ⟨hvyxc, hvyxs, hvyxt⟩ := fderiv_apply_props hvyd hvys 1
  obtain ⟨hvxyc, hvxys, hvxyt⟩ := fderiv_apply_props hvxd hvxs I

  have ibp1 : ∫ z, vy z * fderiv ℝ u z 1 = -∫ z, fderiv ℝ vy z 1 * u z := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset' hO huc hvyxc hvyxs (hvyxt.trans hvyO)
    · exact integrable_mul_of_tsupport_subset' hO hux hvyc hvys hvyO
    · exact integrable_mul_of_tsupport_subset' hO huc hvyc hvys hvyO
    · intro x _; exact (hvyd.differentiable one_ne_zero) x
    · intro x hx; exact hud x (hvyO hx)

  have ibp2 : ∫ z, vx z * fderiv ℝ u z I = -∫ z, fderiv ℝ vx z I * u z := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact integrable_mul_of_tsupport_subset' hO huc hvxyc hvxys (hvxyt.trans hvxO)
    · exact integrable_mul_of_tsupport_subset' hO huy hvxc hvxs hvxO
    · exact integrable_mul_of_tsupport_subset' hO huc hvxc hvxs hvxO
    · intro x _; exact (hvxd.differentiable one_ne_zero) x
    · intro x hx; exact hud x (hvxO hx)

  have hsymm : ∀ z, fderiv ℝ vy z 1 = fderiv ℝ vx z I := fun z => mixed_partials_symm hv z I 1
  have hI1 : Integrable fun z => vy z * fderiv ℝ u z 1 :=
    integrable_mul_of_tsupport_subset' hO hux hvyc hvys hvyO
  have hI2 : Integrable fun z => vx z * fderiv ℝ u z I :=
    integrable_mul_of_tsupport_subset' hO huy hvxc hvxs hvxO
  calc ∫ z, (fderiv ℝ u z 1 * fderiv ℝ v z I - fderiv ℝ u z I * fderiv ℝ v z 1)
      = ∫ z, (vy z * fderiv ℝ u z 1 - vx z * fderiv ℝ u z I) := by
        congr 1; funext z; simp only [hvx, hvy]; ring
    _ = (∫ z, vy z * fderiv ℝ u z 1) - ∫ z, vx z * fderiv ℝ u z I := integral_sub hI1 hI2
    _ = 0 := by
        rw [ibp1, ibp2]
        simp only [hsymm, sub_self]

def D (f : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ f z 1 + I * fderiv ℝ f z I) / 2

theorem D_continuous {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f) : Continuous (D f) := by
  unfold D
  have hc : ∀ v : ℂ, Continuous fun z => fderiv ℝ f z v := fun v =>
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hc 1).add (continuous_const.mul (hc I))).div_const _

theorem D_eq_zero_of_notMem_tsupport {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ tsupport f) : D f z = 0 := by
  simp [D, fderiv_of_notMem_tsupport ℝ hz]

theorem D_hasCompactSupport {f : ℂ → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (D f) :=
  HasCompactSupport.intro hf fun _ hz => D_eq_zero_of_notMem_tsupport hz

theorem tsupport_D_subset (f : ℂ → ℂ) : tsupport (D f) ⊆ tsupport f :=
  closure_minimal (fun _ hz => by
    by_contra h'
    exact hz (D_eq_zero_of_notMem_tsupport h')) (isClosed_tsupport f)

theorem integrableOn_inv (r : ℝ) : IntegrableOn (fun x : ℂ => x⁻¹) (ball 0 r) := by
  have hd : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) hd (C := 1) (α := 1) ?_ ?_ ?_
  · rw [Complex.finrank_real_complex]; norm_num
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [norm_inv, Real.rpow_neg_one, one_mul]
  · exact measurable_inv.aestronglyMeasurable

theorem integrableOn_inv_sub (a : ℂ) (r : ℝ) :
    IntegrableOn (fun z : ℂ => (z - a)⁻¹) (ball a r) := by
  have hT := (measurePreserving_add_right (volume : Measure ℂ) a).integrableOn_comp_preimage
    (measurableEmbedding_addRight a) (f := fun z : ℂ => (z - a)⁻¹) (s := ball a r)
  rw [← hT]
  have hpre : (fun x : ℂ => x + a) ⁻¹' ball a r = ball 0 r := by
    ext x
    simp only [mem_preimage, mem_ball_iff_norm, add_sub_cancel_right, sub_zero]
  rw [hpre]
  simp only [Function.comp_def, add_sub_cancel_right]
  exact integrableOn_inv r

theorem integrable_inv_sub_mul (a : ℂ) {u : ℂ → ℂ} (hu : Continuous u)
    (hus : HasCompactSupport u) : Integrable fun z => (z - a)⁻¹ * u z := by
  obtain ⟨R, hR⟩ := hus.isCompact.isBounded.subset_closedBall a
  have hq : IntegrableOn (fun z : ℂ => (z - a)⁻¹) (closedBall a (R + 1)) :=
    (integrableOn_inv_sub a (R + 2)).mono_set (closedBall_subset_ball (by linarith))
  have h1 : IntegrableOn (fun z => (z - a)⁻¹ * u z) (closedBall a (R + 1)) :=
    hq.mul_continuousOn hu.continuousOn (isCompact_closedBall _ _)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
  intro z hz
  have huz : u z ≠ 0 := fun h0 => hz (by simp [h0])
  exact closedBall_subset_closedBall (by linarith) (hR (subset_tsupport _ huz))

section Disc

variable {a : ℂ} {r : ℝ} {n : ℤ} {Ψ Φ E E' k : ℂ → ℂ}
  (hΨ : ContDiffOn ℝ 1 Ψ (ball a r))
  (hΨ1 : ∀ z ∈ ball a r, ‖Ψ z * (Ψ a)⁻¹ - 1‖ < 1) (hΨa : Ψ a ≠ 0)
  (hΦ : ∀ z ∈ ball a r, Φ z = (z - a) ^ n * Ψ z)
  (hE : ∀ z ∈ ball a r, HasDerivAt E (E' z) z)
  (hk : ContDiff ℝ 2 k) (hks : HasCompactSupport k) (hkr : tsupport k ⊆ ball a r)

def Lg (Ψ : ℂ → ℂ) (a z : ℂ) : ℂ := log (Ψ z * (Ψ a)⁻¹)

include hΨ1 in
theorem mem_slit {z : ℂ} (hz : z ∈ ball a r) : Ψ z * (Ψ a)⁻¹ ∈ slitPlane := by
  have : Ψ z * (Ψ a)⁻¹ = 1 + (Ψ z * (Ψ a)⁻¹ - 1) := by ring
  rw [this]; exact mem_slitPlane_of_norm_lt_one (hΨ1 z hz)

include hΨ1 hΨa in
theorem Ψ_ne {z : ℂ} (hz : z ∈ ball a r) : Ψ z ≠ 0 := by
  have := slitPlane_ne_zero (mem_slit hΨ1 hz)
  exact left_ne_zero_of_mul this

include hΨ hΨ1 in
theorem contDiffOn_Lg : ContDiffOn ℝ 1 (Lg Ψ a) (ball a r) := by
  intro z hz
  have h1 : ContDiffWithinAt ℝ 1 (fun w => Ψ w * (Ψ a)⁻¹) (ball a r) z :=
    (hΨ z hz).mul contDiffWithinAt_const
  have h2 : ContDiffAt ℝ 1 log (Ψ z * (Ψ a)⁻¹) :=
    (Complex.contDiffAt_log (mem_slit hΨ1 hz)).restrict_scalars ℝ
  exact h2.comp_contDiffWithinAt z h1

include hΨ1 hΨa in
theorem exp_Lg {z : ℂ} (hz : z ∈ ball a r) : exp (Lg Ψ a z) = Ψ z * (Ψ a)⁻¹ :=
  Complex.exp_log (mul_ne_zero (Ψ_ne hΨ1 hΨa hz) (inv_ne_zero hΨa))

include hΨ hΨ1 hΨa in

theorem fderiv_Ψ_eq {z : ℂ} (hz : z ∈ ball a r) :
    fderiv ℝ Ψ z = Ψ z • fderiv ℝ (Lg Ψ a) z := by
  have hLd : DifferentiableAt ℝ (Lg Ψ a) z :=
    ((contDiffOn_Lg hΨ hΨ1).differentiableOn one_ne_zero z hz).differentiableAt
      (isOpen_ball.mem_nhds hz)
  have hΨd : DifferentiableAt ℝ Ψ z :=
    ((hΨ.differentiableOn one_ne_zero) z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  have hcomp : HasFDerivAt (fun w => exp (Lg Ψ a w)) (exp (Lg Ψ a z) • fderiv ℝ (Lg Ψ a) z) z :=
    (Complex.hasDerivAt_exp _).comp_hasFDerivAt z hLd.hasFDerivAt
  have hev : (fun w => exp (Lg Ψ a w)) =ᶠ[𝓝 z] fun w => Ψ w * (Ψ a)⁻¹ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using exp_Lg hΨ1 hΨa hw
  have h1 : HasFDerivAt (fun w => Ψ w * (Ψ a)⁻¹) (exp (Lg Ψ a z) • fderiv ℝ (Lg Ψ a) z) z :=
    hcomp.congr_of_eventuallyEq hev.symm
  have h2 : HasFDerivAt (fun w => Ψ w * (Ψ a)⁻¹) ((Ψ a)⁻¹ • fderiv ℝ Ψ z) z := by
    have := hΨd.hasFDerivAt.mul_const (Ψ a)⁻¹
    simpa [mul_comm] using this
  have heq := h1.unique h2
  rw [exp_Lg hΨ1 hΨa hz] at heq
  have : fderiv ℝ Ψ z = (Ψ a) • ((Ψ a)⁻¹ • fderiv ℝ Ψ z) := by
    rw [smul_smul, mul_inv_cancel₀ hΨa, one_smul]
  rw [this, ← heq, smul_smul]
  congr 1
  field_simp

include hE in
theorem analyticOnNhd_E : AnalyticOnNhd ℂ E (ball a r) := by
  have hd : DifferentiableOn ℂ E (ball a r) := fun z hz =>
    (hE z hz).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

include hE in
theorem contDiffAt_E {z : ℂ} (hz : z ∈ ball a r) (m : ℕ∞) : ContDiffAt ℝ m E z :=
  ((analyticOnNhd_E hE z hz).contDiffAt (n := m)).restrict_scalars ℝ

include hE in
theorem continuousOn_E' : ContinuousOn E' (ball a r) := by
  have h1 : ContinuousOn (deriv E) (ball a r) := (analyticOnNhd_E hE).deriv.continuousOn
  refine h1.congr fun z hz => ?_
  exact ((hE z hz).deriv).symm

def vEk (E k : ℂ → ℂ) (z : ℂ) : ℂ := E z * k z

include hE hk hkr in
theorem contDiff_vEk : ContDiff ℝ 2 (vEk E k) := by
  refine contDiff_iff_contDiffAt.2 fun z => ?_
  by_cases hz : z ∈ ball a r
  · exact (contDiffAt_E hE hz 2).mul hk.contDiffAt
  · have hz' : z ∉ tsupport k := fun h' => hz (hkr h')
    have h0 : k =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 hz'
    have : vEk E k =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [h0] with w hw
      simp [vEk, hw]
    exact contDiffAt_const.congr_of_eventuallyEq this

include hks in
theorem hasCompactSupport_vEk : HasCompactSupport (vEk E k) := hks.mul_left

theorem tsupport_vEk : tsupport (vEk E k) ⊆ tsupport k :=
  closure_minimal (fun z hz => subset_tsupport _ (right_ne_zero_of_mul hz)) (isClosed_tsupport _)

include hE hk hkr in
theorem fderiv_vEk {z : ℂ} (hz : z ∈ ball a r) (w : ℂ) :
    fderiv ℝ (vEk E k) z w = E z * fderiv ℝ k z w + k z * (E' z * w) := by
  have h1 : HasFDerivAt E (E' z • (1 : ℂ →L[ℝ] ℂ)) z := (hE z hz).complexToReal_fderiv
  have h2 : HasFDerivAt k (fderiv ℝ k z) z := (hk.differentiable (by norm_num) z).hasFDerivAt
  have h3 : HasFDerivAt (vEk E k) (E z • fderiv ℝ k z + k z • E' z • (1 : ℂ →L[ℝ] ℂ)) z :=
    h1.mul h2
  rw [h3.fderiv]
  simp [smul_eq_mul, mul_comm]

include hE hk hkr in

theorem D_vEk (z : ℂ) : D (vEk E k) z = E z * D k z := by
  by_cases hz : z ∈ ball a r
  · simp only [D, fderiv_vEk hE hk hkr hz]
    have : I * I = -1 := Complex.I_mul_I
    linear_combination (k z * E' z / 2) * this
  · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
    have hzv : z ∉ tsupport (vEk E k) := fun h' => hzk (tsupport_vEk h')
    rw [D_eq_zero_of_notMem_tsupport hzv, D_eq_zero_of_notMem_tsupport hzk, mul_zero]

include hΨ hΨ1 hΨa hΦ in

theorem fderiv_Φ_div {z : ℂ} (hz : z ∈ ball a r) (hza : z ≠ a) (w : ℂ) :
    fderiv ℝ Φ z w / Φ z = n * w / (z - a) + fderiv ℝ (Lg Ψ a) z w := by
  have hd : z - a ≠ 0 := sub_ne_zero.2 hza
  have hΨz : Ψ z ≠ 0 := Ψ_ne hΨ1 hΨa hz
  have hΨd : DifferentiableAt ℝ Ψ z :=
    ((hΨ.differentiableOn one_ne_zero) z hz).differentiableAt (isOpen_ball.mem_nhds hz)

  have hp : HasDerivAt (fun w : ℂ => (w - a) ^ n) ((n : ℂ) * (z - a) ^ (n - 1)) z := by
    have := (hasDerivAt_zpow n (z - a) (Or.inl hd)).comp z ((hasDerivAt_id z).sub_const a)
    simp at this
    exact this
  have hmodel : HasFDerivAt (fun w => (w - a) ^ n * Ψ w)
      ((z - a) ^ n • fderiv ℝ Ψ z + Ψ z • (((n : ℂ) * (z - a) ^ (n - 1)) • (1 : ℂ →L[ℝ] ℂ))) z :=
    hp.complexToReal_fderiv.mul hΨd.hasFDerivAt
  have hev : Φ =ᶠ[𝓝 z] fun w => (w - a) ^ n * Ψ w := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hΦ w hw
  have hΦd : HasFDerivAt Φ _ z := hmodel.congr_of_eventuallyEq hev
  rw [hΦd.fderiv, hΦ z hz, fderiv_Ψ_eq hΨ hΨ1 hΨa hz]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  have hp' : (z - a) ^ (n - 1) = (z - a) ^ n / (z - a) := by
    rw [zpow_sub_one₀ hd, div_eq_mul_inv]
  rw [hp']
  have hzn : (z - a) ^ n ≠ 0 := zpow_ne_zero _ hd
  field_simp
  ring

include hΨ hΨ1 hΨa hΦ in
theorem Φ_ne {z : ℂ} (hz : z ∈ ball a r) (hza : z ≠ a) : Φ z ≠ 0 := by
  rw [hΦ z hz]
  exact mul_ne_zero (zpow_ne_zero _ (sub_ne_zero.2 hza)) (Ψ_ne hΨ1 hΨa hz)

include hΨ hΨ1 hΨa hΦ hE hk hks hkr in

theorem disc_identity :
    Integrable (fun z => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) ∧
    Integrable (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) +
      2 * ((n : ℂ) * E a * k a) =
    2 / π * ∫ z, E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  have hv2 : ContDiff ℝ 2 (vEk E k) := contDiff_vEk hE hk hkr
  have hv1 : ContDiff ℝ 1 (vEk E k) := hv2.of_le (by norm_num)
  have hvs : HasCompactSupport (vEk E k) := hasCompactSupport_vEk hks
  have hvt : tsupport (vEk E k) ⊆ ball a r := tsupport_vEk.trans hkr
  have hk1 : ContDiff ℝ 1 k := hk.of_le (by norm_num)
  have hLg := contDiffOn_Lg hΨ hΨ1
  have hLg' : ContinuousOn (fderiv ℝ (Lg Ψ a)) (ball a r) :=
    hLg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hLx : ContinuousOn (fun z => fderiv ℝ (Lg Ψ a) z 1) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hLy : ContinuousOn (fun z => fderiv ℝ (Lg Ψ a) z I) (ball a r) :=
    hLg'.clm_apply continuousOn_const
  have hDL : ContinuousOn (D (Lg Ψ a)) (ball a r) := by
    unfold D; exact (hLx.add (continuousOn_const.mul hLy)).div_const _
  have hE'c := continuousOn_E' hE

  set P1 : ℂ → ℂ := fun z => (z - a)⁻¹ * D (vEk E k) z with hP1
  set P2 : ℂ → ℂ := fun z => fderiv ℝ (Lg Ψ a) z 1 * fderiv ℝ (vEk E k) z I -
    fderiv ℝ (Lg Ψ a) z I * fderiv ℝ (vEk E k) z 1 with hP2
  set P3 : ℂ → ℂ := fun z => E' z * D (Lg Ψ a) z * k z with hP3
  have iP1 : Integrable P1 := integrable_inv_sub_mul a (D_continuous hv1) (D_hasCompactSupport hvs)
  obtain ⟨hvxc, hvxs, hvxt⟩ := fderiv_apply_props hv1 hvs 1
  obtain ⟨hvyc, hvys, hvyt⟩ := fderiv_apply_props hv1 hvs I
  have iP2 : Integrable P2 :=
    (integrable_mul_of_tsupport_subset isOpen_ball hLx hvyc hvys (hvyt.trans hvt)).sub
      (integrable_mul_of_tsupport_subset isOpen_ball hLy hvxc hvxs (hvxt.trans hvt))
  have iP3 : Integrable P3 :=
    integrable_mul_of_tsupport_subset isOpen_ball (hE'c.mul hDL) hk.continuous hks hkr

  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ a := by
    have : ({a}ᶜ : Set ℂ) ∈ ae (volume : Measure ℂ) := compl_mem_ae_iff.2 (measure_singleton a)
    filter_upwards [this] with z hz using hz
  have hpt1 : ∀ z, z ≠ a → E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1) =
      -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := Φ_ne hΨ hΨ1 hΨa hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP1, hP2, hP3, D_vEk hE hk hkr, fderiv_vEk hE hk hkr hz, D]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z * I + E z * n * fderiv ℝ k z I +
        (z - a) * fderiv ℝ (Lg Ψ a) z I * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      have hzv : z ∉ tsupport (vEk E k) := fun h' => hz (hvt h')
      simp only [hP1, hP2, hP3, fderiv_of_notMem_tsupport ℝ hzk, fderiv_of_notMem_tsupport ℝ hzv,
        image_eq_zero_of_notMem_tsupport hzk, D_eq_zero_of_notMem_tsupport hzv]
      simp
  have hpt2 : ∀ z, z ≠ a →
      E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) = P3 z := by
    intro z hza
    by_cases hz : z ∈ ball a r
    · have hΦz : Φ z ≠ 0 := Φ_ne hΨ hΨ1 hΨa hΦ hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      have h1 := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza 1
      have hI := fderiv_Φ_div hΨ hΨ1 hΨa hΦ hz hza I
      rw [div_eq_iff hΦz] at h1 hI
      simp only [hP3, D]
      rw [h1, hI]
      have hII : I * I = -1 := Complex.I_mul_I
      field_simp
      linear_combination ((n : ℂ) * k z * E' z) * hII
    · have hzk : z ∉ tsupport k := fun h' => hz (hkr h')
      simp only [hP3, image_eq_zero_of_notMem_tsupport hzk]
      simp
  have hae1 : (fun z => E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ k z I - fderiv ℝ Φ z I * fderiv ℝ k z 1)) =ᵐ[volume]
      fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := by
    filter_upwards [hae] with z hz using hpt1 z hz
  have hae2 : (fun z => E' z * k z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) =ᵐ[volume]
      P3 := by
    filter_upwards [hae] with z hz using hpt2 z hz
  have iA1 : Integrable fun z => -2 * I * n * P1 z := iP1.const_mul _
  have iA : Integrable fun z => -2 * I * n * P1 z + P2 z := iA1.add iP2
  have iB : Integrable fun z => 2 * I * P3 z := iP3.const_mul _
  have iRHS : Integrable fun z => -2 * I * n * P1 z + P2 z - 2 * I * P3 z := iA.sub iB
  refine ⟨iRHS.congr hae1.symm, iP3.congr hae2.symm, ?_⟩
  rw [integral_congr_ae hae1, integral_congr_ae hae2, integral_sub iA iB, integral_add iA1 iP2,
    integral_const_mul, integral_const_mul]

  have vP1 : ∫ z, P1 z = -π * (E a * k a) := by
    have := Complex.integral_inv_sub_mul_dbar_eq_neg_pi_mul a (vEk E k) hv1 hvs
    simpa [hP1, D, vEk] using this
  have vP2 : ∫ z, P2 z = 0 := integral_wedge_eq_zero isOpen_ball hLg hv2 hvs hvt
  rw [vP1, vP2]
  have hI : I * I = -1 := Complex.I_mul_I
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  linear_combination (2 * (n : ℂ) * (E a * k a) * π - 2 * ∫ z, P3 z) * hI

end Disc

section Global

variable {U : Set ℂ} (hU : IsOpen U) {Φ : ℂ → ℂ} {n : ℂ → ℤ}
  (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
    Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)

include hloc in

theorem n_eq_zero_of_continuousAt {a : ℂ} (ha : a ∈ U) (hc : ContinuousAt Φ a) (hΦa : Φ a ≠ 0) :
    n a = 0 := by
  obtain ⟨Ψ, hΨ, hΨ0, hev⟩ := hloc a ha
  rcases lt_trichotomy (n a) 0 with hlt | heq | hgt
  ·
    exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -n a = (m : ℤ) := ⟨(-n a).toNat, by omega⟩
    have hm0 : 0 < m := by omega
    have hev' : Ψ =ᶠ[𝓝[≠] a] fun z => (z - a) ^ m * Φ z := by
      have h1 : ∀ᶠ z in 𝓝[≠] a, Φ z = (z - a) ^ (n a) * Ψ z :=
        mem_nhdsWithin_of_mem_nhds hev
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hza
      have hd : z - a ≠ 0 := sub_ne_zero.2 hza
      rw [hz, ← mul_assoc, ← zpow_natCast, ← hm, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_mul]
    have hT : Tendsto (fun z => (z - a) ^ m * Φ z) (𝓝[≠] a) (𝓝 (0 * Φ a)) := by
      refine Tendsto.mul ?_ (hc.tendsto.mono_left nhdsWithin_le_nhds)
      have : Tendsto (fun z : ℂ => (z - a) ^ m) (𝓝 a) (𝓝 ((a - a) ^ m)) :=
        ((continuous_id.sub continuous_const).pow m).continuousAt.tendsto
      rw [sub_self, zero_pow hm0.ne'] at this
      exact this.mono_left nhdsWithin_le_nhds
    rw [zero_mul] at hT
    have hΨT : Tendsto Ψ (𝓝[≠] a) (𝓝 (Ψ a)) := hΨ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact hΨ0 (tendsto_nhds_unique hΨT (hT.congr' hev'.symm))
  · exact heq
  · exfalso
    have := hev.self_of_nhds
    simp only [sub_self, zero_zpow _ hgt.ne', zero_mul] at this
    exact hΦa this

include hloc in

theorem exists_disc {τ : ℂ} (hτ : τ ∈ U) (hUn : U ∈ 𝓝 τ) :
    ∃ r : ℝ, ∃ Ψ : ℂ → ℂ, 0 < r ∧ ball τ r ⊆ U ∧ ContDiffOn ℝ 1 Ψ (ball τ r) ∧
      (∀ z ∈ ball τ r, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1) ∧ Ψ τ ≠ 0 ∧
      (∀ z ∈ ball τ r, Φ z = (z - τ) ^ (n τ) * Ψ z) := by
  obtain ⟨Ψ, hΨ, hΨ0, hev⟩ := hloc τ hτ
  have h1 : ∀ᶠ z in 𝓝 τ, ContDiffAt ℝ 1 Ψ z := hΨ.eventually (by simp)
  have h2 : ∀ᶠ z in 𝓝 τ, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1 := by
    have hc : ContinuousAt (fun z => Ψ z * (Ψ τ)⁻¹ - 1) τ :=
      (hΨ.continuousAt.mul continuousAt_const).sub continuousAt_const
    have h0 : ‖Ψ τ * (Ψ τ)⁻¹ - 1‖ < 1 := by rw [mul_inv_cancel₀ hΨ0]; simp
    exact hc.norm.eventually (gt_mem_nhds h0)
  have h0 : ∀ᶠ z in 𝓝 τ, z ∈ U := hUn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (((h0.and hev).and h1).and h2)
  refine ⟨r, Ψ, hr, fun z hz => (hball hz).1.1.1, fun z hz => (hball hz).1.2.contDiffWithinAt,
    fun z hz => (hball hz).2, hΨ0, fun z hz => (hball hz).1.1.2⟩

end Global

theorem tsupport_ofReal_comp (ρ : ℂ → ℝ) : tsupport (fun z => ((ρ z : ℝ) : ℂ)) = tsupport ρ := by
  simp only [tsupport]
  congr 1
  ext z
  simp

theorem main (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
  classical

  have hdisc : ∀ τ, τ ∈ U → ∃ r : ℝ, ∃ Ψ : ℂ → ℂ, 0 < r ∧ ball τ r ⊆ U ∧
      ContDiffOn ℝ 1 Ψ (ball τ r) ∧ (∀ z ∈ ball τ r, ‖Ψ z * (Ψ τ)⁻¹ - 1‖ < 1) ∧ Ψ τ ≠ 0 ∧
      (∀ z ∈ ball τ r, Φ z = (z - τ) ^ (n τ) * Ψ z) := fun τ hτ =>
    exists_disc hloc hτ (hU.mem_nhds hτ)
  choose! r Ψf hr hrU hΨf hΨ1 hΨ0 hΦf using hdisc

  have hiso : ∀ τ ∈ U, ∀ a ∈ ball τ (r τ), a ≠ τ → n a = 0 := by
    intro τ hτ a ha haτ
    have haU : a ∈ U := hrU τ hτ ha
    have hcont : ContinuousAt Φ a := by
      have hev : Φ =ᶠ[𝓝 a] fun z => (z - τ) ^ (n τ) * Ψf τ z := by
        filter_upwards [isOpen_ball.mem_nhds ha] with z hz using hΦf τ hτ z hz
      refine (ContinuousAt.congr ?_ hev.symm)
      refine ContinuousAt.mul ?_ ((hΨf τ hτ).continuousOn.continuousAt (isOpen_ball.mem_nhds ha))
      exact ((continuousAt_id.sub continuousAt_const).zpow₀ _ (Or.inl (sub_ne_zero.2 haτ)))
    have hΦa : Φ a ≠ 0 := Φ_ne (hΨf τ hτ) (hΨ1 τ hτ) (hΨ0 τ hτ) (hΦf τ hτ) ha haτ
    exact n_eq_zero_of_continuousAt hloc haU hcont hΦa

  set K := tsupport h with hK
  have hKc : IsCompact K := hsupp
  obtain ⟨t, htK, hcov⟩ := hKc.elim_nhds_subcover (fun x => ball x (r x / 2)) fun x hx =>
    ball_mem_nhds x (half_pos (hr x (hU' hx)))
  have htU : ∀ x ∈ t, x ∈ U := fun x hx => hU' (htK x hx)

  set ι := {x // x ∈ t}
  set Uc : ι → Set ℂ := fun i => ball (i : ℂ) (r i / 2) with hUc
  have hUo : ∀ i, IsOpen (Uc i) := fun i => isOpen_ball
  have hKU : K ⊆ ⋃ i, Uc i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) (isClosed_tsupport h) Uc hUo hKU
  set ρ : ι → ℂ → ℂ := fun i z => ((f i z : ℝ) : ℂ) with hρ
  have hρs : ∀ i, ContDiff ℝ 2 (ρ i) := fun i => by
    have h1 : ContDiff ℝ ∞ (f i : ℂ → ℝ) := contMDiff_iff_contDiff.1 (f i).contMDiff
    exact Complex.ofRealCLM.contDiff.comp (h1.of_le (by norm_cast))
  have hρt : ∀ i, tsupport (ρ i) ⊆ ball (i : ℂ) (r i / 2) := fun i => by
    rw [hρ, tsupport_ofReal_comp]; exact hf i
  have hρ1 : ∀ z ∈ K, ∑ i : ι, ρ i z = 1 := by
    intro z hz
    have := f.sum_eq_one hz
    rw [finsum_eq_sum_of_fintype] at this
    simp only [hρ]
    exact_mod_cast this

  set k : ι → ℂ → ℂ := fun i z => h z * ρ i z with hkdef
  have hk2 : ∀ i, ContDiff ℝ 2 (k i) := fun i => hh.mul (hρs i)
  have hks : ∀ i, HasCompactSupport (k i) := fun i => hsupp.mul_right
  have hkt : ∀ i, tsupport (k i) ⊆ ball (i : ℂ) (r i) := fun i =>
    (closure_minimal (fun z hz => subset_tsupport _ (right_ne_zero_of_mul hz))
      (isClosed_tsupport _)).trans ((hρt i).trans (ball_subset_ball (by linarith [hr i (htU i i.2)])))
  have hsum : h = ∑ i : ι, k i := by
    funext z
    rw [Finset.sum_apply]
    simp only [hkdef, ← Finset.mul_sum]
    by_cases hz : z ∈ K
    · rw [hρ1 z hz, mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

  have hD : ∀ i : ι, _ := fun i => disc_identity (hΨf i (htU i i.2)) (hΨ1 i (htU i i.2))
    (hΨ0 i (htU i i.2)) (hΦf i (htU i i.2)) (fun z hz => hE z (hrU i (htU i i.2) hz))
    (hk2 i) (hks i) (hkt i)

  have hfd : ∀ z w, fderiv ℝ h z w = ∑ i : ι, fderiv ℝ (k i) z w := by
    intro z w
    rw [hsum, fderiv_sum fun i _ => (hk2 i).differentiable (by norm_num) z]
    simp [Finset.sum_apply]
  have hhz : ∀ z, h z = ∑ i : ι, k i z := fun z => by rw [hsum, Finset.sum_apply]

  have hI1 : (fun z : ℂ => E z / Φ z *
      (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) =
      fun z => ∑ i : ι, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (k i) z I - fderiv ℝ Φ z I * fderiv ℝ (k i) z 1) := by
    funext z
    rw [hfd z I, hfd z 1, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  have hI2 : (fun z : ℂ => E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) =
      fun z => ∑ i : ι, E' z * k i z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by
    funext z
    rw [hhz z, Finset.mul_sum, Finset.sum_mul]

  have hpt : ∀ i : ι, ∑ᶠ a : ℂ, (n a : ℂ) * E a * k i a = (n i : ℂ) * E i * k i i := by
    intro i
    refine finsum_eq_single _ (i : ℂ) fun a hai => ?_
    by_cases hka : k i a = 0
    · rw [hka, mul_zero]
    · have ha : a ∈ ball (i : ℂ) (r i) := hkt i (subset_tsupport _ hka)
      rw [hiso i (htU i i.2) a ha hai]; simp
  have hfin : ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a = ∑ i : ι, (n i : ℂ) * E i * k i i := by
    have h1 : (fun a : ℂ => (n a : ℂ) * E a * h a) = fun a => ∑ i : ι, (n a : ℂ) * E a * k i a := by
      funext a; rw [hhz a, Finset.mul_sum]
    rw [h1, finsum_sum_comm]
    · exact Finset.sum_congr rfl fun i _ => hpt i
    · intro i _
      refine Set.Finite.subset (Set.finite_singleton (i : ℂ)) fun a ha => ?_
      by_contra hai
      apply ha
      show (n a : ℂ) * E a * k i a = 0
      by_cases hka : k i a = 0
      · rw [hka, mul_zero]
      · have ha' : a ∈ ball (i : ℂ) (r i) := hkt i (subset_tsupport _ hka)
        rw [hiso i (htU i i.2) a ha' hai]; simp

  refine ⟨?_, ?_, ?_⟩
  · rw [hI1]; exact integrable_finsetSum _ fun i _ => (hD i).1
  · rw [hI2]; exact integrable_finsetSum _ fun i _ => (hD i).2.1
  · rw [hI1, hI2, integral_finsetSum _ fun i _ => (hD i).1,
      integral_finsetSum _ fun i _ => (hD i).2.1, hfin, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => (hD i).2.2

end Complex.WedgeArgument

end

p2m_open "Complex P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.Complex MeasureTheory"
open scoped Real Topology

theorem solution
    (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) :=
  Complex.WedgeArgument.main U hU Φ n hloc E E' hE h hh hsupp hU'

end S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
end P2MW
export P2MW.S_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv (solution)
