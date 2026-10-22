-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_no_short_return
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-04T23:03:56.16446+00:00
-- url     : https://prove2.me/submissions/cbca1973-1ecc-48b0-b6b8-cbb2d8e2c12e

import Mathlib
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Theorems.Thm_BirkhoffGlobalSection_leviCivita_smoothAt_of_secondCollisionFree
import Theorems.Thm_BirkhoffGlobalSection_first_critical_value_near_half
import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum

namespace BirkhoffGlobalSection.NoShortReturn

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

/-- The Levi-Civita lift of the inner Lagrange point, with `x = q₁ + μ`. -/
noncomputable def eL (μ x : ℝ) : Phase :=
  ![Real.sqrt (x / 2), 0, 0, Real.sqrt (x / 2) * (μ - x)]

/-- Minus the Jacobi energy of the inner Lagrange point. -/
noncomputable def cStar (μ x : ℝ) : ℝ := (x - μ) ^ 2 / 2 + (1 - μ) / x + μ / (1 - x)

theorem axis_equation (μ : ℝ) {L : Phase} (hcrit : isCriticalPoint (jacobiHamiltonian μ) L)
    (hL1 : L 1 = 0) (hL2 : L 2 = 0) (hL3 : L 3 = -L 0)
    (hx0 : 0 < L 0 + μ) (hx1 : L 0 + μ < 1) :
    -L 0 + (1 - μ) / (L 0 + μ) ^ 2 - μ / (1 - (L 0 + μ)) ^ 2 = 0 := by
  set x := L 0 + μ with hx
  let ℓ : ℝ → Phase := fun t => ![L 0 + t, 0, 0, -L 0]
  have hℓ0 : ℓ 0 = L := by
    funext i; fin_cases i <;> simp [ℓ, hL1, hL2, hL3]
  have hℓ : HasDerivAt ℓ ![1, 0, 0, 0] 0 := by
    rw [hasDerivAt_pi]
    intro i
    fin_cases i
    · simpa [ℓ] using (hasDerivAt_id' (0 : ℝ)).const_add (L 0)
    · simpa [ℓ] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [ℓ] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa [ℓ] using hasDerivAt_const (0 : ℝ) (-L 0)
  have hH : HasFDerivAt (jacobiHamiltonian μ) (0 : Phase →L[ℝ] ℝ) (ℓ 0) := by
    rw [hℓ0, ← hcrit.2]; exact hcrit.1.hasFDerivAt
  have h1 := hH.comp_hasDerivAt (0 : ℝ) hℓ
  simp only [zero_apply] at h1
  -- explicit form near 0
  let F : ℝ → ℝ := fun t =>
    L 0 ^ 2 / 2 - (L 0 + t) * L 0 - (1 - μ) / (x + t) - μ / (1 - x - t)
  have hxt : x + 0 ≠ 0 := by simp; linarith
  have hyt : 1 - x - 0 ≠ 0 := by simp; linarith
  have hF : HasDerivAt F (-L 0 + (1 - μ) / x ^ 2 - μ / (1 - x) ^ 2) 0 := by
    have ha := ((hasDerivAt_id' (0 : ℝ)).const_add x).inv hxt
    have hb := ((hasDerivAt_id' (0 : ℝ)).const_sub (1 - x)).inv hyt
    have hc := ((hasDerivAt_id' (0 : ℝ)).const_add (L 0)).mul_const (L 0)
    have := (((hasDerivAt_const (0 : ℝ) (L 0 ^ 2 / 2)).sub hc).sub (ha.const_mul (1 - μ))).sub
      (hb.const_mul μ)
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    · simp only [add_zero, sub_zero]; ring
    · simp only [F, Pi.sub_apply, Pi.inv_apply, div_eq_mul_inv]
  have heq : (jacobiHamiltonian μ ∘ ℓ) =ᶠ[𝓝 0] F := by
    have hm : 0 < min x (1 - x) := lt_min hx0 (by linarith)
    have hnb : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < x + t ∧ 0 < 1 - x - t := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hm] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      have h1 := abs_lt.mp ht
      have := min_le_left x (1 - x); have := min_le_right x (1 - x)
      constructor <;> linarith [h1.1, h1.2]
    filter_upwards [hnb] with t ht
    simp only [Function.comp, jacobiHamiltonian, ℓ, F]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    have e1 : Real.sqrt ((L 0 + t + μ) ^ 2 + 0 ^ 2) = x + t := by
      rw [show (L 0 + t + μ) ^ 2 + (0 : ℝ) ^ 2 = (x + t) ^ 2 by rw [hx]; ring]
      exact Real.sqrt_sq ht.1.le
    have e2 : Real.sqrt ((L 0 + t - 1 + μ) ^ 2 + 0 ^ 2) = 1 - x - t := by
      rw [show (L 0 + t - 1 + μ) ^ 2 + (0 : ℝ) ^ 2 = (1 - x - t) ^ 2 by rw [hx]; ring]
      exact Real.sqrt_sq ht.2.le
    rw [e1, e2]; ring
  have h2 := hF.congr_of_eventuallyEq heq
  have := h1.unique h2
  linarith

/-- Data of the inner Lagrange point: `x = q₁ + μ ∈ (0,1)` solves the axis equation and the
first critical value is `-cStar μ x`. -/
theorem lagrange_data (μ : ℝ) (h0 : 0 < μ) (h1 : μ < 1) :
    ∃ x : ℝ, 0 < x ∧ x < 1 ∧
      x - μ - (1 - μ) / x ^ 2 + μ / (1 - x) ^ 2 = 0 ∧
      firstCriticalValue μ = -cStar μ x := by
  obtain ⟨L, ⟨_, hcrit, hlo, hhi, hL1⟩, hHL⟩ := inner_lagrange_realizes_first_critical_value μ h0 h1
  obtain ⟨hL2, hL3⟩ := jacobi_critical_momentum μ L hcrit
  rw [hL1] at hL2
  have hx0 : 0 < L 0 + μ := by linarith
  have hx1 : L 0 + μ < 1 := by linarith
  have hax := axis_equation μ hcrit hL1 hL2 hL3 hx0 hx1
  refine ⟨L 0 + μ, hx0, hx1, by linarith, ?_⟩
  rw [← hHL]
  simp only [jacobiHamiltonian, cStar, hL1, hL2, hL3]
  have e1 : Real.sqrt ((L 0 + μ) ^ 2 + 0 ^ 2) = L 0 + μ := by
    rw [show (L 0 + μ) ^ 2 + (0 : ℝ) ^ 2 = (L 0 + μ) ^ 2 by ring]; exact Real.sqrt_sq hx0.le
  have e2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + 0 ^ 2) = 1 - (L 0 + μ) := by
    rw [show (L 0 - 1 + μ) ^ 2 + (0 : ℝ) ^ 2 = (1 - (L 0 + μ)) ^ 2 by ring]
    exact Real.sqrt_sq (by linarith)
  rw [e1, e2]; ring

theorem x_near_half {μ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1)
    (hf : x - μ - (1 - μ) / x ^ 2 + μ / (1 - x) ^ 2 = 0) (h0 : 0 < μ) (h1 : μ < 1) :
    |x - 1 / 2| ≤ 7 * |μ - 1 / 2| := by
  have hy : 0 < 1 - x := by linarith
  rcases le_total (1 / 2) x with hx | hx
  · have hx2 : 1 / 4 ≤ x ^ 2 := by nlinarith
    have hy2 : (1 - x) ^ 2 ≤ 1 / 4 := by nlinarith
    have a1 : (1 - μ) / x ^ 2 ≤ 4 * (1 - μ) := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0:ℝ) ≤ 1 - μ)]
    have a2 : 4 * μ ≤ μ / (1 - x) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hy2 h0.le]
    rw [abs_of_nonneg (by linarith)]
    have := le_abs_self (-(μ - 1 / 2)); rw [abs_neg] at this; linarith
  · have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
    have hy2 : 1 / 4 ≤ (1 - x) ^ 2 := by nlinarith
    have a1 : 4 * (1 - μ) ≤ (1 - μ) / x ^ 2 := by
      rw [le_div_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hx2 (by linarith : (0:ℝ) ≤ 1 - μ)]
    have a2 : μ / (1 - x) ^ 2 ≤ 4 * μ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_le_mul_of_nonneg_left hy2 h0.le]
    rw [abs_of_nonpos (by linarith)]
    have := le_abs_self (μ - 1 / 2); linarith

theorem sqrt_half_sq {x : ℝ} (hx : 0 < x) : Real.sqrt (x / 2) ^ 2 = x / 2 :=
  Real.sq_sqrt (by positivity)

theorem D_eL {μ x : ℝ} (hx : 0 < x) : secondCollisionDistanceSq (eL μ x) = (1 - x) ^ 2 := by
  have h := sqrt_half_sq hx
  simp only [secondCollisionDistanceSq, eL, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  nlinarith [h]

theorem eL_mem {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) : eL μ x ∈ U := by
  show (0 : ℝ) < _; rw [D_eL hx]; nlinarith

theorem rD_eL {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) : rD (eL μ x) = 1 - x := by
  rw [rD, D_eL hx]; exact Real.sqrt_sq (by linarith)

theorem kGrad_eL {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hf : x - μ - (1 - μ) / x ^ 2 + μ / (1 - x) ^ 2 = 0) :
    kGrad μ (cStar μ x) (eL μ x) = 0 := by
  have hz := sqrt_half_sq hx
  set z := Real.sqrt (x / 2) with hzdef
  have hy : 1 - x ≠ 0 := by linarith
  have hxne : x ≠ 0 := hx.ne'
  funext i
  simp only [kGrad, rD_eL hx hx1]
  fin_cases i <;>
    simp only [kGradR, dP, dZ, dD, zNormSq, eL, cStar, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Pi.zero_apply, ← hzdef]
  · have hz3 : z ^ 3 = z * (x / 2) := by rw [← hz]; ring
    have ha : x * x⁻¹ = 1 := mul_inv_cancel₀ hxne
    have hb : (1 - x) * (1 - x)⁻¹ = 1 := mul_inv_cancel₀ hy
    simp only [div_eq_mul_inv, mul_inv, ← inv_pow] at hf ⊢
    linear_combination (-2 * x * z) * hf + (2 * x⁻¹ * z * (μ - 1)) * ha
      + (-4 * (1 - x)⁻¹ ^ 2 * μ * z ^ 3) * hb
      + (-2 * z * (-4 * (1 - x)⁻¹ ^ 3 * μ * z ^ 2 + 2 * (1 - x)⁻¹ ^ 2 * μ - 3 * μ + 3 * x)) * hz
  · ring
  · ring
  · have hz3 : z ^ 3 = z * (x / 2) := by rw [← hz]; ring
    rw [hz3]; ring

theorem K_eL {μ x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    leviCivitaHamiltonian μ (cStar μ x) (eL μ x) = 0 := by
  have hz := sqrt_half_sq hx
  have hr : Real.sqrt (secondCollisionDistanceSq (eL μ x)) = 1 - x := rD_eL hx hx1
  simp only [leviCivitaHamiltonian, hr]
  simp only [wNormSq, zNormSq, eL, cStar, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  set z := Real.sqrt (x / 2)
  have hy : 1 - x ≠ 0 := by linarith
  field_simp
  ring_nf
  rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hz]
  ring


/-- The explicit gradient as a function of parameters and state. -/
noncomputable def Gq (q : ℝ × ℝ × Phase) : Phase := kGradR q.1 q.2.1 (rD q.2.2) q.2.2

/-- The Hessian at the saddle-centers, as a linear action. -/
def H0act (v : Phase) : Phase := ![-16 * v 0 + v 3, 8 * v 1 - v 2, -v 1 + v 2, v 0 + v 3]

/-- The slice embedding `y ↦ (0, 0, y)`. -/
noncomputable def iota : Phase →L[ℝ] ℝ × ℝ × Phase :=
  (ContinuousLinearMap.inr ℝ ℝ (ℝ × Phase)).comp (ContinuousLinearMap.inr ℝ ℝ Phase)

theorem iota_apply (v : Phase) : iota v = ((0 : ℝ), (0 : ℝ), v) := rfl

theorem norm_iota_le : ‖iota‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [iota_apply, Prod.norm_def, Prod.norm_def]; simp

theorem hasFDerivAt_slice (μ c : ℝ) (y : Phase) :
    HasFDerivAt (fun y : Phase => ((μ, c, y) : ℝ × ℝ × Phase)) iota y := by
  have e : (fun y : Phase => ((μ, c, y) : ℝ × ℝ × Phase)) = fun y => ((μ, c, 0) : ℝ × ℝ × Phase) + iota y := by
    funext y; simp [iota_apply]
  rw [e]; exact iota.hasFDerivAt.const_add _

theorem contDiffAt_kGradR' (i : Fin 4) {p : ℝ × ℝ × ℝ × Phase} (hp : p.2.2.1 ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) p := by
  have h3 : p.2.2.1 ^ 3 ≠ 0 := pow_ne_zero 3 hp
  fin_cases i <;>
    simp only [kGradR, dP, dZ, dD, zNormSq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop (disch := first | assumption | exact mul_ne_zero two_ne_zero h3)

theorem contDiffAt_rD {y : Phase} (hy : y ∈ U) : ContDiffAt ℝ 1 rD y := by
  unfold rD
  refine ContDiffAt.sqrt ?_ (show (0 : ℝ) < secondCollisionDistanceSq y from hy).ne'
  unfold secondCollisionDistanceSq; fun_prop

theorem contDiffAt_Gq {q : ℝ × ℝ × Phase} (hq : q.2.2 ∈ U) : ContDiffAt ℝ 1 Gq q := by
  have hr : ContDiffAt ℝ 1 (fun q : ℝ × ℝ × Phase => (q.1, q.2.1, rD q.2.2, q.2.2)) q := by
    have := (contDiffAt_rD hq).comp q
      (contDiffAt_snd.comp q contDiffAt_snd :
        ContDiffAt ℝ 1 (fun q : ℝ × ℝ × Phase => q.2.2) q)
    fun_prop
  have hr0 : rD q.2.2 ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  rw [contDiffAt_pi]
  intro i
  have := ContDiffAt.comp
    (g := fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) q
    (contDiffAt_kGradR' i (p := (q.1, q.2.1, rD q.2.2, q.2.2)) hr0) hr
  exact this

theorem isOpen_U' : IsOpen U :=
  isOpen_lt continuous_const (by unfold secondCollisionDistanceSq; fun_prop)

theorem coord_expand (φ : Phase →L[ℝ] ℝ) (u : Phase) :
    φ u = ∑ i, u i * φ (coordinateVector i) := by
  have hu : u = ∑ i, u i • coordinateVector i := by
    funext j
    simp [coordinateVector, Finset.sum_apply]
  conv_lhs => rw [hu]
  simp [map_sum, map_smul, smul_eq_mul]

/-- The `y`-derivative of the gradient at `(1/2, 2, s)` is the Hessian `kHess (1/2) 2 s`. -/
theorem slice_deriv_apply (s : Phase) (hs : s ∈ U) (v : Phase) (i : Fin 4) :
    ((fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), s)).comp iota) v i =
      ∑ l, v l * kHess (1 / 2) 2 s i l := by
  have hG := (contDiffAt_Gq (q := ((1 / 2 : ℝ), (2 : ℝ), s)) hs).differentiableAt (by norm_num)
  have hcomp : HasFDerivAt (kGrad (1 / 2) 2)
      ((fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), s)).comp iota) s := by
    have := HasFDerivAt.comp (g := Gq) s hG.hasFDerivAt (hasFDerivAt_slice (1 / 2) 2 s)
    exact this
  have hi := (hasFDerivAt_pi'.1 hcomp) i
  have hev : (fun y => kGrad (1 / 2) 2 y i) =ᶠ[𝓝 s]
      fun y => fderiv ℝ (leviCivitaHamiltonian (1 / 2) 2) y (coordinateVector i) := by
    filter_upwards [isOpen_U'.mem_nhds hs] with y hy
    rw [← (leviCivita_explicit_derivatives (1 / 2) 2).1 y hy i]; rfl
  have h2 := (leviCivita_explicit_derivatives (1 / 2) 2).2.1 s hs (coordinateVector i) v
  rw [← hev.fderiv_eq, hi.fderiv] at h2
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply] at h2
  show (fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), s)) (iota v) i = _
  rw [h2]
  simp [coordinateVector, Finset.sum_ite_eq', ite_mul]

/-- Uniform linearization of the gradient near `(1/2, 2, s)`. -/
theorem grad_linearization (s : Phase) (hs : s ∈ U)
    (hH : ∀ v : Phase, ((fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), s)).comp iota) v = H0act v)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ μ c : ℝ, |μ - 1 / 2| < δ → |c - 2| < δ →
      (∀ y : Phase, ‖y - s‖ < δ → y ∈ U) ∧
      ∀ y y' : Phase, ‖y - s‖ < δ → ‖y' - s‖ < δ →
        ‖Gq (μ, c, y) - Gq (μ, c, y') - H0act (y - y')‖ ≤ η * ‖y - y'‖ := by
  set q0 : ℝ × ℝ × Phase := ((1 / 2 : ℝ), (2 : ℝ), s)
  have hG := contDiffAt_Gq (q := q0) hs
  have hcont : ContinuousAt (fderiv ℝ Gq) q0 :=
    (hG.fderiv_right (m := 0) (by norm_num)).continuousAt
  have hev : ∀ᶠ q in 𝓝 q0, ContDiffAt ℝ 1 Gq q := hG.eventually (by simp)
  have hU : ∀ᶠ q in 𝓝 q0, q.2.2 ∈ U :=
    (continuous_snd.comp continuous_snd).continuousAt.preimage_mem_nhds (isOpen_U'.mem_nhds hs)
  have hη' : ∀ᶠ q in 𝓝 q0, ‖fderiv ℝ Gq q - fderiv ℝ Gq q0‖ < η := by
    have := hcont.eventually (Metric.ball_mem_nhds _ hη)
    filter_upwards [this] with q hq
    simpa [dist_eq_norm] using hq
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp ((hev.and hU).and hη')
  refine ⟨δ, hδ, fun μ c hμ hc => ?_⟩
  have hq : ∀ y : Phase, ‖y - s‖ < δ → dist ((μ, c, y) : ℝ × ℝ × Phase) q0 < δ := by
    intro y hy
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt hμ (max_lt hc hy)
  refine ⟨fun y hy => (hall (hq y hy)).1.2, fun y y' hy hy' => ?_⟩
  set A := (fderiv ℝ Gq q0).comp iota
  let ψ : Phase → Phase := fun z => Gq (μ, c, z) - A z
  have hψ : ∀ z ∈ Metric.ball s δ,
      HasFDerivWithinAt ψ ((fderiv ℝ Gq (μ, c, z)).comp iota - A) (Metric.ball s δ) z := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hd := ((hall (hq z hz)).1.1.differentiableAt (by norm_num)).hasFDerivAt
    exact ((hd.comp z (hasFDerivAt_slice μ c z)).sub A.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.ball s δ, ‖(fderiv ℝ Gq (μ, c, z)).comp iota - A‖ ≤ η := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h3 := (hall (hq z hz)).2
    rw [show (fderiv ℝ Gq (μ, c, z)).comp iota - A = (fderiv ℝ Gq (μ, c, z) - fderiv ℝ Gq q0).comp iota
      by ext; simp [A]]
    calc ‖(fderiv ℝ Gq (μ, c, z) - fderiv ℝ Gq q0).comp iota‖
        ≤ ‖fderiv ℝ Gq (μ, c, z) - fderiv ℝ Gq q0‖ * ‖iota‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ η * 1 := mul_le_mul h3.le norm_iota_le (norm_nonneg _) hη.le
      _ = η := mul_one η
  have hmv := (convex_ball s δ).norm_image_sub_le_of_norm_hasFDerivWithin_le hψ hbound
    (by rw [Metric.mem_ball, dist_eq_norm]; exact hy') (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)
  have e : ψ y - ψ y' = Gq (μ, c, y) - Gq (μ, c, y') - H0act (y - y') := by
    simp only [ψ, ← hH, map_sub]; abel
  rw [← e]; exact hmv



/-! ### Values at the saddle-centers -/

theorem D_sP : secondCollisionDistanceSq (![1 / 2, 0, 0, 0] : Phase) = 1 / 4 := by
  simp [secondCollisionDistanceSq]; norm_num

theorem D_sM : secondCollisionDistanceSq (![-(1 / 2), 0, 0, 0] : Phase) = 1 / 4 := by
  simp [secondCollisionDistanceSq]; norm_num

theorem sP_mem : (![1 / 2, 0, 0, 0] : Phase) ∈ U := by
  show (0 : ℝ) < _; rw [D_sP]; norm_num

theorem sM_mem : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U := by
  show (0 : ℝ) < _; rw [D_sM]; norm_num

theorem rD_quarter {s : Phase} (h : secondCollisionDistanceSq s = 1 / 4) : rD s = 1 / 2 := by
  rw [rD, h, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem hess_sP (v : Phase) :
    ((fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), ![1 / 2, 0, 0, 0])).comp iota) v = H0act v := by
  funext i
  rw [slice_deriv_apply _ sP_mem, kHess, rD_quarter D_sP]
  fin_cases i <;>
    simp [Fin.sum_univ_four, kHessR, hP, hZ, hD, dZ, dD, zNormSq, H0act] <;> ring

theorem hess_sM (v : Phase) :
    ((fderiv ℝ Gq ((1 / 2 : ℝ), (2 : ℝ), ![-(1 / 2), 0, 0, 0])).comp iota) v = H0act v := by
  funext i
  rw [slice_deriv_apply _ sM_mem, kHess, rD_quarter D_sM]
  fin_cases i <;>
    simp [Fin.sum_univ_four, kHessR, hP, hZ, hD, dZ, dD, zNormSq, H0act] <;> ring

/-! ### Affine dependence on `c`, symmetry -/

theorem K_affine (μ c c' : ℝ) (y : Phase) :
    leviCivitaHamiltonian μ c y = leviCivitaHamiltonian μ c' y + (c - c') * zNormSq y := by
  unfold leviCivitaHamiltonian; ring

theorem Gq_affine (μ c c' : ℝ) (y : Phase) :
    Gq (μ, c, y) = Gq (μ, c', y) + (c - c') • dZ y := by
  funext i
  fin_cases i <;> simp [Gq, kGradR, dP, dZ] <;> (try ring)

theorem D_neg (y : Phase) : secondCollisionDistanceSq (-y) = secondCollisionDistanceSq y := by
  simp only [secondCollisionDistanceSq, Pi.neg_apply]; ring

theorem K_neg (μ c : ℝ) (y : Phase) :
    leviCivitaHamiltonian μ c (-y) = leviCivitaHamiltonian μ c y := by
  unfold leviCivitaHamiltonian; rw [D_neg]; simp [wNormSq, zNormSq]

theorem Gq_neg (μ c : ℝ) (y : Phase) : Gq (μ, c, -y) = -Gq (μ, c, y) := by
  have hr : rD (-y) = rD y := by rw [rD, rD, D_neg]
  funext i
  simp only [Gq, hr]
  fin_cases i <;> simp [kGradR, dP, dZ, dD, zNormSq] <;> ring

/-! ### Gradient along a line and the Taylor lower bound -/

theorem fderivK_apply (μ c : ℝ) {y : Phase} (hy : y ∈ U) (u : Phase) :
    fderiv ℝ (leviCivitaHamiltonian μ c) y u = ∑ i, u i * Gq (μ, c, y) i := by
  rw [coord_expand]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact (leviCivita_explicit_derivatives μ c).1 y hy i

/-- `qH u = uᵀ H₀ u`. -/
def qH (u : Phase) : ℝ := ∑ i, u i * H0act u i

theorem H0act_smul (t : ℝ) (u : Phase) : H0act (t • u) = t • H0act u := by
  funext i; fin_cases i <;> simp [H0act] <;> ring

theorem abs_dot_le (u v : Phase) : |∑ i, u i * v i| ≤ 4 * (‖u‖ * ‖v‖) := by
  have h : ∀ i, |u i * v i| ≤ ‖u‖ * ‖v‖ := fun i => by
    rw [abs_mul]
    exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i) (abs_nonneg _) (norm_nonneg _)
  calc |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun i _ => h i
    _ = 4 * (‖u‖ * ‖v‖) := by simp

theorem taylor_lower {s e u : Phase} {μ c η δ : ℝ} (hη : 0 ≤ η)
    (hUδ : ∀ y : Phase, ‖y - s‖ < δ → y ∈ U)
    (hlin : ∀ y y' : Phase, ‖y - s‖ < δ → ‖y' - s‖ < δ →
      ‖Gq (μ, c, y) - Gq (μ, c, y') - H0act (y - y')‖ ≤ η * ‖y - y'‖)
    (he : ‖e - s‖ < δ) (heu : ‖e + u - s‖ < δ)
    (hG0 : Gq (μ, c, e) = 0) (hK0 : leviCivitaHamiltonian μ c e = 0) :
    qH u - 4 * η * ‖u‖ ^ 2 ≤ 2 * leviCivitaHamiltonian μ c (e + u) := by
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖e + t • u - s‖ < δ := by
    intro t ht
    have : e + t • u - s = (1 - t) • (e - s) + t • (e + u - s) := by
      funext i; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    calc ‖(1 - t) • (e - s) + t • (e + u - s)‖
        ≤ ‖(1 - t) • (e - s)‖ + ‖t • (e + u - s)‖ := norm_add_le _ _
      _ = (1 - t) * ‖e - s‖ + t * ‖e + u - s‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith [ht.2]),
            Real.norm_of_nonneg ht.1]
      _ < δ := by
          rcases eq_or_lt_of_le ht.1 with h0 | h0
          · subst h0; simpa using he
          · nlinarith [ht.2]
  set a := qH u - 4 * η * ‖u‖ ^ 2 with ha
  let g : ℝ → ℝ := fun t => leviCivitaHamiltonian μ c (e + t • u)
  let φ : ℝ → ℝ := fun t => g t - t ^ 2 / 2 * a
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt g (∑ i, u i * Gq (μ, c, e + t • u) i) t := by
    intro t ht
    have hyU := hUδ _ (hseg t ht)
    have hK := ((leviCivita_smoothAt_of_secondCollisionFree μ c _ hyU).differentiableAt
      (by simp)).hasFDerivAt
    have hl : HasDerivAt (fun t : ℝ => e + t • u) u t := by
      simpa using ((hasDerivAt_id t).smul_const u).const_add e
    have := hK.comp_hasDerivAt t hl
    rw [fderivK_apply μ c hyU] at this
    exact this
  have hφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt φ (∑ i, u i * Gq (μ, c, e + t • u) i - t * a) t := by
    intro t ht
    have := (hg t ht).sub (((hasDerivAt_pow 2 t).div_const 2).mul_const a)
    refine this.congr_deriv ?_
    simp only [Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one]; ring
  have hφ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ∑ i, u i * Gq (μ, c, e + t • u) i - t * a := by
    intro t ht
    have hl := hlin _ _ (hseg t ht) he
    rw [hG0, sub_zero, show e + t • u - e = t • u by abel, H0act_smul, norm_smul,
      Real.norm_of_nonneg ht.1] at hl
    set err := Gq (μ, c, e + t • u) - t • H0act u with herr
    have hsplit : ∑ i, u i * Gq (μ, c, e + t • u) i = t * qH u + ∑ i, u i * err i := by
      simp only [qH, herr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    have hb := abs_dot_le u err
    have hb2 : ‖u‖ * ‖err‖ ≤ ‖u‖ * (η * (t * ‖u‖)) := mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    rw [hsplit, ha]
    have := (abs_le.mp hb).1
    nlinarith [ht.1]
  have hmono : MonotoneOn φ (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (hφ t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hφ t (interior_subset ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by rw [(hφ t (interior_subset ht)).deriv]; exact hφ' t (interior_subset ht))
  have h01 := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [φ, g, zero_smul, add_zero, one_smul, hK0] at h01
  linarith

/-! ### The Lyapunov inequality -/

theorem lin2 (a b x y N : ℝ) (hx : |x| ≤ N) (hy : |y| ≤ N) :
    |a * x + b * y| ≤ (|a| + |b|) * N := by
  calc |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
    _ = |a| * |x| + |b| * |y| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * N + |b| * N := add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = (|a| + |b|) * N := by ring

theorem prod_bound {p e c N η : ℝ} (hp : |p| ≤ c * N) (he : |e| ≤ η * N) (hc : 0 ≤ c)
    (hN : 0 ≤ N) : -(c * η * N ^ 2) ≤ p * e := by
  have : |p * e| ≤ c * N * (η * N) := by
    rw [abs_mul]; exact mul_le_mul hp he (abs_nonneg _) (by positivity)
  have := (abs_le.mp this).1; nlinarith

set_option maxHeartbeats 2000000 in
/-- The derivative of `Q(y - e)` along the field is positive. Here `g = H₀u + ε + κ dZ`. -/
theorem lyap_alg (u0 u1 u2 u3 e0 e1 e2 e3 y0 y1 κ η N : ℝ) (hN : 0 < N)
    (hu0 : |u0| ≤ N) (hu1 : |u1| ≤ N) (hu2 : |u2| ≤ N) (hu3 : |u3| ≤ N)
    (hN2 : N ^ 2 ≤ u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2)
    (he0 : |e0| ≤ η * N) (he1 : |e1| ≤ η * N) (he2 : |e2| ≤ η * N) (he3 : |e3| ≤ η * N)
    (hκ : 0 ≤ κ) (hκs : κ ≤ 1 / 100) (hη : 0 ≤ η) (hηs : η ≤ 1 / 100)
    (hlev : u0 * (-16 * u0 + u3) + u1 * (8 * u1 - u2) + u2 * (-u1 + u2) + u3 * (u0 + u3)
      ≤ 4 * η * N ^ 2 - 2 * κ * (y0 ^ 2 + y1 ^ 2)) :
    0 < 2 * ((-7 / 2 * u1 + 10 * u2) * (-u1 + u2 + e2) + (-7 / 2 * u0 + 1 / 4 * u3) * (u0 + u3 + e3)
      + (10 * u0 - 3 / 4 * u3) * (-(-16 * u0 + u3 + e0 + κ * (2 * y0))) + (1 / 4 * u1 - 3 / 4 * u2) * (-(8 * u1 - u2 + e1 + κ * (2 * y1)))) := by
  -- linear part
  have hM : 8 * (u0 ^ 2 + u1 ^ 2 + u2 ^ 2 + u3 ^ 2) ≤
      185 * u0 ^ 2 - 69 / 2 * u0 * u3 + 10 * u3 ^ 2 + 67 * u1 ^ 2 - 61 / 2 * u1 * u2
        + 53 / 2 * u2 ^ 2 := by
    nlinarith [sq_nonneg (u3 - 69 / 8 * u0), sq_nonneg (u2 - 61 / 74 * u1), sq_nonneg u0,
      sq_nonneg u1]
  -- error part
  have hp2 : |-7 / 2 * u1 + 10 * u2| ≤ 27 / 2 * N := by
    have := lin2 (-7 / 2) 10 u1 u2 N hu1 hu2; norm_num at this ⊢; linarith
  have hp3 : |-7 / 2 * u0 + 1 / 4 * u3| ≤ 15 / 4 * N := by
    have := lin2 (-7 / 2) (1 / 4) u0 u3 N hu0 hu3; norm_num at this ⊢; linarith
  have hp0 : |10 * u0 - 3 / 4 * u3| ≤ 43 / 4 * N := by
    have := lin2 10 (-3 / 4) u0 u3 N hu0 hu3
    rw [show 10 * u0 + -3 / 4 * u3 = 10 * u0 - 3 / 4 * u3 by ring] at this
    norm_num at this ⊢; linarith
  have hp1 : |1 / 4 * u1 - 3 / 4 * u2| ≤ 1 * N := by
    have := lin2 (1 / 4) (-3 / 4) u1 u2 N hu1 hu2
    rw [show 1 / 4 * u1 + -3 / 4 * u2 = 1 / 4 * u1 - 3 / 4 * u2 by ring] at this
    norm_num at this ⊢; linarith
  have hNn := hN.le
  have b2 := prod_bound hp2 he2 (by norm_num) hNn
  have b3 := prod_bound hp3 he3 (by norm_num) hNn
  have b0 := prod_bound (p := -(10 * u0 - 3 / 4 * u3)) (by rwa [abs_neg]) he0 (by norm_num) hNn
  have b1 := prod_bound (p := -(1 / 4 * u1 - 3 / 4 * u2)) (by rwa [abs_neg]) he1 (by norm_num) hNn
  -- κ part
  have k0 : (10 * u0 - 3 / 4 * u3) * y0 ≤ 43 / 4 * N * |y0| := by
    calc (10 * u0 - 3 / 4 * u3) * y0 ≤ |(10 * u0 - 3 / 4 * u3) * y0| := le_abs_self _
      _ = |10 * u0 - 3 / 4 * u3| * |y0| := abs_mul _ _
      _ ≤ 43 / 4 * N * |y0| := mul_le_mul_of_nonneg_right hp0 (abs_nonneg _)
  have k1 : (1 / 4 * u1 - 3 / 4 * u2) * y1 ≤ 1 * N * |y1| := by
    calc (1 / 4 * u1 - 3 / 4 * u2) * y1 ≤ |(1 / 4 * u1 - 3 / 4 * u2) * y1| := le_abs_self _
      _ = |1 / 4 * u1 - 3 / 4 * u2| * |y1| := abs_mul _ _
      _ ≤ 1 * N * |y1| := mul_le_mul_of_nonneg_right hp1 (abs_nonneg _)
  have am0 : 43 * N * |y0| ≤ 16 * y0 ^ 2 + 1849 / 64 * N ^ 2 := by
    nlinarith [sq_nonneg (4 * |y0| - 43 / 8 * N), sq_abs y0]
  have am1 : 4 * N * |y1| ≤ 16 * y1 ^ 2 + 1 / 4 * N ^ 2 := by
    nlinarith [sq_nonneg (4 * |y1| - 1 / 2 * N), sq_abs y1]
  have kk : 4 * κ * ((10 * u0 - 3 / 4 * u3) * y0 + (1 / 4 * u1 - 3 / 4 * u2) * y1) ≤
      κ * (16 * (y0 ^ 2 + y1 ^ 2) + 30 * N ^ 2) := by
    have : 4 * ((10 * u0 - 3 / 4 * u3) * y0 + (1 / 4 * u1 - 3 / 4 * u2) * y1) ≤
        16 * (y0 ^ 2 + y1 ^ 2) + 30 * N ^ 2 := by
      have := mul_le_mul_of_nonneg_left k0 (by norm_num : (0:ℝ) ≤ 4)
      have := mul_le_mul_of_nonneg_left k1 (by norm_num : (0:ℝ) ≤ 4)
      have : 0 ≤ N ^ 2 := sq_nonneg N
      linarith
    have := mul_le_mul_of_nonneg_left this hκ
    linarith
  have hκN : κ * N ^ 2 ≤ 1 / 100 * N ^ 2 := mul_le_mul_of_nonneg_right hκs (sq_nonneg N)
  have hηN : η * N ^ 2 ≤ 1 / 100 * N ^ 2 := mul_le_mul_of_nonneg_right hηs (sq_nonneg N)
  have hN2' : 0 < N ^ 2 := by positivity
  linarith


/-! ### Speed bound and Gronwall fence (as in the slow-escape proof) -/

/-- The Levi-Civita vector field, written with the explicit gradient. -/
noncomputable def vfield (q : ℝ × ℝ × Phase) : Phase :=
  ![kGradR q.1 q.2.1 (rD q.2.2) q.2.2 2, kGradR q.1 q.2.1 (rD q.2.2) q.2.2 3,
    -kGradR q.1 q.2.1 (rD q.2.2) q.2.2 0, -kGradR q.1 q.2.1 (rD q.2.2) q.2.2 1]

theorem hvf_eq (μ c : ℝ) {y : Phase} (hy : y ∈ U) :
    hamiltonianVectorField (leviCivitaHamiltonian μ c) y = vfield (μ, c, y) := by
  have h := (leviCivita_explicit_derivatives μ c).1 y hy
  simp only [hamiltonianVectorField, vfield, h, kGrad]

theorem differentiableAt_rD {y : Phase} (hy : y ∈ U) : DifferentiableAt ℝ rD y := by
  unfold rD
  refine DifferentiableAt.sqrt ?_ (show (0 : ℝ) < secondCollisionDistanceSq y from hy).ne'
  unfold secondCollisionDistanceSq; fun_prop

theorem differentiableAt_kGradR' (i : Fin 4) {p : ℝ × ℝ × ℝ × Phase} (hp : p.2.2.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) p := by
  have h3 : p.2.2.1 ^ 3 ≠ 0 := pow_ne_zero 3 hp
  fin_cases i <;>
    simp only [kGradR, dP, dZ, dD, zNormSq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop (disch := first | assumption | exact mul_ne_zero two_ne_zero h3)

theorem differentiableAt_vfield {q : ℝ × ℝ × Phase} (hq : q.2.2 ∈ U) :
    DifferentiableAt ℝ vfield q := by
  have hr : DifferentiableAt ℝ (fun q : ℝ × ℝ × Phase => (q.1, q.2.1, rD q.2.2, q.2.2)) q :=
    by
      have := (differentiableAt_rD hq).comp q
        (differentiableAt_snd.comp q differentiableAt_snd :
          DifferentiableAt ℝ (fun q : ℝ × ℝ × Phase => q.2.2) q)
      fun_prop
  have hr0 : rD q.2.2 ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hK : ∀ i : Fin 4, DifferentiableAt ℝ
      (fun q : ℝ × ℝ × Phase => kGradR q.1 q.2.1 (rD q.2.2) q.2.2 i) q := fun i => by
    have := DifferentiableAt.comp
      (g := fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) q
      (differentiableAt_kGradR' i (p := (q.1, q.2.1, rD q.2.2, q.2.2)) hr0) hr
    exact this
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · exact hK 2
  · exact hK 3
  · exact (hK 0).neg
  · exact (hK 1).neg

theorem vfield_sP : vfield (1 / 2, 2, ![1 / 2, 0, 0, 0]) = 0 := by
  funext i
  fin_cases i <;> simp [vfield, kGradR, dP, dZ, dD, zNormSq] <;>
    (try rw [rD_quarter (by simp [secondCollisionDistanceSq]; norm_num)]) <;> norm_num

theorem vfield_sM : vfield (1 / 2, 2, ![-(1 / 2), 0, 0, 0]) = 0 := by
  funext i
  fin_cases i <;> simp [vfield, kGradR, dP, dZ, dD, zNormSq] <;>
    (try rw [rD_quarter (by simp [secondCollisionDistanceSq]; norm_num)]) <;> norm_num

/-- Linear speed bound near an equilibrium of the `(1/2, 2)` field. -/
theorem lin_bound (s : Phase) (hs : s ∈ U) (h0 : vfield (1 / 2, 2, s) = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (μ c : ℝ) (y : Phase),
      |μ - 1 / 2| < δ → |c - 2| < δ → ‖y - s‖ < δ →
        y ∈ U ∧ ‖vfield (μ, c, y)‖ ≤ C * (‖y - s‖ + |μ - 1 / 2| + |c - 2|) := by
  have hd := differentiableAt_vfield (q := ((1 / 2 : ℝ), (2 : ℝ), s)) hs
  obtain ⟨C0, hC0⟩ := hd.isBigO_sub.bound
  have hU : ∀ᶠ q in 𝓝 ((1 / 2 : ℝ), (2 : ℝ), s), q.2.2 ∈ U :=
    (continuous_snd.comp continuous_snd).continuousAt.preimage_mem_nhds (isOpen_U'.mem_nhds hs)
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp (hC0.and hU)
  refine ⟨max C0 1, δ, lt_of_lt_of_le one_pos (le_max_right _ _), hδ,
    fun μ c y hμ hc hy => ?_⟩
  have hdist : dist (μ, c, y) ((1 / 2 : ℝ), (2 : ℝ), s) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt hμ (max_lt hc hy)
  obtain ⟨hb, hyU⟩ := hall hdist
  refine ⟨hyU, ?_⟩
  rw [h0, sub_zero] at hb
  have hn : ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ ≤ ‖y - s‖ + |μ - 1 / 2| + |c - 2| := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    have h1 := norm_nonneg (y - s)
    have h2 := abs_nonneg (μ - 1 / 2)
    have h3 := abs_nonneg (c - 2)
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  have hn0 := norm_nonneg ((μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s))
  calc ‖vfield (μ, c, y)‖ ≤ C0 * ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ := hb
    _ ≤ max C0 1 * ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hn0
    _ ≤ max C0 1 * (‖y - s‖ + |μ - 1 / 2| + |c - 2|) :=
        mul_le_mul_of_nonneg_left hn (le_trans zero_le_one (le_max_right _ _))

/-- Gronwall fence: a trajectory with speed `≤ C (‖x - s‖ + p)` inside the ball of radius `R`,
starting within `r > p` of `s`, stays in that ball for time `L` when `r e^{2CL} < R`. -/
theorem stay_in_ball {x v : ℝ → Phase} (hx : ∀ t, HasDerivAt x (v t) t) (s : Phase)
    {C R r p : ℝ} (hC : 0 < C) (hp0 : 0 ≤ p) (hp : p < r)
    (hv : ∀ t, ‖x t - s‖ < R → ‖v t‖ ≤ C * (‖x t - s‖ + p))
    {t0 L : ℝ} (hrR : r * Real.exp (2 * C * L) < R) (h0 : ‖x t0 - s‖ < r) :
    ∀ t ∈ Set.Icc t0 (t0 + L), ‖x t - s‖ < R := by
  have hr0 : 0 < r := lt_of_le_of_lt hp0 hp
  have key : ∀ t ∈ Set.Icc t0 (t0 + L), ‖x t - s‖ ≤ r * Real.exp (2 * C * (t - t0)) := by
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary (f := fun t => x t - s) (f' := v)
      (B := fun t => r * Real.exp (2 * C * (t - t0)))
      (B' := fun t => 2 * C * (r * Real.exp (2 * C * (t - t0)))) ?_ ?_ ?_ ?_ ?_
    · exact fun t _ => ((hx t).sub_const s).continuousAt.continuousWithinAt
    · exact fun t _ => ((hx t).sub_const s).hasDerivWithinAt
    · show ‖x t0 - s‖ ≤ r * Real.exp (2 * C * (t0 - t0))
      rw [sub_self, mul_zero, Real.exp_zero, mul_one]; exact h0.le
    · intro t
      exact ((((hasDerivAt_id t).sub_const t0).const_mul (2 * C)).exp.const_mul r).congr_deriv
        (by simp only [id, mul_one]; ring)
    · intro t ht heq
      have hle : 2 * C * (t - t0) ≤ 2 * C * L := by
        have := ht.2; have := ht.1; nlinarith
      have hB : r * Real.exp (2 * C * (t - t0)) < R :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hr0.le) hrR
      have hb := hv t (heq ▸ hB)
      rw [heq] at hb
      have hr1 : r ≤ r * Real.exp (2 * C * (t - t0)) :=
        le_mul_of_one_le_right hr0.le (Real.one_le_exp (by have := ht.1; nlinarith))
      have hpB : C * p < C * (r * Real.exp (2 * C * (t - t0))) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hp hr1) hC
      linarith
  intro t ht
  have hle : 2 * C * (t - t0) ≤ 2 * C * L := by
    have := ht.2; nlinarith
  calc ‖x t - s‖ ≤ r * Real.exp (2 * C * (t - t0)) := key t ht
    _ ≤ r * Real.exp (2 * C * L) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hr0.le
    _ < R := hrR

/-! ### Pointwise Lyapunov positivity -/

/-- `uᵀ Q u` for the Lyapunov form `Q`. -/
noncomputable def lyapQ (u : Phase) : ℝ :=
  -7 * u 0 * u 1 + 20 * u 0 * u 2 + 1 / 2 * u 1 * u 3 - 3 / 2 * u 2 * u 3

/-- `2 uᵀ Q w`, the derivative of `lyapQ` in direction `w`. -/
noncomputable def lyapD (u w : Phase) : ℝ :=
  2 * ((-7 / 2 * u 1 + 10 * u 2) * w 0 + (-7 / 2 * u 0 + 1 / 4 * u 3) * w 1
    + (10 * u 0 - 3 / 4 * u 3) * w 2 + (1 / 4 * u 1 - 3 / 4 * u 2) * w 3)

theorem sq_norm_le_sum (u : Phase) : ‖u‖ ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2 := by
  have h : ‖u‖ ≤ Real.sqrt (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    fin_cases i <;> simp <;> nlinarith [sq_nonneg (u 0), sq_nonneg (u 1), sq_nonneg (u 2),
      sq_nonneg (u 3)]
  calc ‖u‖ ^ 2 ≤ (Real.sqrt (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 + u 3 ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt (by positivity)

theorem lyap_pos {s e y : Phase} {μ c cs δ : ℝ}
    (hUδ : ∀ y : Phase, ‖y - s‖ < δ → y ∈ U)
    (hlin : ∀ y y' : Phase, ‖y - s‖ < δ → ‖y' - s‖ < δ →
      ‖Gq (μ, cs, y) - Gq (μ, cs, y') - H0act (y - y')‖ ≤ 1 / 100 * ‖y - y'‖)
    (he : ‖e - s‖ < δ) (hy : ‖y - s‖ < δ)
    (hG0 : Gq (μ, cs, e) = 0) (hK0 : leviCivitaHamiltonian μ cs e = 0)
    (hκ : 0 ≤ c - cs) (hκs : c - cs ≤ 1 / 100)
    (hKy : leviCivitaHamiltonian μ c y = 0) (hne : y ≠ e) :
    0 < lyapD (y - e) (vfield (μ, c, y)) := by
  set u := y - e with hu
  set κ := c - cs with hκdef
  have hN : 0 < ‖u‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  have heu : ‖e + u - s‖ < δ := by rw [hu, add_sub_cancel]; exact hy
  have ht := taylor_lower (by norm_num : (0 : ℝ) ≤ 1 / 100) hUδ hlin he heu hG0 hK0
  rw [hu, add_sub_cancel] at ht
  have hKa := K_affine μ c cs y
  rw [hKy] at hKa
  have hlev : qH u ≤ 4 * (1 / 100) * ‖u‖ ^ 2 - 2 * κ * (y 0 ^ 2 + y 1 ^ 2) := by
    simp only [zNormSq] at hKa; nlinarith
  have hl := hlin y e hy he
  rw [hG0, sub_zero] at hl
  set err := Gq (μ, cs, y) - H0act u with herr
  have hg : Gq (μ, c, y) = H0act u + err + κ • dZ y := by
    rw [Gq_affine μ c cs y, herr]; abel
  have hE : ∀ i, |err i| ≤ 1 / 100 * ‖u‖ := fun i => (norm_le_pi_norm err i).trans hl
  have hU : ∀ i, |u i| ≤ ‖u‖ := fun i => norm_le_pi_norm u i
  have key := lyap_alg (u 0) (u 1) (u 2) (u 3) (err 0) (err 1) (err 2) (err 3) (y 0) (y 1) κ
    (1 / 100) ‖u‖ hN (hU 0) (hU 1) (hU 2) (hU 3) (sq_norm_le_sum u) (hE 0) (hE 1) (hE 2) (hE 3)
    hκ hκs (by norm_num) le_rfl (by simpa [qH, Fin.sum_univ_four, H0act] using hlev)
  have hv : vfield (μ, c, y) = ![Gq (μ, c, y) 2, Gq (μ, c, y) 3, -Gq (μ, c, y) 0,
      -Gq (μ, c, y) 1] := rfl
  rw [hv, hg]
  simp only [lyapD, Pi.add_apply, Pi.smul_apply, smul_eq_mul, H0act, dZ,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]
  linarith

/-! ### No closed loop -/

theorem hasDerivAt_lyapQ {x : ℝ → Phase} {w : Phase} {t : ℝ} (e : Phase)
    (hx : HasDerivAt x w t) :
    HasDerivAt (fun t => lyapQ (x t - e)) (lyapD (x t - e) w) t := by
  have h : ∀ i, HasDerivAt (fun t => x t i - e i) (w i) t := fun i => by
    simpa using ((hasDerivAt_pi.1 hx) i).sub_const (e i)
  have := (((((h 0).const_mul (-7)).mul (h 1)).add (((h 0).const_mul 20).mul (h 2))).add
    (((h 1).const_mul (1 / 2)).mul (h 3))).sub (((h 2).const_mul (3 / 2)).mul (h 3))
  refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  · simp only [lyapD, Pi.sub_apply]; ring
  · simp only [lyapQ, Pi.sub_apply, Pi.add_apply, Pi.mul_apply]

theorem no_loop {x : ℝ → Phase} {μ c : ℝ} (hx : ∀ t, HasDerivAt x (vfield (μ, c, x t)) t)
    (e : Phase) {a b : ℝ} (hab : a < b)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < lyapD (x t - e) (vfield (μ, c, x t))) : x b ≠ x a := by
  intro h
  have hd : ∀ t, HasDerivAt (fun t => lyapQ (x t - e)) (lyapD (x t - e) (vfield (μ, c, x t))) t :=
    fun t => hasDerivAt_lyapQ e (hx t)
  have hmono : StrictMonoOn (fun t => lyapQ (x t - e)) (Set.Icc a b) :=
    strictMonoOn_of_deriv_pos (convex_Icc a b) (fun t _ => (hd t).continuousAt.continuousWithinAt)
      (fun t ht => by rw [(hd t).deriv]; exact hpos t (interior_subset ht))
  have := hmono ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab
  simp only [h] at this
  exact lt_irrefl _ this

/-! ### The lifted Lagrange point is close to `s₊` -/

theorem eL_close {μ x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hx : |x - 1 / 2| ≤ 7 * |μ - 1 / 2|) :
    ‖eL μ x - ![1 / 2, 0, 0, 0]‖ ≤ 8 * |μ - 1 / 2| := by
  have hw := sqrt_half_sq hx0
  set w := Real.sqrt (x / 2) with hwdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw1 : w ≤ 1 := by nlinarith
  have hd0 : 0 ≤ |μ - 1 / 2| := abs_nonneg _
  have hc0 : |w - 1 / 2| ≤ |x - 1 / 2| := by
    have hprod : (w - 1 / 2) * (w + 1 / 2) = (x - 1 / 2) / 2 := by nlinarith
    have : |w - 1 / 2| * (w + 1 / 2) = |x - 1 / 2| / 2 := by
      rw [← abs_of_nonneg (by linarith : (0 : ℝ) ≤ w + 1 / 2), ← abs_mul, hprod, abs_div,
        abs_two]
    nlinarith [abs_nonneg (w - 1 / 2), abs_nonneg (x - 1 / 2)]
  have hc3 : |w * (μ - x)| ≤ 8 * |μ - 1 / 2| := by
    rw [abs_mul, abs_of_nonneg hw0]
    have : |μ - x| ≤ |μ - 1 / 2| + |x - 1 / 2| := by
      calc |μ - x| = |(μ - 1 / 2) - (x - 1 / 2)| := by ring_nf
        _ ≤ |μ - 1 / 2| + |x - 1 / 2| := abs_sub _ _
    nlinarith [abs_nonneg (μ - x)]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  fin_cases i <;>
    simp only [eL, Pi.sub_apply, Real.norm_eq_abs, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta,
      Fin.mk_one, Fin.reduceFinMk, sub_zero, ← hwdef, sub_self, abs_zero] <;>
    linarith


theorem sM_eq : (![-(1 / 2), 0, 0, 0] : Phase) = -![1 / 2, 0, 0, 0] := by
  funext i; fin_cases i <;> simp

theorem zNormSq_eL {μ x : ℝ} (hx : 0 < x) : zNormSq (eL μ x) = x / 2 := by
  simp only [zNormSq, eL, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [sqrt_half_sq hx]; ring

end BirkhoffGlobalSection.NoShortReturn

open BirkhoffGlobalSection BirkhoffGlobalSection.NoShortReturn in
theorem solution (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U)
    (L : ℝ) (hL : 0 < L) :
    ∃ V : Set Phase, IsOpen V ∧ V ⊆ U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ V ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ V) →
            ∀ s : ℝ, x s ∈ V → ∀ d : ℝ, 0 < d → d ≤ L →
              x (s + d) ≠ x s := by
  obtain ⟨δ1, hδ1, hlin1⟩ := grad_linearization _ sP_mem hess_sP (1 / 100) (by norm_num)
  obtain ⟨δ2, hδ2, hlin2⟩ := grad_linearization _ sM_mem hess_sM (1 / 100) (by norm_num)
  obtain ⟨C1, δ3, hC1, hδ3, hb1⟩ := lin_bound _ sP_mem vfield_sP
  obtain ⟨C2, δ4, hC2, hδ4, hb2⟩ := lin_bound _ sM_mem vfield_sM
  obtain ⟨R1, hR1, hball1⟩ := Metric.isOpen_iff.mp hU _ hplus
  obtain ⟨R2, hR2, hball2⟩ := Metric.isOpen_iff.mp hU _ hminus
  set C := max C1 C2 with hCdef
  have hC : 0 < C := lt_of_lt_of_le hC1 (le_max_left _ _)
  set ρ := min (min δ1 δ2) (min δ3 δ4) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hδ1 hδ2) (lt_min hδ3 hδ4)
  have hρ1 : ρ ≤ δ1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ δ2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ3 : ρ ≤ δ3 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ4 : ρ ≤ δ4 := le_trans (min_le_right _ _) (min_le_right _ _)
  set R := min (min R1 R2) (ρ / 2) with hRdef
  have hR : 0 < R := lt_min (lt_min hR1 hR2) (by positivity)
  have hRR1 : R ≤ R1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRR2 : R ≤ R2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRρ : R ≤ ρ / 2 := min_le_right _ _
  set r := R / 2 * Real.exp (-(2 * C * L)) with hrdef
  have hr : 0 < r := by positivity
  have hrR : r * Real.exp (2 * C * L) < R := by
    rw [hrdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; linarith
  have hrhalf : r ≤ R / 2 := by
    rw [hrdef]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.2 (by have := mul_pos (mul_pos two_pos hC) hL; linarith))
  set θ := min (min (r / 4) (ρ / 16)) (1 / 400) with hθdef
  have hθ : 0 < θ := lt_min (lt_min (by positivity) (by positivity)) (by norm_num)
  have hθr : θ ≤ r / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hθρ : θ ≤ ρ / 16 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hθs : θ ≤ 1 / 400 := min_le_right _ _
  obtain ⟨ε0, hε0, hcrit⟩ := first_critical_value_near_half θ hθ
  have hrsub1 : Metric.ball (![1 / 2, 0, 0, 0] : Phase) r ⊆ U :=
    (Metric.ball_subset_ball (by linarith)).trans hball1
  have hrsub2 : Metric.ball (![-(1 / 2), 0, 0, 0] : Phase) r ⊆ U :=
    (Metric.ball_subset_ball (by linarith)).trans hball2
  refine ⟨Metric.ball (![1 / 2, 0, 0, 0] : Phase) r ∪ Metric.ball (![-(1 / 2), 0, 0, 0] : Phase) r,
    Metric.isOpen_ball.union Metric.isOpen_ball, Set.union_subset hrsub1 hrsub2,
    Or.inl (Metric.mem_ball_self hr), Or.inr (Metric.mem_ball_self hr),
    min ε0 θ, θ, lt_min hε0 hθ, hθ, ?_⟩
  intro μ c h0 h1 hμ hc hsub x T hper _ s0 hs0 d hd0 hdL heq
  have hμθ : |μ - 1 / 2| < θ := lt_of_lt_of_le hμ (min_le_right _ _)
  obtain ⟨xL, hx0, hx1, hax, hfc⟩ := lagrange_data μ h0 h1
  set cs := cStar μ xL with hcsdef
  have hsub' : -c < firstCriticalValue μ := hsub
  rw [hfc] at hsub'
  have hcs1 : cs < c := by linarith
  have hcs2 : 2 - θ < cs := by
    have := hcrit μ h0 h1 (lt_of_lt_of_le hμ (min_le_left _ _)); rw [hfc] at this; linarith
  have hcθ : |c - 2| < θ := abs_lt.2 ⟨by linarith, by linarith⟩
  have hcsθ : |cs - 2| < θ := abs_lt.2 ⟨by linarith, by linarith⟩
  have hκ0 : 0 ≤ c - cs := by linarith
  have hκs : c - cs ≤ 1 / 100 := by linarith
  have heP := eL_close hx0 hx1 (x_near_half hx0 hx1 hax h0 h1)
  have hGe : Gq (μ, cs, eL μ xL) = 0 := kGrad_eL hx0 hx1 hax
  have hKe : leviCivitaHamiltonian μ cs (eL μ xL) = 0 := K_eL hx0 hx1
  have hKec : 0 < leviCivitaHamiltonian μ c (eL μ xL) := by
    rw [K_affine μ c cs, hKe, zNormSq_eL hx0]
    have : 0 < c - cs := by linarith
    positivity
  have hp0 : 0 ≤ |μ - 1 / 2| + |c - 2| := by positivity
  have hp : |μ - 1 / 2| + |c - 2| < r := by linarith
  have hder := hper.2.2.1
  have hloc : ∀ t, x t ∈ regularEnergyLocus μ c :=
    fun t => connectedComponentIn_subset _ _ (hper.2.1 t)
  have hKx : ∀ t, leviCivitaHamiltonian μ c (x t) = 0 := fun t => (hloc t).1
  have hxU : ∀ t, x t ∈ TangentialHessian.U := fun t => (hloc t).2
  have hxv : ∀ t, HasDerivAt x (vfield (μ, c, x t)) t := fun t => by
    rw [← hvf_eq μ c (hxU t)]; exact hder t
  have hds : s0 < s0 + d := by linarith
  rcases hs0 with h | h
  · have hstay := stay_in_ball hder _ hC hp0 hp (R := R) (L := L)
      (fun t ht => by
        obtain ⟨hyU, hbd⟩ := hb1 μ c (x t) (by linarith) (by linarith) (by linarith)
        rw [hvf_eq μ c hyU]
        calc ‖vfield (μ, c, x t)‖ ≤ C1 * (‖x t - ![1 / 2, 0, 0, 0]‖ + |μ - 1 / 2| + |c - 2|) := hbd
          _ ≤ C * (‖x t - ![1 / 2, 0, 0, 0]‖ + (|μ - 1 / 2| + |c - 2|)) := by
            rw [← add_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      hrR (by rwa [Metric.mem_ball, dist_eq_norm] at h)
    obtain ⟨hUδ, hlin⟩ := hlin1 μ cs (by linarith) (by linarith)
    refine no_loop hxv (eL μ xL) hds (fun t ht => ?_) heq
    have hy := hstay t ⟨ht.1, by linarith [ht.2]⟩
    refine lyap_pos hUδ hlin (by linarith) (by linarith) hGe hKe hκ0 hκs (hKx t) ?_
    intro he; have := hKx t; rw [he] at this; linarith
  · have hstay := stay_in_ball hder _ hC hp0 hp (R := R) (L := L)
      (fun t ht => by
        obtain ⟨hyU, hbd⟩ := hb2 μ c (x t) (by linarith) (by linarith) (by linarith)
        rw [hvf_eq μ c hyU]
        calc ‖vfield (μ, c, x t)‖ ≤ C2 * (‖x t - ![-(1 / 2), 0, 0, 0]‖ + |μ - 1 / 2| + |c - 2|) := hbd
          _ ≤ C * (‖x t - ![-(1 / 2), 0, 0, 0]‖ + (|μ - 1 / 2| + |c - 2|)) := by
            rw [← add_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      hrR (by rwa [Metric.mem_ball, dist_eq_norm] at h)
    obtain ⟨hUδ, hlin⟩ := hlin2 μ cs (by linarith) (by linarith)
    have heM : ‖-eL μ xL - ![-(1 / 2), 0, 0, 0]‖ = ‖eL μ xL - ![1 / 2, 0, 0, 0]‖ := by
      rw [sM_eq, ← norm_neg]; congr 1; abel
    have hGe' : Gq (μ, cs, -eL μ xL) = 0 := by rw [Gq_neg, hGe, neg_zero]
    have hKe' : leviCivitaHamiltonian μ cs (-eL μ xL) = 0 := by rw [K_neg, hKe]
    have hKec' : 0 < leviCivitaHamiltonian μ c (-eL μ xL) := by rw [K_neg]; exact hKec
    refine no_loop hxv (-eL μ xL) hds (fun t ht => ?_) heq
    have hy := hstay t ⟨ht.1, by linarith [ht.2]⟩
    refine lyap_pos hUδ hlin (by rw [heM]; linarith) (by linarith) hGe' hKe' hκ0 hκs (hKx t) ?_
    intro he; have := hKx t; rw [he] at this; linarith
