-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_linear_system_rotation_growth
-- status  : ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-09-28T17:52:19.15398+00:00
-- url     : https://prove2.me/submissions/2afdfb5b-05c2-415d-ac52-aa6e48aafb21

import Theorems.Thm_BirkhoffGlobalSection_ambient_rotation_product_slit
import Theorems.Thm_BirkhoffGlobalSection_saddle_center_constant_rotation_growth
import Theorems.Thm_BirkhoffGlobalSection_linear_system_rotation_perturbation
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.Module.FiniteDimension

open BirkhoffGlobalSection
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false

/-- The symplectic pairing `x ⬝ᵥ qI y` in coordinates. -/
private lemma omegaQ (x y : Phase) :
    x ⬝ᵥ TangentialHessian.qI.mulVec y = x 0 * y 2 + x 1 * y 3 - x 2 * y 0 - x 3 * y 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

private lemma mulVec_apply4 (A : Matrix (Fin 4) (Fin 4) ℝ) (x : Phase) (i : Fin 4) :
    A.mulVec x i = A i 0 * x 0 + A i 1 * x 1 + A i 2 * x 2 + A i 3 * x 3 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private lemma qI0 (w : Phase) : TangentialHessian.qI.mulVec w 0 = w 2 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI1 (w : Phase) : TangentialHessian.qI.mulVec w 1 = w 3 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI2 (w : Phase) : TangentialHessian.qI.mulVec w 2 = -w 0 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
private lemma qI3 (w : Phase) : TangentialHessian.qI.mulVec w 3 = -w 1 := by
  simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private lemma qI_apply (w : Phase) :
    TangentialHessian.qI.mulVec w = ![w 2, w 3, -w 0, -w 1] := by
  funext i; fin_cases i <;> simp [TangentialHessian.qI, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The linear flow of a symmetric coefficient matrix preserves the symplectic
pairing on the interval where the equation holds. -/
private lemma symp_on_interval {a b : ℝ} (hab : a ≤ b) {H : ℝ → Matrix (Fin 4) (Fin 4) ℝ}
    (hHs : ∀ t ∈ Set.Icc a b, ∀ i j : Fin 4, H t i j = H t j i)
    {Y : ℝ → (Phase →L[ℝ] Phase)}
    (hY0 : ∀ u v : Phase,
      Y a u ⬝ᵥ TangentialHessian.qI.mulVec (Y a v) = u ⬝ᵥ TangentialHessian.qI.mulVec v)
    (hYd : ∀ t ∈ Set.Icc a b, ∀ v : Phase,
      HasDerivAt (fun τ => Y τ v) (TangentialHessian.qI.mulVec ((H t).mulVec (Y t v))) t) :
    ∀ t ∈ Set.Icc a b, ∀ u v : Phase,
      Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := by
  intro t ht u v
  set f : ℝ → ℝ := fun τ => Y τ u ⬝ᵥ TangentialHessian.qI.mulVec (Y τ v) with hf
  have hderiv : ∀ s ∈ Set.Icc a b, HasDerivAt f 0 s := by
    intro s hs
    have hc := hasDerivAt_pi.mp (hYd s hs u)
    have hd := hasDerivAt_pi.mp (hYd s hs v)
    have h := ((((hc 0).mul (hd 2)).add ((hc 1).mul (hd 3))).sub ((hc 2).mul (hd 0))).sub
      ((hc 3).mul (hd 1))
    refine (h.congr_deriv ?_).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun r => ?_)
    · simp only [qI0, qI1, qI2, qI3]
      simp only [mulVec_apply4]
      have h01 := hHs s hs 0 1; have h02 := hHs s hs 0 2; have h03 := hHs s hs 0 3
      have h12 := hHs s hs 1 2; have h13 := hHs s hs 1 3; have h23 := hHs s hs 2 3
      rw [h01, h02, h03, h12, h13, h23]
      ring
    · simp only [hf, omegaQ, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  have hcont : ContinuousOn f (Set.Icc a b) :=
    fun s hs => (hderiv s hs).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun s hs => (hderiv s (Set.Ico_subset_Icc_self hs)).hasDerivWithinAt)
  rw [show Y t u ⬝ᵥ TangentialHessian.qI.mulVec (Y t v) = f t from rfl, hconst t ht]
  exact hY0 u v

/-- A symplectic linear map is injective. -/
private lemma symp_injective {M : Phase →L[ℝ] Phase}
    (hM : ∀ u v : Phase,
      M u ⬝ᵥ TangentialHessian.qI.mulVec (M v) = u ⬝ᵥ TangentialHessian.qI.mulVec v) :
    Function.Injective M := by
  intro u w huw
  have h0 : ∀ v : Phase, (u - w) ⬝ᵥ TangentialHessian.qI.mulVec v = 0 := by
    intro v
    rw [← hM (u - w) v, map_sub, huw, sub_self, zero_dotProduct]
  funext i
  have e2 := h0 (coordinateVector 2); have e3 := h0 (coordinateVector 3)
  have e0 := h0 (coordinateVector 0); have e1 := h0 (coordinateVector 1)
  simp [omegaQ, coordinateVector] at e0 e1 e2 e3
  fin_cases i
  · show u 0 = w 0; linarith [e2]
  · show u 1 = w 1; linarith [e3]
  · show u 2 = w 2; linarith [e0]
  · show u 3 = w 3; linarith [e1]

/-- The ambient determinant in terms of the matrix entries. -/
private lemma ambientRotationDet_eq (M : Phase →L[ℝ] Phase) :
    ambientRotationDet M =
      (⟨(M (coordinateVector 0) 0 + M (coordinateVector 2) 2) / 2,
          (M (coordinateVector 2) 0 - M (coordinateVector 0) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 1) 1 + M (coordinateVector 3) 3) / 2,
          (M (coordinateVector 3) 1 - M (coordinateVector 1) 3) / 2⟩ -
      (⟨(M (coordinateVector 1) 0 + M (coordinateVector 3) 2) / 2,
          (M (coordinateVector 3) 0 - M (coordinateVector 1) 2) / 2⟩ : ℂ) *
        ⟨(M (coordinateVector 0) 1 + M (coordinateVector 2) 3) / 2,
          (M (coordinateVector 2) 1 - M (coordinateVector 0) 3) / 2⟩ := by
  unfold ambientRotationDet
  rw [Matrix.det_fin_two]
  rfl

private lemma continuous_mk {f g : ℝ → ℝ} {s : Set ℝ} (hf : ContinuousOn f s)
    (hg : ContinuousOn g s) : ContinuousOn (fun t => (⟨f t, g t⟩ : ℂ)) s := by
  have : (fun t => (⟨f t, g t⟩ : ℂ)) = fun t => (f t : ℂ) + (g t : ℂ) * Complex.I := by
    funext t; apply Complex.ext <;> simp
  rw [this]
  exact (Complex.continuous_ofReal.comp_continuousOn hf).add
    ((Complex.continuous_ofReal.comp_continuousOn hg).mul continuousOn_const)

/-- The ambient determinant of a family of maps with continuous entries is continuous. -/
private lemma detP_continuousOn {Z : ℝ → (Phase →L[ℝ] Phase)} {s : Set ℝ}
    (hZ : ∀ (k i : Fin 4), ContinuousOn (fun t => Z t (coordinateVector k) i) s) :
    ContinuousOn (fun t => ambientRotationDet (Z t)) s := by
  simp only [ambientRotationDet_eq]
  refine ((continuous_mk ?_ ?_).mul (continuous_mk ?_ ?_)).sub
    ((continuous_mk ?_ ?_).mul (continuous_mk ?_ ?_)) <;>
    first
    | exact ((hZ _ _).add (hZ _ _)).div_const _
    | exact ((hZ _ _).sub (hZ _ _)).div_const _

/-- Transfer of a polar representation through the bounded-defect product. -/
private lemma polar_transfer {qY qΦ qM : ℂ} {α ρ : ℝ} (hρ : 0 < ρ)
    (hqY : qY = ⟨ρ * Real.cos α, ρ * Real.sin α⟩)
    (hX : qY * (starRingEnd ℂ) qΦ * (starRingEnd ℂ) qM ∈ Complex.slitPlane) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ qΦ =
      ⟨ρ' * Real.cos (α - Complex.arg (qY * (starRingEnd ℂ) qΦ * (starRingEnd ℂ) qM) -
          Complex.arg qM),
        ρ' * Real.sin (α - Complex.arg (qY * (starRingEnd ℂ) qΦ * (starRingEnd ℂ) qM) -
          Complex.arg qM)⟩ := by
  set X := qY * (starRingEnd ℂ) qΦ * (starRingEnd ℂ) qM with hXdef
  have hX0 : X ≠ 0 := Complex.slitPlane_ne_zero hX
  have hqM : qM ≠ 0 := by
    intro h; apply hX0; rw [hXdef, h, map_zero, mul_zero]
  have hqYexp : qY = (ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I) := by
    rw [hqY]; apply Complex.ext <;>
      simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  have hnX : 0 < ‖X‖ := norm_pos_iff.mpr hX0
  have hnM : 0 < ‖qM‖ := norm_pos_iff.mpr hqM
  set θX := Complex.arg X with hθX
  set θM := Complex.arg qM with hθM
  set φ := α - θX - θM with hφ
  set ρ' := ‖X‖ / (ρ * ‖qM‖) with hρ'
  refine ⟨ρ', by positivity, ?_⟩
  have hcY : (starRingEnd ℂ) qY = (ρ : ℂ) * Complex.exp (-(α : ℂ) * Complex.I) := by
    rw [hqYexp, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul,
      Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have hcX : (starRingEnd ℂ) X = (‖X‖ : ℂ) * Complex.exp (-(θX : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I X
    rw [← hθX] at h
    conv_lhs => rw [← h]
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
      Complex.conj_I]
    ring_nf
  have hM : qM = (‖qM‖ : ℂ) * Complex.exp ((θM : ℂ) * Complex.I) :=
    (Complex.norm_mul_exp_arg_mul_I qM).symm
  have hconj : (starRingEnd ℂ) X = (starRingEnd ℂ) qY * qΦ * qM := by
    rw [hXdef]; simp [map_mul]
  have hexp : Complex.exp (-(α : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) *
      Complex.exp ((θM : ℂ) * Complex.I) = Complex.exp (-(θX : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hφ]; push_cast; ring
  have hmag : ((ρ * ρ' * ‖qM‖ : ℝ) : ℂ) = (‖X‖ : ℂ) := by
    congr 1
    rw [hρ']; field_simp
  have hw : (starRingEnd ℂ) qY * ((ρ' : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) * qM =
      (starRingEnd ℂ) X := by
    rw [hcY, hM, hcX, ← hmag, ← hexp]
    push_cast
    ring
  have hne : (starRingEnd ℂ) qY * qM ≠ 0 := by
    refine mul_ne_zero ?_ hqM
    rw [hcY]
    exact mul_ne_zero (by exact_mod_cast hρ.ne') (Complex.exp_ne_zero _)
  have heq : qΦ = (ρ' : ℂ) * Complex.exp ((φ : ℂ) * Complex.I) := by
    have h1 : (starRingEnd ℂ) qY * qM * qΦ =
        (starRingEnd ℂ) qY * qM * ((ρ' : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) := by
      calc (starRingEnd ℂ) qY * qM * qΦ = (starRingEnd ℂ) X := by rw [hconj]; ring
        _ = _ := by rw [← hw]; ring
    exact mul_left_cancel₀ hne h1
  rw [heq]
  apply Complex.ext
  · simp [Complex.exp_ofReal_mul_I_re]
  · simp [Complex.exp_ofReal_mul_I_im]

theorem solution (R : ℝ) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧
      ∀ (a : ℝ) (H : ℝ → Matrix (Fin 4) (Fin 4) ℝ),
        ContinuousOn H (Set.Icc a (a + L)) →
        (∀ t ∈ Set.Icc a (a + L), ∀ i j : Fin 4, H t i j = H t j i) →
        (∀ t ∈ Set.Icc a (a + L),
          ‖H t - !![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1]‖ < δ) →
        ∀ Y : ℝ → (Phase →L[ℝ] Phase),
          (∀ u v : Phase,
            Y a u ⬝ᵥ TangentialHessian.qI.mulVec (Y a v) =
              u ⬝ᵥ TangentialHessian.qI.mulVec v) →
          (∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
            HasDerivAt (fun τ => Y τ v)
              (TangentialHessian.qI.mulVec ((H t).mulVec (Y t v))) t) →
          ∀ α : ℝ → ℝ, IsAmbientRotationAngle Y α →
            R < α (a + L) - α a := by
  obtain ⟨L, hL, hgrowth⟩ := saddle_center_constant_rotation_growth (R + 3 * Real.pi)
  have hK : ∀ i j : Fin 4,
      (!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℝ) i j =
      (!![-16, 0, 0, 1; 0, 8, -1, 0; 0, -1, 1, 0; 1, 0, 0, 1] : Matrix (Fin 4) (Fin 4) ℝ) j i := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  obtain ⟨δ, hδ, hpert⟩ := linear_system_rotation_perturbation _ hK L hL
  refine ⟨δ, L, hδ, hL, ?_⟩
  intro a H hHc hHs hHδ Y hY0 hYd α hα
  have hab : a ≤ a + L := by linarith
  have haI : a ∈ Set.Icc a (a + L) := ⟨le_refl a, hab⟩
  have hbI : a + L ∈ Set.Icc a (a + L) := ⟨hab, le_refl _⟩
  -- the flow is symplectic on the interval
  have hsymp := symp_on_interval hab hHs hY0 hYd
  -- invert the initial matrix
  set M : Phase →L[ℝ] Phase := Y a with hMdef
  have hinj : Function.Injective M := symp_injective hY0
  set e : Phase ≃ₗ[ℝ] Phase := LinearEquiv.ofInjectiveEndo (M : Phase →ₗ[ℝ] Phase) hinj
  set Minv : Phase →L[ℝ] Phase :=
    LinearMap.toContinuousLinearMap (e.symm : Phase →ₗ[ℝ] Phase) with hMinv
  have he : ∀ x, e x = M x := fun x => by simp [e, LinearEquiv.coe_ofInjectiveEndo]
  have hMMinv : ∀ v, M (Minv v) = v := by
    intro v
    show M (e.symm v) = v
    rw [← he]; exact e.apply_symm_apply v
  have hMinvM : ∀ v, Minv (M v) = v := by
    intro v
    show e.symm (M v) = v
    rw [← he]; exact e.symm_apply_apply v
  -- the identity-normalized flow
  set Φ : ℝ → (Phase →L[ℝ] Phase) := fun t => (Y t).comp Minv with hΦ
  have hΦa : Φ a = ContinuousLinearMap.id ℝ Phase := by
    ext v i; simp [hΦ, ← hMdef, hMMinv]
  have hΦd : ∀ t ∈ Set.Icc a (a + L), ∀ v : Phase,
      HasDerivAt (fun τ => Φ τ v)
        (TangentialHessian.qI.mulVec ((H t).mulVec (Φ t v))) t :=
    fun t ht v => hYd t ht (Minv v)
  have hΦM : ∀ t, (Φ t).comp M = Y t := by
    intro t; ext v i; simp [hΦ, hMinvM]
  have hMsymp : ∀ u v : Phase,
      M u ⬝ᵥ TangentialHessian.qI.mulVec (M v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := hY0
  have hΦsymp : ∀ t ∈ Set.Icc a (a + L), ∀ u v : Phase,
      Φ t u ⬝ᵥ TangentialHessian.qI.mulVec (Φ t v) = u ⬝ᵥ TangentialHessian.qI.mulVec v := by
    intro t ht u v
    show Y t (Minv u) ⬝ᵥ TangentialHessian.qI.mulVec (Y t (Minv v)) = _
    rw [hsymp t ht, ← hMsymp, hMMinv, hMMinv]
  -- bounded defect: the product of determinants avoids the negative axis
  set X : ℝ → ℂ := fun t => ambientRotationDet (Y t) *
      (starRingEnd ℂ) (ambientRotationDet (Φ t)) * (starRingEnd ℂ) (ambientRotationDet M)
    with hXdef
  have hslit : ∀ t ∈ Set.Icc a (a + L), X t ∈ Complex.slitPlane := by
    intro t ht
    have h := ambient_rotation_product_slit (Φ t) M (hΦsymp t ht) hMsymp
    rw [hΦM t] at h
    exact h
  -- continuity on the interval
  have hYc : ∀ (k i : Fin 4), ContinuousOn (fun t => Y t (coordinateVector k) i)
      (Set.Icc a (a + L)) := fun k i t ht =>
    ((hasDerivAt_pi.mp (hYd t ht (coordinateVector k))) i).continuousAt.continuousWithinAt
  have hΦc : ∀ (k i : Fin 4), ContinuousOn (fun t => Φ t (coordinateVector k) i)
      (Set.Icc a (a + L)) := fun k i t ht =>
    ((hasDerivAt_pi.mp (hΦd t ht (coordinateVector k))) i).continuousAt.continuousWithinAt
  have hXc : ContinuousOn X (Set.Icc a (a + L)) :=
    ((detP_continuousOn hYc).mul
      (Complex.continuous_conj.comp_continuousOn (detP_continuousOn hΦc))).mul
      continuousOn_const
  -- a continuous angle for the identity-normalized flow
  set αΦ : ℝ → ℝ := fun t => α t - Complex.arg (X t) - Complex.arg (ambientRotationDet M)
    with hαΦ
  have hargc : ContinuousOn (fun t => Complex.arg (X t)) (Set.Icc a (a + L)) :=
    fun t ht => (Complex.continuousAt_arg (hslit t ht)).comp_continuousWithinAt (hXc t ht)
  have hαΦc : ContinuousOn αΦ (Set.Icc a (a + L)) :=
    (hα.1.continuousOn.sub hargc).sub continuousOn_const
  have hαΦpolar : ∀ t ∈ Set.Icc a (a + L), ∃ ρ : ℝ, 0 < ρ ∧
      ambientRotationDet (Φ t) = ⟨ρ * Real.cos (αΦ t), ρ * Real.sin (αΦ t)⟩ := by
    intro t ht
    obtain ⟨ρ, hρ, hq⟩ := hα.2 t
    exact polar_transfer hρ hq (hslit t ht)
  -- the constant model and the perturbation estimate
  obtain ⟨Φ₀, α₀, hΦ₀a, hΦ₀d, hα₀c, hα₀polar, hα₀grow⟩ := hgrowth a
  have hcmp := hpert a H hHc hHs hHδ Φ Φ₀ hΦa hΦ₀a hΦd hΦ₀d αΦ α₀ hαΦc hα₀c
    hαΦpolar hα₀polar
  -- the defect costs less than `2π`
  have h1 := Complex.neg_pi_lt_arg (X (a + L))
  have h2 : Complex.arg (X a) < Real.pi := by
    rw [Complex.arg_lt_pi_iff]
    rcases Complex.mem_slitPlane_iff.mp (hslit a haI) with h | h
    · exact Or.inl h.le
    · exact Or.inr h
  simp only [hαΦ] at hcmp
  linarith
