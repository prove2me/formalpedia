-- Prove2me | solution 1 for FiniteEnergyPlane.exists_angle_fundamentalSolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T22:53:09.535803+00:00
-- url     : https://prove2.me/submissions/b545d93d-c745-42c8-9d56-b83cf9c7451d

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_linearODE_continuous_param
import Theorems.Thm_FiniteEnergyPlane_eq_mul_exp_integral_div_of_hasDerivAt
import Mathlib



namespace FiniteEnergyPlane

open Matrix
open scoped Real

/-- `ℂ → ℝ²`, the inverse of `vecToC`. -/
noncomputable def wxOfC (z : ℂ) : CauchyRiemannIndex.Vec 1 :=
  z.re • EuclideanSpace.single (Sum.inl 0) 1 + z.im • EuclideanSpace.single (Sum.inr 0) 1

theorem wx_vecToC_ofC (z : ℂ) : vecToC (wxOfC z) = z := by
  apply Complex.ext <;> simp [vecToC, wxOfC, EuclideanSpace.single_apply]

theorem wx_vecToC_inj {v w : CauchyRiemannIndex.Vec 1} (h : vecToC v = vecToC w) : v = w := by
  have h1 : v (Sum.inl 0) = w (Sum.inl 0) := congrArg Complex.re h
  have h2 : v (Sum.inr 0) = w (Sum.inr 0) := congrArg Complex.im h
  ext i
  rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> assumption

theorem wx_continuous_ofC : Continuous wxOfC := by
  unfold wxOfC
  fun_prop

/-- `vecToC` as a continuous `ℝ`-linear map. -/
noncomputable def wxVecToCL : CauchyRiemannIndex.Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun v w => Complex.ext (by simp [vecToC]) (by simp [vecToC])
      map_smul' := fun c v => Complex.ext (by simp [vecToC]) (by simp [vecToC]) }

theorem wx_vecToCL_apply (v : CauchyRiemannIndex.Vec 1) : wxVecToCL v = vecToC v := rfl

theorem wx_vecToC_J (S : CauchyRiemannIndex.Mat 1) (μ : ℝ) (w : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * (S + μ • 1)) w) =
      Complex.I * (vecToC (Matrix.toEuclideanLin S w) + μ * vecToC w) := by
  apply Complex.ext <;>
  simp [vecToC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.J, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply] <;> ring

theorem wx_norm_vecToC_le (S : CauchyRiemannIndex.Mat 1) (w : CauchyRiemannIndex.Vec 1) :
    ‖vecToC (Matrix.toEuclideanLin S w)‖ ≤
      (|S (Sum.inl 0) (Sum.inl 0)| + |S (Sum.inl 0) (Sum.inr 0)| +
        |S (Sum.inr 0) (Sum.inl 0)| + |S (Sum.inr 0) (Sum.inr 0)|) * ‖vecToC w‖ := by
  set a := S (Sum.inl 0) (Sum.inl 0)
  set b := S (Sum.inl 0) (Sum.inr 0)
  set c := S (Sum.inr 0) (Sum.inl 0)
  set d := S (Sum.inr 0) (Sum.inr 0)
  have hre : (vecToC (Matrix.toEuclideanLin S w)).re = a * w (Sum.inl 0) + b * w (Sum.inr 0) := by
    simp [vecToC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, a, b]
  have him : (vecToC (Matrix.toEuclideanLin S w)).im = c * w (Sum.inl 0) + d * w (Sum.inr 0) := by
    simp [vecToC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, c, d]
  have h1 : |w (Sum.inl 0)| ≤ ‖vecToC w‖ := Complex.abs_re_le_norm (vecToC w)
  have h2 : |w (Sum.inr 0)| ≤ ‖vecToC w‖ := Complex.abs_im_le_norm (vecToC w)
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [hre, him]
  have e1 : |a * w (Sum.inl 0) + b * w (Sum.inr 0)| ≤ |a| * ‖vecToC w‖ + |b| * ‖vecToC w‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  have e2 : |c * w (Sum.inl 0) + d * w (Sum.inr 0)| ≤ |c| * ‖vecToC w‖ + |d| * ‖vecToC w‖ := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    gcongr
  linarith

theorem exists_angle_fundamentalSolution_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (Ψ : ℝ → ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : ∀ μ, CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) (Ψ μ)) :
    ∃ (C : ℝ) (θ : ℝ → ℝ → ℝ → ℝ),
      (∀ μ t v, v ≠ 0 → Matrix.toEuclideanLin (Ψ μ t) v ≠ 0) ∧
      (∀ μ α, Continuous (θ μ α)) ∧ (∀ μ α, θ μ α 0 = α) ∧
      (∀ μ α t, θ μ (α + 2 * π) t = θ μ α t + 2 * π) ∧
      (∀ (μ α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) → ∀ t,
        vecToC (Matrix.toEuclideanLin (Ψ μ t) v) =
          (‖vecToC (Matrix.toEuclideanLin (Ψ μ t) v)‖ : ℂ) *
            Complex.exp (θ μ α t * Complex.I)) ∧
      Continuous (fun p : ℝ × ℝ => θ p.1 p.2 1) ∧
      ∀ μ α, |θ μ α 1 - α - μ| ≤ C := by
  -- nonvanishing
  have hsymm : ∀ μ t : ℝ, (Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)).IsSymm := fun μ t =>
    (hSinf.2.2 t).add (Matrix.isSymm_one.smul μ)
  have hne : ∀ (μ t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ μ t) v ≠ 0 := by
    intro μ t v hv h
    have hdet : IsUnit (Ψ μ t).det := SymplecticGroup.symplectic_det
      (CauchyRiemannIndex.fundamentalSolution_symplectic 1 _ (hsymm μ) (Ψ μ) (hΨ μ) t)
    apply hv
    have : Matrix.toEuclideanLin ((Ψ μ t)⁻¹ * Ψ μ t) v = 0 := by
      rw [Matrix.toLpLin_mul, LinearMap.comp_apply, h, map_zero]
    rwa [Matrix.nonsing_inv_mul _ hdet, Matrix.toLpLin_one, LinearMap.id_apply] at this
  have hneC : ∀ (μ t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → vecToC (Matrix.toEuclideanLin (Ψ μ t) v) ≠ 0 := by
    intro μ t v hv h
    apply hne μ t v hv
    apply wx_vecToC_inj
    rw [h]
    exact Complex.ext (by simp [vecToC]) (by simp [vecToC])
  -- derivative
  have hx : ∀ (μ : ℝ) (w : CauchyRiemannIndex.Vec 1) (t : ℝ),
      HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ μ t) w)
        (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * (Sinf t + μ • 1))
          (Matrix.toEuclideanLin (Ψ μ t) w)) t := by
    intro μ w t
    let _ : NormedAddCommGroup (CauchyRiemannIndex.Mat 1) := Matrix.normedAddCommGroup
    let _ : NormedSpace ℝ (CauchyRiemannIndex.Mat 1) := Matrix.normedSpace
    let Lw : CauchyRiemannIndex.Mat 1 →ₗ[ℝ] CauchyRiemannIndex.Vec 1 :=
      { toFun := fun N => Matrix.toEuclideanLin N w
        map_add' := fun N N' => by simp
        map_smul' := fun c N => by simp }
    have h := (LinearMap.toContinuousLinearMap Lw).hasFDerivAt.comp_hasDerivAt t ((hΨ μ).2 t)
    refine h.congr_deriv ?_
    show Matrix.toEuclideanLin _ w = _
    rw [Matrix.toLpLin_mul, LinearMap.comp_apply]
  -- the operator family
  set B : (ℝ × ℝ) × ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 := fun p =>
    LinearMap.toContinuousLinearMap
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * (Sinf p.2 + p.1.1 • 1))) with hBdef
  have hB : Continuous B := by
    let Φl : CauchyRiemannIndex.Mat 1 →ₗ[ℝ]
        (CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1) :=
      { toFun := fun N => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
        map_add' := fun N N' => by ext x : 1; simp
        map_smul' := fun c N => by ext x : 1; simp }
    have hM : Continuous fun p : (ℝ × ℝ) × ℝ =>
        CauchyRiemannIndex.J₀ 1 * (Sinf p.2 + p.1.1 • (1 : CauchyRiemannIndex.Mat 1)) :=
      continuous_const.matrix_mul ((hSinf.1.comp continuous_snd).add
        ((continuous_fst.comp continuous_fst).smul continuous_const))
    exact (LinearMap.continuous_of_finiteDimensional Φl).comp hM
  set v : ℝ → CauchyRiemannIndex.Vec 1 := fun α => wxOfC (Complex.exp (α * Complex.I)) with hvdef
  have hv0 : ∀ α, v α ≠ 0 := by
    intro α h
    have h1 : vecToC (v α) = Complex.exp (α * Complex.I) := wx_vecToC_ofC _
    rw [h] at h1
    exact Complex.exp_ne_zero _ (h1.symm.trans (Complex.ext (by simp [vecToC]) (by simp [vecToC])))
  set x : ℝ → ℝ → ℝ → CauchyRiemannIndex.Vec 1 := fun μ α t =>
    Matrix.toEuclideanLin (Ψ μ t) (v α) with hxdef
  set X : ℝ → ℝ → ℝ → ℂ := fun μ α t => vecToC (x μ α t) with hXdef
  set Xd : ℝ → ℝ → ℝ → ℂ := fun μ α t => vecToC (B ((μ, α), t) (x μ α t)) with hXddef
  have hXder : ∀ μ α t, HasDerivAt (X μ α) (Xd μ α t) t := fun μ α t =>
    wxVecToCL.hasFDerivAt.comp_hasDerivAt t (hx μ (v α) t)
  have hX0 : ∀ μ α t, X μ α t ≠ 0 := fun μ α t => hneC μ t (v α) (hv0 α)
  have hXstart : ∀ μ α, X μ α 0 = Complex.exp (α * Complex.I) := by
    intro μ α
    simp only [hXdef, hxdef, (hΨ μ).1, Matrix.toLpLin_one, LinearMap.id_apply, hvdef]
    exact wx_vecToC_ofC _
  -- joint continuity
  have hjc : Continuous fun p : (ℝ × ℝ) × unitInterval => x p.1.1 p.1.2 p.2 :=
    CauchyRiemannIndex.linearODE_continuous_param B hB (fun τ => v τ.2)
      (wx_continuous_ofC.comp (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)))
      (fun τ => x τ.1 τ.2) (fun τ => by simp [hxdef, (hΨ τ.1).1])
      (fun τ t => hx τ.1 (v τ.2) t)
  have hxc : ∀ μ α, Continuous (x μ α) := fun μ α =>
    continuous_iff_continuousAt.2 fun t => (hx μ (v α) t).continuousAt
  have hXdc : ∀ μ α, Continuous (Xd μ α) := fun μ α =>
    wxVecToCL.continuous.comp ((hB.comp (continuous_const.prodMk continuous_id)).clm_apply
      (hxc μ α))
  -- the angle
  set W : ℝ → ℝ → ℝ → ℂ := fun μ α t => ∫ s in (0 : ℝ)..t, Xd μ α s / X μ α s with hWdef
  set θ : ℝ → ℝ → ℝ → ℝ := fun μ α t => α + (W μ α t).im with hθdef
  have hXc : ∀ μ α, Continuous (X μ α) := fun μ α =>
    continuous_iff_continuousAt.2 fun t => (hXder μ α t).continuousAt
  have hq : ∀ μ α, Continuous fun s => Xd μ α s / X μ α s := fun μ α =>
    (hXdc μ α).div (hXc μ α) (hX0 μ α)
  have hWc : ∀ μ α, Continuous (W μ α) := fun μ α =>
    continuous_iff_continuousAt.2 fun t =>
      ((hq μ α).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  have hrep : ∀ μ α t, X μ α t = (‖X μ α t‖ : ℂ) * Complex.exp (θ μ α t * Complex.I) := by
    intro μ α t
    have hL := eq_mul_exp_integral_div_of_hasDerivAt (hXder μ α) (hXdc μ α) (hX0 μ α) t
    rw [hXstart] at hL
    have hW : W μ α t = ((W μ α t).re : ℂ) + ((W μ α t).im : ℂ) * Complex.I :=
      (Complex.re_add_im _).symm
    have hexp : Complex.exp (α * Complex.I) * Complex.exp (W μ α t) =
        (Real.exp (W μ α t).re : ℂ) * Complex.exp (θ μ α t * Complex.I) := by
      rw [← Complex.exp_add, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      conv_lhs => rw [hW]
      simp only [hθdef, Complex.ofReal_add]
      ring
    have hnorm : ‖X μ α t‖ = Real.exp (W μ α t).re := by
      rw [hL, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_exp, one_mul]
    rw [hnorm]
    exact hL.trans hexp
  -- bound on `S∞`
  set K : ℝ → ℝ := fun t =>
    |Sinf t (Sum.inl 0) (Sum.inl 0)| + |Sinf t (Sum.inl 0) (Sum.inr 0)| +
      |Sinf t (Sum.inr 0) (Sum.inl 0)| + |Sinf t (Sum.inr 0) (Sum.inr 0)| with hKdef
  have hKc : Continuous K := by
    have he : ∀ i j, Continuous fun t => Sinf t i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hSinf.1)
    simp only [hKdef]
    fun_prop
  have hKper : Function.Periodic K 1 := fun t => by simp only [hKdef, hSinf.2.1 t]
  obtain ⟨C₀, hC₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hKc.continuousOn
  have hK : ∀ t, K t ≤ C₀ := by
    intro t
    have h := hKper.sub_int_mul_eq (n := ⌊t⌋) (x := t)
    rw [mul_one] at h
    rw [← h]
    have hm : t - ⌊t⌋ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC₀ _ hm)
  have hpt : ∀ μ α s, |(Xd μ α s / X μ α s).im - μ| ≤ C₀ := by
    intro μ α s
    have hform : Xd μ α s = Complex.I *
        (vecToC (Matrix.toEuclideanLin (Sinf s) (x μ α s)) + μ * X μ α s) := by
      simp only [hXddef, hBdef, LinearMap.coe_toContinuousLinearMap']
      exact wx_vecToC_J _ _ _
    have hXne := hX0 μ α s
    have hdiv : Xd μ α s / X μ α s =
        Complex.I * (vecToC (Matrix.toEuclideanLin (Sinf s) (x μ α s)) / X μ α s + μ) := by
      rw [hform]; field_simp
    have him : (Xd μ α s / X μ α s).im - μ =
        (vecToC (Matrix.toEuclideanLin (Sinf s) (x μ α s)) / X μ α s).re := by
      rw [hdiv]; simp
    rw [him]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 hXne)]
    exact (wx_norm_vecToC_le _ _).trans (mul_le_mul_of_nonneg_right (hK s) (norm_nonneg _))
  -- continuity of the endpoint angle
  set G : (ℝ × ℝ) × unitInterval → ℂ := fun p =>
    vecToC (B (p.1, p.2) (x p.1.1 p.1.2 p.2)) / vecToC (x p.1.1 p.1.2 p.2) with hGdef
  have hGc : Continuous G := by
    have hBc : Continuous fun p : (ℝ × ℝ) × unitInterval => B (p.1, (p.2 : ℝ)) :=
      hB.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact (wxVecToCL.continuous.comp (hBc.clm_apply hjc)).div (wxVecToCL.continuous.comp hjc)
      fun p => hX0 p.1.1 p.1.2 p.2
  set F : ℝ × ℝ → ℝ → ℂ := fun p s => G (p, Set.projIcc 0 1 zero_le_one s) with hFdef
  have hFc : Continuous (Function.uncurry F) :=
    hGc.comp (continuous_fst.prodMk (continuous_projIcc.comp continuous_snd))
  have hFW : ∀ p : ℝ × ℝ, ∫ s in (0 : ℝ)..1, F p s = W p.1 p.2 1 := by
    intro p
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    simp only [hFdef, hGdef, Set.projIcc_of_mem _ hs]
    rfl
  have hθ1c : Continuous fun p : ℝ × ℝ => θ p.1 p.2 1 := by
    have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := MeasureTheory.volume) hFc 0 1
    simp only [hθdef]
    refine continuous_snd.add (Complex.continuous_im.comp ?_)
    simpa only [hFW] using h
  refine ⟨C₀, θ, hne, fun μ α => continuous_const.add (Complex.continuous_im.comp (hWc μ α)),
    fun μ α => by simp [hθdef, hWdef], ?_, ?_, hθ1c, ?_⟩
  · intro μ α t
    have hv2 : v (α + 2 * π) = v α := by
      simp only [hvdef]
      congr 1
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      have : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I := by push_cast; ring
      rw [this, Complex.exp_two_pi_mul_I, mul_one]
    simp only [hθdef, hWdef, hXddef, hXdef, hxdef, hv2]
    ring
  · intro μ α w hw t
    have : w = v α := by
      apply wx_vecToC_inj
      rw [hw]; exact (wx_vecToC_ofC _).symm
    subst this
    exact hrep μ α t
  · intro μ α
    have hint : (W μ α 1).im = ∫ s in (0 : ℝ)..1, (Xd μ α s / X μ α s).im := by
      have := Complex.imCLM.intervalIntegral_comp_comm
        ((hq μ α).intervalIntegrable (μ := MeasureTheory.volume) 0 1)
      simpa [hWdef] using this.symm
    have heq : θ μ α 1 - α - μ = ∫ s in (0 : ℝ)..1, ((Xd μ α s / X μ α s).im - μ) := by
      have hs := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := 0) (b := 1)
        (f := fun s => (Xd μ α s / X μ α s).im) (g := fun _ => μ)
        ((Complex.continuous_im.comp (hq μ α)).intervalIntegrable 0 1) intervalIntegrable_const
      rw [hs, intervalIntegral.integral_const, ← hint]
      simp [hθdef]
    rw [heq]
    have := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := 1) (C := C₀) (f := fun s => (Xd μ α s / X μ α s).im - μ)
      (fun s _ => by rw [Real.norm_eq_abs]; exact hpt μ α s)
    simpa [Real.norm_eq_abs] using this

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped Real

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (Ψ : ℝ → ℝ → CauchyRiemannIndex.Mat 1)
    (hΨ : ∀ μ, CauchyRiemannIndex.IsFundamentalSolution
      (fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1)) (Ψ μ)) :
    ∃ (C : ℝ) (θ : ℝ → ℝ → ℝ → ℝ),
      (∀ (μ t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (Ψ μ t) v ≠ 0) ∧
      (∀ μ α, Continuous (θ μ α)) ∧ (∀ μ α, θ μ α 0 = α) ∧
      (∀ μ α t, θ μ (α + 2 * π) t = θ μ α t + 2 * π) ∧
      (∀ (μ α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) → ∀ t,
        vecToC (Matrix.toEuclideanLin (Ψ μ t) v) =
          (‖vecToC (Matrix.toEuclideanLin (Ψ μ t) v)‖ : ℂ) *
            Complex.exp (θ μ α t * Complex.I)) ∧
      Continuous (fun p : ℝ × ℝ => θ p.1 p.2 1) ∧
      ∀ μ α, |θ μ α 1 - α - μ| ≤ C :=
  exists_angle_fundamentalSolution_aux Sinf hSinf Ψ hΨ
