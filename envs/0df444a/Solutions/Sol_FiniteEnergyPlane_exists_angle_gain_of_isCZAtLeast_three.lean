-- Prove2me | solution 1 for FiniteEnergyPlane.exists_angle_gain_of_isCZAtLeast_three
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-21T13:40:49.380969+00:00
-- url     : https://prove2.me/submissions/858897ba-ff84-4f95-aca0-68676dfbd24a

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
import Theorems.Thm_FiniteEnergyPlane_eq_mul_exp_integral_div_of_hasDerivAt
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_FiniteEnergyPlane_periodicOrbit_bridge
import Theorems.Thm_FiniteEnergyPlane_asympOp_frame_bridge
import Theorems.Thm_FiniteEnergyPlane_lt_of_mem_windingInterval_linearizedXiPath
import Theorems.Thm_HryniewiczCriterion_linearizedXiPath_isSymplecticPath
import Theorems.Thm_HryniewiczCriterion_windingInterval_narrow
import Theorems.Thm_HryniewiczCriterion_czIndexOfPath_ge_three_iff
import Mathlib.Analysis.Calculus.Deriv.Shift
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique



/-!
# Base layer for `exists_angle_gain_of_isCZAtLeast_three` (25370c3f)

Lifts of nowhere-vanishing paths, uniqueness for `ζ' = J₀ S∞ ζ`, a Lipschitz angle of a solution,
and the bridge between `vecToC` and `rotationVector`.
-/

namespace FiniteEnergyPlane

open Matrix
open scoped Real ContDiff

noncomputable section

/-- `ℂ → ℝ²`, the inverse of `vecToC`. -/
def agOfC (z : ℂ) : CauchyRiemannIndex.Vec 1 :=
  z.re • EuclideanSpace.single (Sum.inl 0) 1 + z.im • EuclideanSpace.single (Sum.inr 0) 1

theorem ag_vecToC_ofC (z : ℂ) : vecToC (agOfC z) = z := by
  apply Complex.ext <;> simp [vecToC, agOfC, EuclideanSpace.single_apply]

theorem ag_vecToC_inj {v w : CauchyRiemannIndex.Vec 1} (h : vecToC v = vecToC w) : v = w := by
  have h1 : v (Sum.inl 0) = w (Sum.inl 0) := congrArg Complex.re h
  have h2 : v (Sum.inr 0) = w (Sum.inr 0) := congrArg Complex.im h
  ext i
  rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> assumption

theorem ag_vecToC_smul (c : ℝ) (v : CauchyRiemannIndex.Vec 1) :
    vecToC (c • v) = (c : ℂ) * vecToC v := by
  apply Complex.ext <;> simp [vecToC]

theorem ag_vecToC_zero : vecToC (0 : CauchyRiemannIndex.Vec 1) = 0 := by
  apply Complex.ext <;> simp [vecToC]

/-- `vecToC` as a continuous `ℝ`-linear map. -/
def agVecToCL : CauchyRiemannIndex.Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun v w => Complex.ext (by simp [vecToC]) (by simp [vecToC])
      map_smul' := fun c v => Complex.ext (by simp [vecToC]) (by simp [vecToC]) }

theorem ag_vecToCL_apply (v : CauchyRiemannIndex.Vec 1) : agVecToCL v = vecToC v := rfl

/-- The operator `J₀ S(t)` as a continuous linear map. -/
def agB (S : ℝ → CauchyRiemannIndex.Mat 1) (t : ℝ) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1 :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t))

theorem ag_B_apply (S : ℝ → CauchyRiemannIndex.Mat 1) (t : ℝ) (v : CauchyRiemannIndex.Vec 1) :
    agB S t v = Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) v := rfl

theorem ag_B_continuous (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S) :
    Continuous (agB S) := by
  let Φl : CauchyRiemannIndex.Mat 1 →ₗ[ℝ]
      (CauchyRiemannIndex.Vec 1 →L[ℝ] CauchyRiemannIndex.Vec 1) :=
    { toFun := fun N => LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin N)
      map_add' := fun N N' => by ext x : 1; simp
      map_smul' := fun c N => by ext x : 1; simp }
  have hM : Continuous fun t => CauchyRiemannIndex.J₀ 1 * S t :=
    continuous_const.matrix_mul hS
  exact (LinearMap.continuous_of_finiteDimensional Φl).comp hM

/-- Uniqueness for `ζ' = J₀ S ζ`. -/
theorem ag_sol_unique (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S)
    {ζ ζ' : ℝ → CauchyRiemannIndex.Vec 1}
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t)
    (hζ' : ∀ t, HasDerivAt ζ' (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ' t)) t)
    (h0 : ζ 0 = ζ' 0) : ζ = ζ' := by
  obtain ⟨x, -, hx⟩ := AsymptoticOperator.linearODE_existsUnique (agB S) (ag_B_continuous S hS) (ζ 0)
  have e1 := hx ζ ⟨rfl, hζ⟩
  have e2 := hx ζ' ⟨h0.symm, hζ'⟩
  rw [e1, e2]

/-- `t ↦ Ψ(t) w` solves `ζ' = J₀ S ζ`. -/
theorem ag_fund_apply_hasDerivAt (S : ℝ → CauchyRiemannIndex.Mat 1)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution S Ψ)
    (w : CauchyRiemannIndex.Vec 1) (t : ℝ) :
    HasDerivAt (fun t => Matrix.toEuclideanLin (Ψ t) w)
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t)
        (Matrix.toEuclideanLin (Ψ t) w)) t := by
  let _ : NormedAddCommGroup (CauchyRiemannIndex.Mat 1) := Matrix.normedAddCommGroup
  let _ : NormedSpace ℝ (CauchyRiemannIndex.Mat 1) := Matrix.normedSpace
  let Lw : CauchyRiemannIndex.Mat 1 →ₗ[ℝ] CauchyRiemannIndex.Vec 1 :=
    { toFun := fun N => Matrix.toEuclideanLin N w
      map_add' := fun N N' => by simp
      map_smul' := fun c N => by simp }
  have h := (LinearMap.toContinuousLinearMap Lw).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)
  refine h.congr_deriv ?_
  show Matrix.toEuclideanLin _ w = _
  rw [Matrix.toLpLin_mul, LinearMap.comp_apply]

/-- `Ψ(t)` is injective. -/
theorem ag_fund_apply_ne_zero (S : ℝ → CauchyRiemannIndex.Mat 1) (hSym : ∀ t, (S t).IsSymm)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution S Ψ)
    (t : ℝ) (v : CauchyRiemannIndex.Vec 1) (hv : v ≠ 0) :
    Matrix.toEuclideanLin (Ψ t) v ≠ 0 := by
  intro h
  have hdet : IsUnit (Ψ t).det := SymplecticGroup.symplectic_det
    (CauchyRiemannIndex.fundamentalSolution_symplectic 1 _ hSym Ψ hΨ t)
  apply hv
  have : Matrix.toEuclideanLin ((Ψ t)⁻¹ * Ψ t) v = 0 := by
    rw [Matrix.toLpLin_mul, LinearMap.comp_apply, h, map_zero]
  rwa [Matrix.nonsing_inv_mul _ hdet, Matrix.toLpLin_one, LinearMap.id_apply] at this

/-- Solutions are `Ψ(t) ζ(k)` after an integer shift. -/
theorem ag_shift_eq (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S)
    (hper : Function.Periodic S 1)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution S Ψ)
    {ζ : ℝ → CauchyRiemannIndex.Vec 1}
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t)
    (k : ℤ) (t : ℝ) : ζ (t + k) = Matrix.toEuclideanLin (Ψ t) (ζ k) := by
  have hpk : ∀ t, S (t + k) = S t := fun t => by
    have := (hper.int_mul k) t
    simpa using this
  have h1 : ∀ t, HasDerivAt (fun t => ζ (t + k))
      (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ (t + k))) t := fun t => by
    have := (hζ (t + k)).comp_add_const t (k : ℝ)
    rw [hpk] at this
    exact this
  have h := ag_sol_unique S hS h1 (ag_fund_apply_hasDerivAt S Ψ hΨ (ζ k)) (by
    simp [hΨ.1])
  exact congrFun h t

/-- Two continuous lifts of the argument of a nowhere-vanishing path differ by a constant. -/
theorem ag_lift_sub_const {f : ℝ → ℂ} (hf0 : ∀ t, f t ≠ 0) {θ θ' : ℝ → ℝ}
    (hθc : Continuous θ) (hθc' : Continuous θ')
    (hθ : ∀ t, f t = (‖f t‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (hθ' : ∀ t, f t = (‖f t‖ : ℂ) * Complex.exp ((θ' t : ℂ) * Complex.I)) (t : ℝ) :
    θ t - θ' t = θ 0 - θ' 0 := by
  have hpi := Real.pi_pos
  have hint : ∀ t, ∃ n : ℤ, θ t - θ' t = 2 * π * n := by
    intro t
    have hn : (‖f t‖ : ℂ) ≠ 0 := by simpa using hf0 t
    have he : Complex.exp ((θ t : ℂ) * Complex.I) = Complex.exp ((θ' t : ℂ) * Complex.I) :=
      mul_left_cancel₀ hn ((hθ t).symm.trans (hθ' t))
    have he1 : Complex.exp (((θ t - θ' t : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 he1
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  set g : ℝ → ℝ := fun t => (θ t - θ' t) / (2 * π) with hg
  have hgc : Continuous g := (hθc.sub hθc').div_const _
  have hgint : ∀ t, ∃ n : ℤ, g t = n := by
    intro t
    obtain ⟨n, hn⟩ := hint t
    refine ⟨n, ?_⟩
    simp only [hg, hn]
    field_simp
  have hgt : g t = g 0 := by
    obtain ⟨n₀, hn₀⟩ := hgint 0
    obtain ⟨n₁, hn₁⟩ := hgint t
    by_contra hne
    have hne' : n₀ ≠ n₁ := fun h => hne (by rw [hn₀, hn₁, h])
    have hmem : ((min n₀ n₁ : ℤ) : ℝ) + 1 / 2 ∈ Set.uIcc (g 0) (g t) := by
      rw [hn₀, hn₁]
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · have : ((n₀ : ℝ) + 1) ≤ n₁ := by exact_mod_cast hlt
        rw [min_eq_left hlt.le, Set.uIcc_of_le (by exact_mod_cast hlt.le)]
        constructor <;> linarith
      · have : ((n₁ : ℝ) + 1) ≤ n₀ := by exact_mod_cast hlt
        rw [min_eq_right hlt.le, Set.uIcc_of_ge (by exact_mod_cast hlt.le)]
        constructor <;> linarith
    obtain ⟨c, -, hc⟩ := intermediate_value_uIcc hgc.continuousOn hmem
    obtain ⟨m, hm⟩ := hgint c
    rw [hm] at hc
    have h2 : (m : ℝ) * 2 = ((min n₀ n₁ : ℤ) : ℝ) * 2 + 1 := by linarith
    have h3 : m * 2 = min n₀ n₁ * 2 + 1 := by exact_mod_cast h2
    omega
  simp only [hg] at hgt
  field_simp at hgt
  linarith

/-- The norm bound for `vecToC (S w)`. -/
theorem ag_norm_vecToC_le (S : CauchyRiemannIndex.Mat 1) (w : CauchyRiemannIndex.Vec 1) :
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

theorem ag_vecToC_J (S : CauchyRiemannIndex.Mat 1) (w : CauchyRiemannIndex.Vec 1) :
    vecToC (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S) w) =
      Complex.I * vecToC (Matrix.toEuclideanLin S w) := by
  apply Complex.ext <;>
  simp [vecToC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.J, Matrix.fromBlocks, Matrix.mul_apply, Matrix.one_apply] <;> ring

/-- A Lipschitz angle for every nowhere-vanishing solution of `ζ' = J₀ S ζ`, with a constant
depending only on the loop `S`. -/
theorem ag_exists_angle (S : ℝ → CauchyRiemannIndex.Mat 1) (hS : Continuous S)
    (hper : Function.Periodic S 1) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t) →
      (∀ t, ζ t ≠ 0) →
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, vecToC (ζ t) = (‖vecToC (ζ t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) ∧
        ∀ s t, s ≤ t → |θ t - θ s| ≤ C₀ * (t - s) := by
  -- bound on `S`
  set K : ℝ → ℝ := fun t =>
    |S t (Sum.inl 0) (Sum.inl 0)| + |S t (Sum.inl 0) (Sum.inr 0)| +
      |S t (Sum.inr 0) (Sum.inl 0)| + |S t (Sum.inr 0) (Sum.inr 0)| with hKdef
  have hKc : Continuous K := by
    have he : ∀ i j, Continuous fun t => S t i j := fun i j =>
      (continuous_apply j).comp ((continuous_apply i).comp hS)
    simp only [hKdef]
    fun_prop
  have hKper : Function.Periodic K 1 := fun t => by simp only [hKdef, hper t]
  obtain ⟨C₁, hC₁⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hKc.continuousOn
  set C₀ := max C₁ 0 with hC₀
  have hK : ∀ t, K t ≤ C₀ := by
    intro t
    have h := hKper.sub_int_mul_eq (n := ⌊t⌋) (x := t)
    rw [mul_one] at h
    rw [← h]
    have hm : t - ⌊t⌋ ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩
    exact ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC₁ _ hm)).trans
      (le_max_left _ _)
  refine ⟨C₀, le_max_right _ _, fun ζ hζ hζ0 => ?_⟩
  have hζc : Continuous ζ := continuous_iff_continuousAt.2 fun t => (hζ t).continuousAt
  set X : ℝ → ℂ := fun t => vecToC (ζ t) with hXdef
  set Xd : ℝ → ℂ := fun t => vecToC (agB S t (ζ t)) with hXddef
  have hXder : ∀ t, HasDerivAt X (Xd t) t := fun t =>
    agVecToCL.hasFDerivAt.comp_hasDerivAt t (hζ t)
  have hXdc : Continuous Xd :=
    agVecToCL.continuous.comp ((ag_B_continuous S hS).clm_apply hζc)
  have hX0 : ∀ t, X t ≠ 0 := fun t h => hζ0 t (ag_vecToC_inj (h.trans ag_vecToC_zero.symm))
  have hXc : Continuous X := continuous_iff_continuousAt.2 fun t => (hXder t).continuousAt
  have hq : Continuous fun s => Xd s / X s := hXdc.div hXc hX0
  set W : ℝ → ℂ := fun t => ∫ s in (0 : ℝ)..t, Xd s / X s with hWdef
  set α₀ : ℝ := Complex.arg (X 0)
  set θ : ℝ → ℝ := fun t => α₀ + (W t).im with hθdef
  have hWc : Continuous W := continuous_iff_continuousAt.2 fun t =>
    (hq.integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt
  refine ⟨θ, continuous_const.add (Complex.continuous_im.comp hWc), ?_, ?_⟩
  · intro t
    have hL := eq_mul_exp_integral_div_of_hasDerivAt hXder hXdc hX0 t
    have hst : X 0 = (‖X 0‖ : ℂ) * Complex.exp (α₀ * Complex.I) :=
      (Complex.norm_mul_exp_arg_mul_I (X 0)).symm
    have hW : W t = ((W t).re : ℂ) + ((W t).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
    have hexp : X 0 * Complex.exp (W t) =
        ((‖X 0‖ * Real.exp (W t).re : ℝ) : ℂ) * Complex.exp (θ t * Complex.I) := by
      conv_lhs => rw [hst]
      rw [mul_assoc, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc,
        ← Complex.exp_add]
      congr 2
      conv_lhs => rw [hW]
      simp only [hθdef, Complex.ofReal_add]
      ring
    have hnorm : ‖X t‖ = ‖X 0‖ * Real.exp (W t).re := by
      rw [hL, norm_mul, Complex.norm_exp]
    show X t = _
    rw [hnorm]
    exact hL.trans hexp
  · intro s t hst
    have hpt : ∀ u, ‖(Xd u / X u).im‖ ≤ C₀ := by
      intro u
      have hform : Xd u = Complex.I * vecToC (Matrix.toEuclideanLin (S u) (ζ u)) := by
        simp only [hXddef, ag_B_apply]
        exact ag_vecToC_J _ _
      have hdiv : Xd u / X u = Complex.I * (vecToC (Matrix.toEuclideanLin (S u) (ζ u)) / X u) := by
        rw [hform]; ring
      rw [hdiv, Real.norm_eq_abs]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (hX0 u))]
      exact (ag_norm_vecToC_le _ _).trans (mul_le_mul_of_nonneg_right (hK u) (norm_nonneg _))
    have hii : ∀ a b : ℝ, (∫ u in a..b, Xd u / X u).im = ∫ u in a..b, (Xd u / X u).im := by
      intro a b
      have := Complex.imCLM.intervalIntegral_comp_comm
        (hq.intervalIntegrable (μ := MeasureTheory.volume) a b)
      simpa using this.symm
    have hdiff : θ t - θ s = ∫ u in s..t, (Xd u / X u).im := by
      have h := intervalIntegral.integral_interval_sub_left (μ := MeasureTheory.volume)
        (hq.intervalIntegrable 0 t) (hq.intervalIntegrable 0 s)
      simp only [hθdef, hWdef]
      rw [← hii, ← h, Complex.sub_im]
      ring
    rw [hdiff]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := C₀)
      (f := fun u => (Xd u / X u).im) (fun u _ => hpt u)
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hst)] at this
    linarith

end

end FiniteEnergyPlane

/-!
# CZ layer for `exists_angle_gain_of_isCZAtLeast_three` (25370c3f)

`S∞` is smooth, `μ_CZ ≥ 3` bounds the winding interval of `Ψ` below by some `a > 1`, and a
solution turns by an element of that interval over every integer period.
-/

namespace FiniteEnergyPlane

open Matrix
open scoped Real ContDiff

noncomputable section

/-! ### Smoothness of `S∞` -/

theorem ag_frame_injective {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z) (t : ℝ) :
    Function.Injective (Z t) := by
  intro a a' h
  have h0 : Z t (a - a') = 0 := by rw [map_sub, h, sub_self]
  set x := Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (a - a') with hx
  have hin := (hZ.2.2 t).2.2.2 (a - a') x
  rw [h0] at hin
  have hz : omega0 (0 : V 1) (Z t x) = 0 := by
    simp [omega0, dot, j0]
  rw [hz] at hin
  have hx0 : x = 0 := inner_self_eq_zero.1 hin.symm
  have hJJ : Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) x = -(a - a') := by
    rw [hx, ← LinearMap.comp_apply, ← Matrix.toLpLin_mul, CauchyRiemannIndex.J₀, Matrix.J_squared,
      map_neg, Matrix.toLpLin_one]
    rfl
  rw [hx0, map_zero] at hJJ
  have : a - a' = 0 := neg_eq_zero.1 hJJ.symm
  exact sub_eq_zero.1 this

theorem ag_Sinf_eq {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {P : ReebOrbit H}
    {Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1} (hZ : IsUnitaryXiFrame J P Z)
    (S S' : ℝ → CauchyRiemannIndex.Mat 1)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (S t) (η t)))
    (hA' : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (S' t) (η t))) : S = S' := by
  funext t
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro c
  have e := (hA (fun _ => c) contDiff_const (fun _ => rfl) t).symm.trans
    (hA' (fun _ => c) contDiff_const (fun _ => rfl) t)
  have e2 := ag_frame_injective hZ t e
  simpa using e2

theorem ag_Sinf_contDiff (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) :
    ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j) := by
  obtain ⟨S', -, hS', hA', -⟩ := (asympOp_frame_bridge H hH J hJ P).2 Z hZ
  rw [ag_Sinf_eq hZ Sinf S' hA hA']
  exact hS'

theorem ag_contDiff_fund (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ) :
    ∀ i j, ContDiff ℝ ∞ (fun t => Ψ t i j) := by
  have hd : ∀ i j t, HasDerivAt (fun t => Ψ t i j)
      ((CauchyRiemannIndex.J₀ 1 * Sinf t * Ψ t) i j) t := fun i j t =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 (hΨ.2 t) i) j
  have hn : ∀ n : ℕ, ∀ i j, ContDiff ℝ n (fun t => Ψ t i j) := by
    intro n
    induction n with
    | zero =>
      intro i j
      simpa using continuous_iff_continuousAt.2 fun t => (hd i j t).continuousAt
    | succ n ih =>
      intro i j
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun t => (hd i j t).differentiableAt, by simp, ?_⟩
      have he : deriv (fun t => Ψ t i j) = fun t => (CauchyRiemannIndex.J₀ 1 * Sinf t * Ψ t) i j :=
        funext fun t => (hd i j t).deriv
      rw [he]
      simp only [Matrix.mul_apply]
      refine ContDiff.sum fun l _ => ContDiff.mul (ContDiff.sum fun m _ => ?_) (ih l j)
      exact contDiff_const.mul ((hS m l).of_le (by exact_mod_cast le_top))
  intro i j
  exact contDiff_infty.2 fun n => hn n i j

lemma ag_det_symp (A : CauchyRiemannIndex.Mat 1) (hA : CauchyRiemannIndex.IsSymplectic A) :
    A.det = 1 := by
  have h := (SymplecticGroup.mem_iff (A := A)).1 hA
  have h' := congrFun (congrFun h (Sum.inl 0 : Fin 1 ⊕ Fin 1)) (Sum.inr 0 : Fin 1 ⊕ Fin 1)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.transpose_apply] at h'
  have hd : A.det = A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
      A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) := by
    rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
    rfl
  rw [hd]
  linarith

/-- The winding interval of `Ψ` is `[a, b]` with `b - a < 1/2`. -/
theorem ag_narrow (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hS : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ) :
    ∃ a b : ℝ, a ≤ b ∧ HryniewiczCriterion.windingInterval
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) = Set.Icc a b := by
  have hsmooth : ContDiffOn ℝ ∞ (fun t i j =>
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ t) : Matrix (Fin 2) (Fin 2) ℝ) i j)
      (Set.Icc 0 1) := by
    refine ContDiff.contDiffOn ?_
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    exact ag_contDiff_fund Sinf hS Ψ hΨ _ _
  have hdet : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ t) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 :=
    fun t _ => by
      rw [Matrix.det_reindex_self]
      exact ag_det_symp _ (CauchyRiemannIndex.fundamentalSolution_symplectic 1 Sinf hSym.2.2 Ψ hΨ t)
  have h0 : (Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ 0) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [hΨ.1]; simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  obtain ⟨a, b, hab, hw, -⟩ := HryniewiczCriterion.windingInterval_narrow _ hsmooth hdet h0
  exact ⟨a, b, hab, hw⟩

/-! ### From `μ_CZ ≥ 3` to the winding interval of `Ψ` -/

lemma ag_contDiff_hamiltonianVectorField (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH : ContDiff ℝ ∞ H₀) : ContDiff ℝ 1 (HryniewiczCriterion.hamiltonianVectorField H₀) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ H₀) := hH.fderiv_right (by norm_cast)
  have hp : ∀ i : Fin 4, ContDiff ℝ 1 (fun x => HryniewiczCriterion.partialDeriv H₀ x i) :=
    fun i => hd.clm_apply contDiff_const
  refine contDiff_pi.2 fun i => ?_
  fin_cases i
  · exact (hp 1).neg
  · exact hp 0
  · exact (hp 3).neg
  · exact hp 2

lemma ag_exists_isLinearizedFlow (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀)
    (P : HryniewiczCriterion.PeriodicOrbit H₀) :
    ∃ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
      HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y := by
  have hx : Continuous P.x :=
    continuous_iff_continuousAt.2 fun t => (P.trajectory.1 t).continuousAt
  have hA : Continuous fun t =>
      fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField H₀) (P.x t) :=
    ((ag_contDiff_hamiltonianVectorField H₀ hH₀.1).continuous_fderiv (by simp)).comp hx
  let B : ℝ → ((HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4) →L[ℝ]
      (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4)) := fun t =>
    ContinuousLinearMap.compL ℝ HryniewiczCriterion.R4 HryniewiczCriterion.R4
      HryniewiczCriterion.R4 (fderiv ℝ (HryniewiczCriterion.hamiltonianVectorField H₀) (P.x t))
  have hB : Continuous B := (ContinuousLinearMap.compL ℝ HryniewiczCriterion.R4
      HryniewiczCriterion.R4 HryniewiczCriterion.R4).continuous.comp hA
  obtain ⟨Y, ⟨hY0, hY⟩, -⟩ :=
    AsymptoticOperator.linearODE_existsUnique B hB (ContinuousLinearMap.id ℝ _)
  exact ⟨Y, hY0, hY⟩

theorem ag_wind_gt_one (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ) :
    ∀ d ∈ HryniewiczCriterion.windingInterval
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)), (1 : ℝ) < d := by
  set H₀ : HryniewiczCriterion.R4 → ℝ := fun x => H (ofR4 x) with hH₀def
  have hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀ := (periodicOrbit_bridge H₀).1.1 hH
  obtain ⟨R, hRr, hRT⟩ := (periodicOrbit_bridge H₀).2 hH₀ |>.2 P
  obtain ⟨c, hc⟩ : ∃ c, ofR4 (R.x c) = P.x 0 := by
    have : P.x 0 ∈ Set.range (fun τ => ofR4 (R.x τ)) := hRr ▸ ⟨0, rfl⟩
    exact this
  let R' : HryniewiczCriterion.PeriodicOrbit H₀ :=
    { x := fun τ => R.x (τ + c)
      T := R.T
      T_pos := R.T_pos
      trajectory := ⟨fun τ => HasDerivAt.comp_add_const τ c (R.trajectory.1 (τ + c)),
        fun τ => R.trajectory.2 (τ + c)⟩
      periodic := fun τ => by
        show R.x (τ + R.T + c) = R.x (τ + c)
        rw [add_right_comm]; exact R.periodic (τ + c) }
  have hrange : Set.range P.x = Set.range (fun τ => ofR4 (R'.x τ)) := by
    rw [← hRr]
    ext y
    constructor
    · rintro ⟨τ, rfl⟩
      refine ⟨τ - c, ?_⟩
      show ofR4 (R.x (τ - c + c)) = _
      rw [sub_add_cancel]
      rfl
    · rintro ⟨τ, rfl⟩; exact ⟨τ + c, rfl⟩
  set g : ℝ → V 1 := fun s => ofR4 (R.x s) with hg
  set f : ℝ → ℝ := fun τ => liouville (g τ) (deriv g τ) with hf
  have hgper : Function.Periodic g R.T := fun τ => by simp only [hg]; rw [R.periodic]
  have hfper : Function.Periodic f R.T := by
    intro τ
    have hd : deriv g (τ + R.T) = deriv g τ := by
      rw [← deriv_comp_add_const]
      congr 1
      funext s
      exact hgper s
    simp only [hf]
    rw [hd, hgper τ]
  have hT' : P.T = ∫ τ in (0 : ℝ)..R'.T,
      liouville (ofR4 (R'.x τ)) (deriv (fun s => ofR4 (R'.x s)) τ) := by
    have he : ∀ τ, liouville (ofR4 (R'.x τ)) (deriv (fun s => ofR4 (R'.x s)) τ) = f (τ + c) := by
      intro τ
      show liouville (g (τ + c)) (deriv (fun s => g (s + c)) τ) = _
      rw [deriv_comp_add_const]
    simp only [he]
    rw [intervalIntegral.integral_comp_add_right]
    have := hfper.intervalIntegral_add_eq c 0
    rw [zero_add, add_comm c R.T] at this
    rw [zero_add, show R'.T = R.T from rfl, this]
    exact hRT
  obtain ⟨Y, hY⟩ := ag_exists_isLinearizedFlow H₀ hH₀ R'
  have h3 := hcz R' hrange hT' Y hY
  obtain ⟨hs, hdet, h0⟩ := HryniewiczCriterion.linearizedXiPath_isSymplecticPath H₀ hH₀ R' Y hY
  obtain ⟨a, b, hab, hw, hwid⟩ := HryniewiczCriterion.windingInterval_narrow _ hs hdet h0
  have hgt := (HryniewiczCriterion.czIndexOfPath_ge_three_iff _ a b hab hw (by linarith)).1 h3
  have hφ := lt_of_mem_windingInterval_linearizedXiPath H₀ hH₀ J R' P hT'
    (by show P.x 0 = R.x (0 + c); rw [zero_add]; exact hc.symm)
    Z hZ hwind Sinf hSym hA Ψ hΨ Y hY 1 (by simpa using hgt)
  simpa using hφ

/-! ### The gain over one period -/

theorem ag_rot_of_vecToC (v : CauchyRiemannIndex.Vec 1) (ρ α : ℝ)
    (h : vecToC v = (ρ : ℂ) * Complex.exp ((α : ℂ) * Complex.I)) :
    ![v (Sum.inl 0), v (Sum.inr 0)] = ρ • HryniewiczCriterion.rotationVector α := by
  have h1 : v (Sum.inl 0) = ρ * Real.cos α := by
    have := congrArg Complex.re h
    simpa [vecToC, Complex.exp_ofReal_mul_I_re] using this
  have h2 : v (Sum.inr 0) = ρ * Real.sin α := by
    have := congrArg Complex.im h
    simpa [vecToC, Complex.exp_ofReal_mul_I_im] using this
  ext i
  fin_cases i <;> simp [HryniewiczCriterion.rotationVector, h1, h2]

theorem ag_mulVec (M : CauchyRiemannIndex.Mat 1) (w : CauchyRiemannIndex.Vec 1) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M).mulVec ![w (Sum.inl 0), w (Sum.inr 0)] =
      ![(Matrix.toEuclideanLin M w) (Sum.inl 0), (Matrix.toEuclideanLin M w) (Sum.inr 0)] := by
  ext i
  fin_cases i <;>
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.toLpLin_apply,
    Fintype.sum_sum_type, Matrix.reindex_apply, Matrix.submatrix_apply] <;> rfl

theorem ag_rot_periodic (x : ℝ) (m : ℤ) :
    HryniewiczCriterion.rotationVector (x - 2 * π * m) = HryniewiczCriterion.rotationVector x := by
  have hc : Real.cos (x - 2 * π * m) = Real.cos x := by
    rw [show x - 2 * π * m = x - (m : ℝ) * (2 * π) by ring, Real.cos_sub_int_mul_two_pi]
  have hs : Real.sin (x - 2 * π * m) = Real.sin x := by
    rw [show x - 2 * π * m = x - (m : ℝ) * (2 * π) by ring, Real.sin_sub_int_mul_two_pi]
  simp [HryniewiczCriterion.rotationVector, hc, hs]

/-- Over every integer period `[k, k+1]` a solution turns by `2π d` with `d` in the winding
interval of `Ψ`. -/
theorem ag_period_mem (S : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop S)
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution S Ψ)
    {ζ : ℝ → CauchyRiemannIndex.Vec 1}
    (hζ : ∀ t, HasDerivAt ζ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * S t) (ζ t)) t)
    (hζ0 : ∀ t, ζ t ≠ 0) {θ : ℝ → ℝ} (hθc : Continuous θ)
    (hθ : ∀ t, vecToC (ζ t) = (‖vecToC (ζ t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I))
    (k : ℤ) :
    (θ (k + 1) - θ k) / (2 * π) ∈ HryniewiczCriterion.windingInterval
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) := by
  have hpi := Real.pi_pos
  set m : ℤ := ⌊θ k / (2 * π)⌋ with hm
  set s₀ : ℝ := θ k - 2 * π * m with hs₀
  have hm1 : (m : ℝ) ≤ θ k / (2 * π) := Int.floor_le _
  have hm2 : θ k / (2 * π) < m + 1 := Int.lt_floor_add_one _
  have hs₀mem : s₀ ∈ Set.Icc (0 : ℝ) (2 * π) := by
    rw [le_div_iff₀ (by positivity)] at hm1
    rw [div_lt_iff₀ (by positivity)] at hm2
    constructor <;> nlinarith
  set θt : ℝ → ℝ := fun t => θ (t + k) - 2 * π * m with hθt
  refine ⟨s₀, hs₀mem, θt, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact ((hθc.comp (continuous_id.add continuous_const)).sub continuous_const).continuousOn
  · simp [hθt, hs₀]
  · intro t _
    have hk0 : ζ k ≠ 0 := hζ0 k
    set ρ : ℝ := ‖vecToC (ζ k)‖ with hρ
    have hρpos : 0 < ρ := norm_pos_iff.2 fun h =>
      hk0 (ag_vecToC_inj (h.trans ag_vecToC_zero.symm))
    have hw := ag_rot_of_vecToC (ζ k) ρ (θ k) (hθ k)
    have hz := ag_rot_of_vecToC (ζ (t + k)) _ (θ (t + k)) (hθ (t + k))
    have hrs : HryniewiczCriterion.rotationVector s₀ =
        ρ⁻¹ • ![ζ k (Sum.inl 0), ζ k (Sum.inr 0)] := by
      rw [hw, smul_smul, inv_mul_cancel₀ hρpos.ne', one_smul, hs₀, ag_rot_periodic]
    refine ⟨ρ⁻¹ * ‖vecToC (ζ (t + k))‖, mul_pos (inv_pos.2 hρpos) (norm_pos_iff.2 fun h =>
      hζ0 _ (ag_vecToC_inj (h.trans ag_vecToC_zero.symm))), ?_⟩
    rw [hrs, Matrix.mulVec_smul, ag_mulVec, ← ag_shift_eq S hSym.1 hSym.2.1 Ψ hΨ hζ k t, hz,
      smul_smul, hθt, ag_rot_periodic]
  · simp only [hθt, hs₀]
    rw [add_comm (1 : ℝ) (k : ℝ)]
    ring

end

end FiniteEnergyPlane

/-!
# `exists_angle_gain_of_isCZAtLeast_three` (25370c3f)

Glue: `μ_CZ ≥ 3` gives a lower bound `a > 1` on the winding interval of `Ψ`, so a solution turns
by at least `2π a` over every integer period; a Lipschitz angle handles the partial periods, and
any lift of a winding-one loop grows like `2π t` up to a bounded error.
-/

namespace FiniteEnergyPlane

open Matrix
open scoped Real ContDiff

noncomputable section

theorem ag_periodic_bound {g : ℝ → ℝ} (hg : Continuous g) (hper : Function.Periodic g 1) :
    ∃ M, ∀ t, |g t| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨M, fun t => ?_⟩
  have h := hper.sub_int_mul_eq (n := ⌊t⌋) (x := t)
  rw [mul_one] at h
  rw [← h]
  have hm : t - ⌊t⌋ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩
  simpa [Real.norm_eq_abs] using hM _ hm

/-- A lift of a winding-one loop grows like `2π t` up to a constant depending only on the loop. -/
theorem ag_lift_bound (E : ℝ → ℂ) (hE : HasLoopWind E 1) :
    ∃ M, ∀ β : ℝ → ℝ, Continuous β →
      (∀ t : ℝ, E t = (‖E t‖ : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) →
      ∀ t₀ t₁ : ℝ, β t₁ - β t₀ ≤ 2 * π * (t₁ - t₀) + M := by
  obtain ⟨-, hEper, hE0, β₀, hβ₀c, hβ₀, hβ₀1⟩ := hE
  have hβ₁l : ∀ t, E t = (‖E t‖ : ℂ) *
      Complex.exp ((((fun t => β₀ (t + 1) - 2 * π) t : ℝ) : ℂ) * Complex.I) := by
    intro t
    have h := hβ₀ (t + 1)
    rw [hEper t] at h
    conv_lhs => rw [h]
    congr 1
    have e : ((((fun t => β₀ (t + 1) - 2 * π) t : ℝ) : ℂ) * Complex.I) =
        (β₀ (t + 1) : ℂ) * Complex.I - 2 * π * Complex.I := by push_cast; ring
    rw [e, Complex.exp_sub, Complex.exp_two_pi_mul_I, div_one]
  have hstep : ∀ t, β₀ (t + 1) = β₀ t + 2 * π := by
    intro t
    have h := ag_lift_sub_const hE0 (hβ₀c.comp (continuous_id.add continuous_const) |>.sub
      continuous_const) hβ₀c hβ₁l hβ₀ t
    have h' : β₀ (t + 1) - 2 * π - β₀ t = β₀ (0 + 1) - 2 * π - β₀ 0 := h
    rw [zero_add] at h'
    push_cast at hβ₀1
    linarith
  have hgper : Function.Periodic (fun t => β₀ t - 2 * π * t) 1 := fun t => by
    simp only [hstep]; ring
  obtain ⟨M, hM⟩ := ag_periodic_bound (hβ₀c.sub (continuous_const.mul continuous_id)) hgper
  refine ⟨2 * M, fun β hβc hβ t₀ t₁ => ?_⟩
  have e0 := ag_lift_sub_const hE0 hβc hβ₀c hβ hβ₀ t₀
  have e1 := ag_lift_sub_const hE0 hβc hβ₀c hβ hβ₀ t₁
  have h0 := abs_le.1 (show |β₀ t₀ - 2 * π * t₀| ≤ M from hM t₀)
  have h1 := abs_le.1 (show |β₀ t₁ - 2 * π * t₁| ≤ M from hM t₁)
  linarith [h0.1, h1.2]

/-- Arithmetic: integer-period gains plus a Lipschitz bound give a uniform linear gain. -/
theorem ag_chain_arith {θ : ℝ → ℝ} {A C₀ : ℝ} (hA : 0 < A) (hC₀ : 0 ≤ C₀)
    (hlip : ∀ s t, s ≤ t → |θ t - θ s| ≤ C₀ * (t - s))
    (hint : ∀ m n : ℤ, m ≤ n → A * ((n : ℝ) - m) ≤ θ n - θ m)
    (t₀ t₁ : ℝ) (h : t₀ ≤ t₁) : A * (t₁ - t₀) - (2 * A + 2 * C₀) ≤ θ t₁ - θ t₀ := by
  set n₀ : ℤ := ⌈t₀⌉
  set n₁ : ℤ := ⌊t₁⌋
  have a1 : t₀ ≤ n₀ := Int.le_ceil t₀
  have a2 : (n₀ : ℝ) < t₀ + 1 := Int.ceil_lt_add_one t₀
  have b1 : (n₁ : ℝ) ≤ t₁ := Int.floor_le t₁
  have b2 : t₁ < n₁ + 1 := Int.lt_floor_add_one t₁
  rcases le_or_gt n₀ n₁ with hn | hn
  · have hmid := hint n₀ n₁ hn
    have hn' : (n₀ : ℝ) ≤ n₁ := by exact_mod_cast hn
    have l1 := abs_le.1 (hlip n₁ t₁ b1)
    have l0 := abs_le.1 (hlip t₀ n₀ a1)
    have c1 : C₀ * (t₁ - n₁) ≤ C₀ := by nlinarith
    have c0 : C₀ * (n₀ - t₀) ≤ C₀ := by nlinarith
    have hm : A * (t₁ - t₀) - 2 * A ≤ A * ((n₁ : ℝ) - n₀) := by nlinarith
    linarith [l1.1, l0.1]
  · have hn' : (n₁ : ℝ) + 1 ≤ n₀ := by exact_mod_cast hn
    have hlt : t₁ - t₀ < 1 := by linarith
    have l := abs_le.1 (hlip t₀ t₁ h)
    have c : C₀ * (t₁ - t₀) ≤ C₀ := by nlinarith
    have hm : A * (t₁ - t₀) ≤ A := by nlinarith
    linarith [l.1]

theorem ag_main (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (E : ℝ → ℂ) (hE : HasLoopWind E 1) :
    ∃ r > 0, ∃ C : ℝ, ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t : ℝ, HasDerivAt ζ
        (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) →
      (∃ t : ℝ, ζ t ≠ 0) →
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t : ℝ, vecToC (ζ t) =
          (‖vecToC (ζ t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) ∧
        ∀ β : ℝ → ℝ, Continuous β →
          (∀ t : ℝ, E t = (‖E t‖ : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) →
          ∀ t₀ t₁ : ℝ, t₀ ≤ t₁ → r * (t₁ - t₀) - C ≤ (θ t₁ - β t₁) - (θ t₀ - β t₀) := by
  have hpi := Real.pi_pos
  have hS := ag_Sinf_contDiff H hH J hJ P Z hZ Sinf hA
  obtain ⟨Ψ, hΨ, -⟩ := CauchyRiemannIndex.fundamentalSolution_existsUnique 1 Sinf hSym.1
  have hgt := ag_wind_gt_one H hH J P hcz Z hZ hwind Sinf hSym hA Ψ hΨ
  obtain ⟨a, b, hab, hw⟩ := ag_narrow Sinf hSym hS Ψ hΨ
  have ha1 : 1 < a := hgt a (by rw [hw]; exact ⟨le_rfl, hab⟩)
  have hge : ∀ d ∈ HryniewiczCriterion.windingInterval
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)), a ≤ d := fun d hd => by
    rw [hw] at hd; exact hd.1
  obtain ⟨C₀, hC₀, hang⟩ := ag_exists_angle Sinf hSym.1 hSym.2.1
  obtain ⟨M, hM⟩ := ag_lift_bound E hE
  set A : ℝ := 2 * π * a with hAdef
  have hApos : 0 < A := by positivity
  refine ⟨A - 2 * π, by nlinarith, 2 * A + 2 * C₀ + M, fun ζ hζ ⟨t₂, ht₂⟩ => ?_⟩
  -- `ζ` vanishes nowhere
  have hζ0 : ∀ t, ζ t ≠ 0 := by
    have hrep : ∀ t, ζ t = Matrix.toEuclideanLin (Ψ t) (ζ 0) := fun t => by
      have := ag_shift_eq Sinf hSym.1 hSym.2.1 Ψ hΨ hζ 0 t
      simpa using this
    have h00 : ζ 0 ≠ 0 := by
      intro h
      apply ht₂
      rw [hrep t₂, h, map_zero]
    intro t
    rw [hrep t]
    exact ag_fund_apply_ne_zero Sinf hSym.2.2 Ψ hΨ t _ h00
  obtain ⟨θ, hθc, hθ, hlip⟩ := hang ζ hζ hζ0
  have hstep : ∀ k : ℤ, A ≤ θ (k + 1) - θ k := by
    intro k
    have h := hge _ (ag_period_mem Sinf hSym Ψ hΨ hζ hζ0 hθc hθ k)
    rw [le_div_iff₀ (by positivity)] at h
    simp only [hAdef]
    linarith
  have hnat : ∀ (n : ℕ) (k : ℤ), A * n ≤ θ (k + n) - θ k := by
    intro n
    induction n with
    | zero => intro k; simp
    | succ n ih =>
      intro k
      have h1 := ih k
      have h2 := hstep (k + n)
      push_cast at h2 ⊢
      rw [← add_assoc]
      linarith
  have hint : ∀ m n : ℤ, m ≤ n → A * ((n : ℝ) - m) ≤ θ n - θ m := by
    intro m n hmn
    obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = m + d := ⟨(n - m).toNat, by omega⟩
    have := hnat d m
    push_cast at this ⊢
    simpa using this
  refine ⟨θ, hθc, hθ, fun β hβc hβ t₀ t₁ h => ?_⟩
  have hθg := ag_chain_arith hApos hC₀ hlip hint t₀ t₁ h
  have hβg := hM β hβc hβ t₀ t₁
  linarith

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J P Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (E : ℝ → ℂ) (hE : HasLoopWind E 1) :
    ∃ r > 0, ∃ C : ℝ, ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1,
      (∀ t : ℝ, HasDerivAt ζ
        (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1 * Sinf t) (ζ t)) t) →
      (∃ t : ℝ, ζ t ≠ 0) →
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t : ℝ, vecToC (ζ t) =
          (‖vecToC (ζ t)‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)) ∧
        ∀ β : ℝ → ℝ, Continuous β →
          (∀ t : ℝ, E t = (‖E t‖ : ℂ) * Complex.exp ((β t : ℂ) * Complex.I)) →
          ∀ t₀ t₁ : ℝ, t₀ ≤ t₁ → r * (t₁ - t₀) - C ≤ (θ t₁ - β t₁) - (θ t₀ - β t₀) :=
  FiniteEnergyPlane.ag_main H hH J hJ P hcz Z hZ hwind Sinf hSym hA E hE
