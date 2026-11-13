-- Prove2me | solution 1 for FiniteEnergyPlane.qMap_smooth_of_isStdTubeStructure
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T22:02:48.703893+00:00
-- url     : https://prove2.me/submissions/6d64e5a6-274f-4aae-8310-0d14aa6c8d5c

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Theorems.Thm_FiniteEnergyPlane_exists_smooth_qPoint_rep



/-!
# Slope weights (local helper definition, not published as a definition)

`IsSlopeWeight χ a b`: `χ` is smooth, with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`.
-/

namespace FiniteEnergyPlane

open scoped ContDiff

/-! ### Slope weights are affine near the ends -/

theorem IsSlopeWeight.eq_right {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : 1 ≤ s) : χ s = χ 1 + b * (s - 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have hb : deriv χ c = b := h.2.2 c hc.1.le
  rw [hb, eq_div_iff (by linarith)] at hc'
  linarith

theorem IsSlopeWeight.eq_left {χ : ℝ → ℝ} {a b : ℝ} (h : IsSlopeWeight χ a b) {s : ℝ}
    (hs : s ≤ -1) : χ s = χ (-1) + a * (s + 1) := by
  rcases hs.eq_or_lt with rfl | hs
  · ring
  have hd : Differentiable ℝ χ := h.1.differentiable (by simp)
  obtain ⟨c, hc, hc'⟩ := exists_deriv_eq_slope χ hs hd.continuous.continuousOn
    hd.differentiableOn
  have ha : deriv χ c = a := h.2.1 c hc.2.le
  rw [ha, eq_div_iff (by linarith)] at hc'
  linarith


end FiniteEnergyPlane

/-!
# Q-S, part 1: matrices of real-linear maps `ℂ → ℂ`, the normal coefficient as such a matrix,
smoothness, periodicity, and the plane form (from `Jbar² = -1`).
-/

namespace FiniteEnergyPlane.QS

open Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- Real and imaginary part, indexed by `Fin 1 ⊕ Fin 1`. -/
def reIm : Fin 1 ⊕ Fin 1 → ℂ → ℝ := Sum.elim (fun _ (y : ℂ) => y.re) (fun _ (y : ℂ) => y.im)

/-- The real basis `1, i` of `ℂ`, indexed by `Fin 1 ⊕ Fin 1`. -/
def basisC : Fin 1 ⊕ Fin 1 → ℂ := Sum.elim (fun _ => (1 : ℂ)) (fun _ => Complex.I)

/-- `reIm i` as a continuous real-linear map. -/
def reImCLM : Fin 1 ⊕ Fin 1 → ℂ →L[ℝ] ℝ := Sum.elim (fun _ => Complex.reCLM) (fun _ => Complex.imCLM)

theorem reImCLM_apply (i : Fin 1 ⊕ Fin 1) (y : ℂ) : reImCLM i y = reIm i y := by
  rcases i with i | i <;> rfl

/-- The real `2 × 2` matrix of a real-linear map `ℂ → ℂ`. -/
def cMat (T : ℂ →L[ℝ] ℂ) : Mat 1 := Matrix.of fun i j => reIm i (T (basisC j))

theorem vecToC_eq (a : Vec 1) :
    vecToC a = (a (Sum.inl 0)) • (1 : ℂ) + (a (Sum.inr 0)) • Complex.I := by
  apply Complex.ext <;> simp [vecToC]

theorem vecToC_cMat (T : ℂ →L[ℝ] ℂ) (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (cMat T) a) = T (vecToC a) := by
  rw [vecToC_eq a, map_add, map_smul, map_smul]
  apply Complex.ext <;>
  simp [vecToC, cMat, reIm, basisC, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type] <;> ring

theorem vecToC_injective : Function.Injective vecToC := by
  intro a b h
  ext i
  rcases i with i | i <;> obtain rfl : i = 0 := Subsingleton.elim _ _
  · exact congrArg Complex.re h
  · exact congrArg Complex.im h

theorem eq_cMat {M : Mat 1} {T : ℂ →L[ℝ] ℂ}
    (h : ∀ a, vecToC (Matrix.toEuclideanLin M a) = T (vecToC a)) : M = cMat T := by
  apply Matrix.toEuclideanLin.injective
  apply LinearMap.ext
  intro a
  apply vecToC_injective
  rw [h, vecToC_cMat]

theorem cMat_sub (T T' : ℂ →L[ℝ] ℂ) : cMat (T - T') = cMat T - cMat T' := by
  ext i j
  rcases i with i | i <;> simp [cMat, reIm]

theorem cMat_apply (T : ℂ →L[ℝ] ℂ) (i j : Fin 1 ⊕ Fin 1) :
    cMat T i j = reIm i (T (basisC j)) := rfl

/-- The `w`-derivative of `Jbar` along `w = 0`. -/
def dW (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (z : ℂ) : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  fderiv ℝ (fun w : ℂ => Jbar (z, w)) 0

/-- Evaluate at `v`, then take the second component. -/
def evSnd (v : ℂ × ℂ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.snd ℝ ℂ ℂ).comp (ContinuousLinearMap.apply ℝ (ℂ × ℂ) v)

theorem evSnd_apply (v : ℂ × ℂ) (L : ℂ × ℂ →L[ℝ] ℂ × ℂ) : evSnd v L = (L v).2 := rfl

/-- `a ↦ [(∂_w Jbar(z, 0) a)(2πi z, 0)]₂`. -/
def tN (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (evSnd ((((2 * π : ℝ) : ℂ) * Complex.I * z), 0)).comp (dW Jbar z)

theorem normalCoeff_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (x : ℝ × ℝ) :
    normalCoeff Jbar x = cMat (tN Jbar (cylInf x.1 x.2)) := rfl

/-- `a ↦ [(∂_w Jinf(t, 0) a)(i, 0)]₂`. -/
def tInf (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (t : ℝ) : ℂ →L[ℝ] ℂ :=
  (evSnd (Complex.I, 0)).comp (fderiv ℝ (fun w : ℂ => Jinf (t, w)) 0)

theorem sinf_eq (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (t : ℝ) : Sinf t = cMat (tInf Jinf t) :=
  eq_cMat fun a => hstd.2.2.2.2.2.2.2 t a

/-! ### smoothness of partial `w`-derivatives -/

theorem contDiff_fderiv_w {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : X × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hK : ContDiffOn ℝ ∞ K (Set.univ ×ˢ ball (0 : ℂ) ρ)) :
    ContDiff ℝ ∞ (fun x : X => fderiv ℝ (fun w : ℂ => K (x, w)) 0) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) := isOpen_univ.prod isOpen_ball
  have hx : ((x, 0) : X × ℂ) ∈ (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) :=
    ⟨Set.mem_univ _, mem_ball_self hρ⟩
  have h1 : ContDiffAt ℝ ∞ (Function.uncurry fun (x : X) (w : ℂ) => K (x, w)) (x, (fun _ => (0 : ℂ)) x) :=
    hK.contDiffAt (hU.mem_nhds hx)
  exact ContDiffAt.fderiv h1 contDiffAt_const (by simp)

theorem hasFDerivAt_w {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : X × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (ρ : ℝ)
    (hK : ContDiffOn ℝ ∞ K (Set.univ ×ˢ ball (0 : ℂ) ρ)) (x : X) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    HasFDerivAt (fun w : ℂ => K (x, w)) (fderiv ℝ (fun w : ℂ => K (x, w)) w) w := by
  have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ : Set (X × ℂ)) := isOpen_univ.prod isOpen_ball
  have hd : DifferentiableAt ℝ K (x, w) :=
    (hK.contDiffAt (hU.mem_nhds ⟨Set.mem_univ _, hw⟩)).differentiableAt (by simp)
  have hc : HasFDerivAt (fun w : ℂ => ((x, w) : X × ℂ))
      ((0 : ℂ →L[ℝ] X).prod (ContinuousLinearMap.id ℝ ℂ)) w :=
    (hasFDerivAt_const x w).prodMk (hasFDerivAt_id w)
  exact (hd.hasFDerivAt.comp w hc).differentiableAt.hasFDerivAt

theorem contDiff_cyl : ContDiff ℝ ∞ (fun q : ℝ × ℝ => cylInf q.1 q.2) := by
  unfold cylInf ccwLoop
  have h1 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((Real.exp (2 * π * q.1) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_fst))
  have h2 : ContDiff ℝ ∞ (fun q : ℝ × ℝ => ((2 * π * q.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_snd)
  exact h1.mul (Complex.contDiff_exp.comp (h2.mul contDiff_const))

theorem cyl_per (s t : ℝ) : cylInf s (t + 1) = cylInf s t := by
  unfold cylInf ccwLoop
  congr 1
  have : (((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I) =
      ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

theorem cyl_ne (s t : ℝ) : cylInf s t ≠ 0 := by
  unfold cylInf ccwLoop
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  exact_mod_cast (Real.exp_pos _).ne'

/-! ### antilinearity of `∂_w Jbar(z, 0)` in the tangential slot -/

theorem dW_antilinear (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (z a Δ : ℂ) :
    (dW Jbar z a (Complex.I * Δ, 0)).2 = -(Complex.I * (dW Jbar z a (Δ, 0)).2) := by
  have hd : HasFDerivAt (fun w : ℂ => Jbar (z, w)) (dW Jbar z) 0 :=
    hasFDerivAt_w Jbar ρ hJ z (mem_ball_self hρ)
  have hsqd := hd.clm_comp hd
  have hconst : HasFDerivAt (fun w : ℂ => (Jbar (z, w)).comp (Jbar (z, w)))
      (0 : ℂ →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ)) 0 := by
    have hev : (fun w : ℂ => (Jbar (z, w)).comp (Jbar (z, w))) =ᶠ[𝓝 0]
        fun _ => -ContinuousLinearMap.id ℝ (ℂ × ℂ) := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hρ)] with w hw
      exact hsq (z, w) ⟨Set.mem_univ _, hw⟩
    exact (hasFDerivAt_const _ _).congr_of_eventuallyEq hev
  have huniq := hsqd.unique hconst
  have ha := congrArg (fun L => L a (Δ, 0)) huniq
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, h0,
    ContinuousLinearMap.zero_apply] at ha
  have hj : ∀ p : ℂ × ℂ, jStd p = (Complex.I * p.1, Complex.I * p.2) := by
    intro p
    show ((Complex.I • ContinuousLinearMap.id ℝ ℂ) p.1, (Complex.I • ContinuousLinearMap.id ℝ ℂ) p.2) = _
    simp
  have ha2 := congrArg Prod.snd ha
  simp only [hj, Prod.snd_add, Prod.snd_zero, mul_zero] at ha2
  change (dW Jbar z a (Complex.I * Δ, 0)).2 = _
  linear_combination ha2

/-! ### plane form -/

theorem isPlaneCoeff_normalCoeff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) : IsPlaneCoeff (normalCoeff Jbar) := by
  let c : ℂ := -(Complex.I / 2)
  let A : ℂ → ℂ →L[ℝ] ℂ := fun z =>
    ((c • ContinuousLinearMap.id ℝ ℂ).comp (evSnd ((1 : ℂ), (0 : ℂ)))).comp (dW Jbar z)
  refine ⟨A, ?_, ?_⟩
  · exact contDiff_const.clm_comp (contDiff_fderiv_w Jbar ρ hρ hJ)
  · intro s t a
    rw [normalCoeff_eq, vecToC_cMat]
    set z := cylInf s t
    set α := vecToC a
    set X := (dW Jbar z α ((1 : ℂ), (0 : ℂ))).2 with hX
    have hanti := dW_antilinear ρ hρ Jbar hJ hsq h0 z α 1
    rw [mul_one] at hanti
    set μ : ℂ := ((2 * π : ℝ) : ℂ) * Complex.I * z
    have hsplit : ((μ, 0) : ℂ × ℂ) = μ.re • ((1 : ℂ), (0 : ℂ)) + μ.im • (Complex.I, (0 : ℂ)) := by
      refine Prod.ext ?_ ?_
      · apply Complex.ext <;> simp
      · simp
    have hlhs : tN Jbar z α = μ.re * X + μ.im * (-(Complex.I * X)) := by
      show (dW Jbar z α (μ, 0)).2 = _
      rw [hsplit, map_add, map_smul, map_smul, Prod.snd_add, Prod.smul_snd, Prod.smul_snd, hanti,
        Complex.real_smul, Complex.real_smul]
    have hrhs : A z α = c * X := rfl
    rw [hlhs, hrhs]
    simp only [μ, c]
    apply Complex.ext <;> simp <;> ring

/-! ### smoothness and periodicity of the entries -/

theorem contDiff_normalCoeff (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (i j : Fin 1 ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => normalCoeff Jbar x i j) := by
  have hd := (contDiff_fderiv_w Jbar ρ hρ hJ).comp contDiff_cyl
  have hv : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf x.1 x.2), (0 : ℂ))) :=
    (contDiff_const.mul contDiff_cyl).prodMk contDiff_const
  have : (fun x : ℝ × ℝ => normalCoeff Jbar x i j) =
      fun x => reImCLM i ((dW Jbar (cylInf x.1 x.2) (basisC j)
        ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf x.1 x.2), (0 : ℂ))).2) := by
    funext x; rw [normalCoeff_eq, cMat_apply, reImCLM_apply]; rfl
  rw [this]
  exact (reImCLM i).contDiff.comp (contDiff_snd.comp ((hd.clm_apply contDiff_const).clm_apply hv))

theorem contDiff_sinf (ρ b : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → Mat 1)
    (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) (i j : Fin 1 ⊕ Fin 1) :
    ContDiff ℝ ∞ (fun t => Sinf t i j) := by
  have : (fun t => Sinf t i j) = fun t => reImCLM i ((tInf Jinf t) (basisC j)) := by
    funext t; rw [sinf_eq ρ b Jbar Jinf Sinf hstd t, cMat_apply, reImCLM_apply]
  rw [this]
  have hT : ContDiff ℝ ∞ (fun t => tInf Jinf t) :=
    contDiff_const.clm_comp (contDiff_fderiv_w Jinf ρ hρ hstd.2.2.2.1)
  exact (reImCLM i).contDiff.comp (hT.clm_apply contDiff_const)

theorem normalCoeff_per (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) :
    normalCoeff Jbar (s, t + 1) = normalCoeff Jbar (s, t) := by
  rw [normalCoeff_eq, normalCoeff_eq]
  simp only [cyl_per]

end

end FiniteEnergyPlane.QS

/-!
# Q-N, layer 6 (local, NOT published): `qMap 0 = 0` and the derivative of `qMap` at `0`

Decoupled from the smoothness proof: assuming only that `qMap` is differentiable at `0` and that
its components are the `L⁴` classes of the pointwise formula near `0`, the derivative in the
directions `(ζ, 0, 0)` and `(0, 0, ζ)` is identified a.e. through difference quotients along
`r_n = 1/(n+1)` (an `L⁴`-convergent sequence has an a.e.-convergent subsequence).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

namespace QN

/-! ### `ℂ ↔ ℝ²` and `toLpOrZero` -/

lemma vecToC_J₀ (a : Vec 1) :
    vecToC (Matrix.toEuclideanLin (J₀ 1) a) = Complex.I * vecToC a := by
  apply Complex.ext <;>
    simp [vecToC, J₀, Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct,
      Matrix.fromBlocks, Fintype.sum_sum_type]

lemma cToVec_vecToC (a : Vec 1) : cToVec (vecToC a) = a := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [cToVec, vecToC]

lemma vecToC_cToVec (z : ℂ) : vecToC (cToVec z) = z := by
  apply Complex.ext <;> simp [cToVec, vecToC]

lemma cToVec_add (a b : ℂ) : cToVec (a + b) = cToVec a + cToVec b := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_smul (r : ℝ) (a : ℂ) : cToVec ((r : ℂ) * a) = r • cToVec a := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma cToVec_zero : cToVec 0 = 0 := by
  ext i; rcases i with i | i <;> simp [cToVec]

lemma continuous_cToVec : Continuous cToVec := by
  unfold cToVec
  exact (EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm.continuous.comp
    (continuous_pi fun i => by rcases i with i | i <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop)

lemma toLpOrZero_eq_toLp {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    toLpOrZero f = hf.toLp f := by
  simp [toLpOrZero, hf]

lemma coeFn_toLpOrZero {f : ℝ × ℝ → Vec 1} (hf : MemLp f 4 cylMeasure) :
    (toLpOrZero f : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] f := by
  rw [toLpOrZero_eq_toLp hf]; exact hf.coeFn_toLp

lemma toLpOrZero_of_ae_zero {f : ℝ × ℝ → Vec 1} (hf : f =ᵐ[cylMeasure] 0) : toLpOrZero f = 0 := by
  have hm : MemLp f 4 cylMeasure := (MemLp.zero (ε := Vec 1)).ae_eq hf.symm
  rw [toLpOrZero_eq_toLp hm]
  exact (MemLp.toLp_eq_toLp_iff hm MemLp.zero).2 hf |>.trans (MemLp.toLp_zero _)

/-! ### The pointwise formula in terms of values -/

/-- `qPoint` with the nine values `T.i q`, `N.i q` (as complex numbers) and `c` made explicit. -/
def qPt (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (c : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ) : ℂ × ℂ :=
  let s := q.1
  let z := cylInf q.1 q.2
  let eT : ℂ := (Real.exp (χT s) : ℂ)
  let eN : ℂ := (Real.exp (χN s) : ℂ)
  let ψ := z + eT * a1
  let ψs := ((2 * π : ℝ) : ℂ) * z + eT * (((deriv χT s : ℝ) : ℂ) * a1 + a2)
  let ψt := ((2 * π : ℝ) : ℂ) * Complex.I * z + eT * a3
  let v := (β s : ℂ) * c + eN * b1
  let vs := ((deriv β s : ℝ) : ℂ) * c + eN * (((deriv χN s : ℝ) : ℂ) * b1 + b2)
  let vt := eN * b3
  let E := (ψs, vs) + Jbar (ψ, v) (ψt, vt)
  ((Real.exp (-χT s) : ℂ) * E.1, (Real.exp (-χN s) : ℂ) * E.2)

lemma qPoint_eq (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (x : QDom) (q : ℝ × ℝ) :
    qPoint Jbar χT χN β x q = qPt Jbar χT χN β q x.2.1
      (vecToC ((x.1 : Triple 1 4).1 q)) (vecToC ((x.1 : Triple 1 4).2.1 q))
      (vecToC ((x.1 : Triple 1 4).2.2 q)) (vecToC ((x.2.2 : Triple 1 4).1 q))
      (vecToC ((x.2.2 : Triple 1 4).2.1 q)) (vecToC ((x.2.2 : Triple 1 4).2.2 q)) := rfl

lemma exp_mul_exp_neg (a : ℝ) : (Real.exp (-a) : ℂ) * (Real.exp a : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

lemma jStd_apply (a b : ℂ) : jStd (a, b) = (Complex.I * a, Complex.I * b) := by
  simp [jStd]

/-- Tangential values: `N = 0`, `c = 0`. -/
lemma qPt_tangential (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (q : ℝ × ℝ) (a1 a2 a3 : ℂ) :
    qPt Jbar χT χN β q 0 a1 a2 a3 0 0 0 =
      (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3, 0) := by
  simp only [qPt, mul_zero, add_zero, h0, jStd_apply, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_
  · have := exp_mul_exp_neg (χT q.1)
    linear_combination (((deriv χT q.1 : ℝ) : ℂ) * a1 + a2 + Complex.I * a3) * this +
      (Real.exp (-χT q.1) : ℂ) * ((2 * π : ℝ) : ℂ) * cylInf q.1 q.2 * Complex.I_sq
  · simp

/-! ### The a.e. limit of difference quotients -/

lemma tendsto_rn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => Set.mem_Ioi.2 (by positivity)⟩

/-- If `f : ℝ → L⁴` has derivative `D` at `0`, `f 0 = 0`, and the representatives of
`f (1/(n+1))`, scaled by `n+1`, converge a.e. to `G`, then `D = G` a.e. -/
lemma ae_eq_of_hasDerivAt {f : ℝ → LpCyl 1 4} {D : LpCyl 1 4} (hf : HasDerivAt f D 0)
    (hf0 : f 0 = 0) (g : ℕ → ℝ × ℝ → Vec 1)
    (hg : ∀ n : ℕ, (f (1 / ((n : ℝ) + 1)) : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] g n)
    (G : ℝ × ℝ → Vec 1)
    (hG : ∀ᵐ q ∂cylMeasure, Tendsto (fun n : ℕ => ((n : ℝ) + 1) • g n q) atTop (𝓝 (G q))) :
    (D : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] G := by
  have h1 := hf.tendsto_slope_zero_right.comp tendsto_rn
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) • f (1 / ((n : ℝ) + 1))) atTop (𝓝 D) := by
    refine h1.congr fun n => ?_
    simp only [Function.comp, zero_add, hf0, sub_zero, one_div, inv_inv]
  obtain ⟨ns, hmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp h2).exists_seq_tendsto_ae
  have hsm : ∀ n : ℕ, ((((n : ℝ) + 1) • f (1 / ((n : ℝ) + 1)) : LpCyl 1 4) : ℝ × ℝ → Vec 1)
      =ᵐ[cylMeasure] fun q => ((n : ℝ) + 1) • g n q := fun n => by
    filter_upwards [Lp.coeFn_smul ((n : ℝ) + 1) (f (1 / ((n : ℝ) + 1))), hg n] with q h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hall := ae_all_iff.2 hsm
  have hG' : ∀ᵐ q ∂cylMeasure, Tendsto (fun i => ((ns i : ℝ) + 1) • g (ns i) q) atTop
      (𝓝 (G q)) := by
    filter_upwards [hG] with q hq
    exact hq.comp hmono.tendsto_atTop
  have hD : ∀ᵐ q ∂cylMeasure, Tendsto (fun i => ((ns i : ℝ) + 1) • g (ns i) q) atTop
      (𝓝 (D q)) := by
    filter_upwards [hns, hall] with q h1 h2
    exact h1.congr fun i => h2 (ns i)
  exact MeasureTheory.AEEqFun.tendsto_ae_unique hD hG'

/-! ### Values of scaled unknowns -/

lemma vecToC_smul (r : ℝ) (a : Vec 1) : vecToC (r • a) = (r : ℂ) * vecToC a := by
  apply Complex.ext <;> simp [vecToC]

lemma vecToC_add (a b : Vec 1) : vecToC (a + b) = vecToC a + vecToC b := by
  apply Complex.ext <;> simp [vecToC]

/-- The nine values of `r • (A, c, B)`, a.e. -/
lemma qPoint_smul_ae (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ)
    (A B : ↥(W1p 4 1)) (c : ℂ) (r : ℝ) :
    (fun q => qPoint Jbar χT χN β (r • ((A, c, B) : QDom)) q) =ᵐ[cylMeasure] fun q =>
      qPt Jbar χT χN β q (r • c)
        ((r : ℂ) * vecToC ((A : Triple 1 4).1 q)) ((r : ℂ) * vecToC ((A : Triple 1 4).2.1 q))
        ((r : ℂ) * vecToC ((A : Triple 1 4).2.2 q)) ((r : ℂ) * vecToC ((B : Triple 1 4).1 q))
        ((r : ℂ) * vecToC ((B : Triple 1 4).2.1 q)) ((r : ℂ) * vecToC ((B : Triple 1 4).2.2 q)) := by
  have e1 : ((r • A : ↥(W1p 4 1)) : Triple 1 4) = r • (A : Triple 1 4) := Submodule.coe_smul r A
  have e2 : ((r • B : ↥(W1p 4 1)) : Triple 1 4) = r • (B : Triple 1 4) := Submodule.coe_smul r B
  filter_upwards [Lp.coeFn_smul r (A : Triple 1 4).1, Lp.coeFn_smul r (A : Triple 1 4).2.1,
    Lp.coeFn_smul r (A : Triple 1 4).2.2, Lp.coeFn_smul r (B : Triple 1 4).1,
    Lp.coeFn_smul r (B : Triple 1 4).2.1, Lp.coeFn_smul r (B : Triple 1 4).2.2]
    with q h1 h2 h3 h4 h5 h6
  rw [qPoint_eq]
  show qPt Jbar χT χN β q (r • c) (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).1 q))
    (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).2.1 q))
    (vecToC (((r • A : ↥(W1p 4 1)) : Triple 1 4).2.2 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).1 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).2.1 q))
    (vecToC (((r • B : ↥(W1p 4 1)) : Triple 1 4).2.2 q)) = _
  rw [e1, e2]
  simp only [Prod.smul_fst, Prod.smul_snd]
  rw [h1, h2, h3, h4, h5, h6]
  simp only [Pi.smul_apply, vecToC_smul]

lemma coeFn_zero_triple (i : Fin 3) :
    (((0 : ↥(W1p 4 1)) : Triple 1 4).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 ∧
    (((0 : ↥(W1p 4 1)) : Triple 1 4).2.1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 ∧
    (((0 : ↥(W1p 4 1)) : Triple 1 4).2.2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure] 0 :=
  ⟨Lp.coeFn_zero _ _ _, Lp.coeFn_zero _ _ _, Lp.coeFn_zero _ _ _⟩

lemma toEL_smul_one' (c : ℝ) (v : Vec 1) :
    Matrix.toEuclideanLin (c • (1 : Mat 1)) v = c • v := by
  simp

lemma toEL_add_smul_one' (A : Mat 1) (c : ℝ) (y : Vec 1) :
    Matrix.toEuclideanLin (A + c • (1 : Mat 1)) y = Matrix.toEuclideanLin A y + c • y := by
  rw [map_add, LinearMap.add_apply, toEL_smul_one']

lemma vecToC_crApply_slope (χ : ℝ → ℝ) (w : Triple 1 4) (q : ℝ × ℝ) :
    vecToC (crApply (fun x => deriv χ x.1 • (1 : Mat 1)) w q) =
      ((deriv χ q.1 : ℝ) : ℂ) * vecToC (w.1 q) + vecToC (w.2.1 q) +
        Complex.I * vecToC (w.2.2 q) := by
  simp only [crApply, vecToC_add, vecToC_J₀, toEL_smul_one', vecToC_smul]
  ring

lemma vecToC_crApply_normal (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χ : ℝ → ℝ) (w : Triple 1 4)
    (q : ℝ × ℝ) :
    vecToC (crApply (fun x => normalCoeff Jbar x + deriv χ x.1 • (1 : Mat 1)) w q) =
      ((deriv χ q.1 : ℝ) : ℂ) * vecToC (w.1 q) + vecToC (w.2.1 q) +
        Complex.I * vecToC (w.2.2 q) + QS.tN Jbar (cylInf q.1 q.2) (vecToC (w.1 q)) := by
  simp only [crApply, toEL_add_smul_one', vecToC_add, vecToC_J₀, vecToC_smul,
    QS.normalCoeff_eq, QS.vecToC_cMat]
  ring

end QN

namespace QN18

/-! ### `ℂ → ℝ²` as a continuous linear map -/

/-- `vecToC` as a continuous linear map. -/
def vL : Vec 1 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := vecToC
      map_add' := fun a b => by apply Complex.ext <;> simp [vecToC]
      map_smul' := fun c a => by apply Complex.ext <;> simp [vecToC] }

@[simp] lemma vL_apply (a : Vec 1) : vL a = vecToC a := rfl

/-- `cToVec` as a continuous linear map. -/
def cL : ℂ →L[ℝ] Vec 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := cToVec
      map_add' := QN.cToVec_add
      map_smul' := fun r a => by
        have := QN.cToVec_smul r a
        simpa [Complex.real_smul] using this }

@[simp] lemma cL_apply (a : ℂ) : cL a = cToVec a := rfl

end QN18

end

end FiniteEnergyPlane

/-!
# Q-N, layer 7 (local, NOT published): the derivative of `qMap` at `0`

* `qMap_tangential_ray`: on the ray `r • (ζ, 0, 0)` the formula is exactly linear in `r`.
* `qMap_zero`: `qMap 0 = 0`.
* `fderiv_qMap_tangential`, `fderiv_qMap_normal`: the two derivative formulas of Q-N, from
  differentiability at `0` and `L⁴`-membership of the pointwise formula near `0`.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

namespace QN

lemma vecToC_zero : vecToC 0 = 0 := by apply Complex.ext <;> simp [vecToC]

/-- The value identity on the tangential ray. -/
lemma qPoint_tangential_ae (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (ζ : ↥(W1p 4 1)) (r : ℝ) :
    (fun q => qPoint Jbar χT χN β (r • ((ζ, 0, 0) : QDom)) q) =ᵐ[cylMeasure] fun q =>
      ((r : ℂ) * vecToC (crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4) q), 0) := by
  obtain ⟨z1, z2, z3⟩ := coeFn_zero_triple 0
  filter_upwards [qPoint_smul_ae Jbar χT χN β ζ 0 0 r, z1, z2, z3] with q h h1 h2 h3
  rw [h, h1, h2, h3]
  simp only [Pi.zero_apply, vecToC_zero, mul_zero, smul_zero]
  rw [qPt_tangential Jbar h0, vecToC_crApply_slope]
  ext <;> simp <;> ring

lemma ae_cToVec_fst (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (ζ : ↥(W1p 4 1)) (r : ℝ) :
    (fun q => cToVec (qPoint Jbar χT χN β (r • ((ζ, 0, 0) : QDom)) q).1) =ᵐ[cylMeasure]
      fun q => r • crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4) q := by
  filter_upwards [qPoint_tangential_ae Jbar h0 χT χN β ζ r] with q h
  rw [h, cToVec_smul, cToVec_vecToC]

lemma qMap_tangential_snd (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (ζ : ↥(W1p 4 1)) (r : ℝ) :
    (qMap Jbar χT χN β (r • ((ζ, 0, 0) : QDom))).2 = 0 := by
  refine toLpOrZero_of_ae_zero ?_
  filter_upwards [qPoint_tangential_ae Jbar h0 χT χN β ζ r] with q h
  rw [h]; exact cToVec_zero

theorem qMap_zero (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) : qMap Jbar χT χN β 0 = 0 := by
  have e : (0 : QDom) = (0 : ℝ) • ((0, 0, 0) : QDom) := by simp
  refine Prod.ext ?_ ?_
  · rw [e]
    refine toLpOrZero_of_ae_zero ?_
    filter_upwards [ae_cToVec_fst Jbar h0 χT χN β 0 0] with q h
    rw [h, zero_smul]; rfl
  · rw [e]; exact qMap_tangential_snd Jbar h0 χT χN β 0 0

lemma hasDerivAt_ray {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : QDom → F}
    (hd : DifferentiableAt ℝ f 0) (h : QDom) :
    HasDerivAt (fun r : ℝ => f (r • h)) (fderiv ℝ f 0 h) 0 := by
  have h1 : HasDerivAt (fun r : ℝ => r • h) h 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const h
  have h2 : HasFDerivAt f (fderiv ℝ f 0) ((fun r : ℝ => r • h) 0) := by
    show HasFDerivAt f (fderiv ℝ f 0) ((0 : ℝ) • h)
    rw [zero_smul]; exact hd.hasFDerivAt
  exact h2.comp_hasDerivAt (0 : ℝ) h1

/-- **Tangential derivative.** -/
theorem fderiv_qMap_tangential (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd) (χT χN β : ℝ → ℝ)
    (hd : DifferentiableAt ℝ (qMap Jbar χT χN β) 0) (ε : ℝ) (hε : 0 < ε)
    (hmem : ∀ x ∈ ball (0 : QDom) ε,
      MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).1) 4 cylMeasure)
    (ζ : ↥(W1p 4 1)) :
    (((fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
        crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4)) ∧
      (fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).2 = 0 := by
  have hF := hasDerivAt_ray hd ((ζ, 0, 0) : QDom)
  have hGe := ae_cToVec_fst Jbar h0 χT χN β ζ
  have hsnd := qMap_tangential_snd Jbar h0 χT χN β ζ
  -- the formula is in `L⁴`, from one small nonzero point of the ray
  obtain ⟨r₀, hr₀, hr₀b⟩ : ∃ r₀ : ℝ, r₀ ≠ 0 ∧ r₀ • ((ζ, 0, 0) : QDom) ∈ ball (0 : QDom) ε := by
    refine ⟨ε / (2 * (‖((ζ, 0, 0) : QDom)‖ + 1)), by positivity, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have ha := norm_nonneg ((ζ, 0, 0) : QDom)
    generalize ‖((ζ, 0, 0) : QDom)‖ = a at ha ⊢
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hG : MemLp (crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4)) 4 cylMeasure := by
    have h1 := ((hmem _ hr₀b).ae_eq (hGe r₀)).const_smul r₀⁻¹
    refine h1.ae_eq (Eventually.of_forall fun q => ?_)
    simp [smul_smul, inv_mul_cancel₀ hr₀]
  have hray : ∀ r : ℝ, (qMap Jbar χT χN β (r • ((ζ, 0, 0) : QDom))).1 = (hG.const_smul r).toLp _ := by
    intro r
    exact (toLpOrZero_eq_toLp ((hG.const_smul r).ae_eq (hGe r).symm)).trans
      ((MemLp.toLp_eq_toLp_iff _ _).2 (hGe r))
  refine ⟨?_, ?_⟩
  · have hF1 : HasDerivAt (fun r : ℝ => (qMap Jbar χT χN β (r • ((ζ, 0, 0) : QDom))).1)
        (fderiv ℝ (qMap Jbar χT χN β) 0 ((ζ, 0, 0) : QDom)).1 0 :=
      ((ContinuousLinearMap.fst ℝ (LpCyl 1 4) (LpCyl 1 4)).hasFDerivAt.comp_hasDerivAt 0 hF)
    refine ae_eq_of_hasDerivAt hF1 (by rw [zero_smul, qMap_zero Jbar h0, Prod.fst_zero])
      (fun n q => (1 / ((n : ℝ) + 1)) • crApply (fun x => deriv χT x.1 • (1 : Mat 1))
        (ζ : Triple 1 4) q) (fun n => ?_) _ (Eventually.of_forall fun q => ?_)
    · rw [hray]; exact (hG.const_smul _).coeFn_toLp
    · refine tendsto_const_nhds.congr fun n => ?_
      rw [smul_smul, mul_one_div_cancel (by positivity), one_smul]
  · have hF2 : HasDerivAt (fun r : ℝ => (qMap Jbar χT χN β (r • ((ζ, 0, 0) : QDom))).2)
        (fderiv ℝ (qMap Jbar χT χN β) 0 ((ζ, 0, 0) : QDom)).2 0 :=
      ((ContinuousLinearMap.snd ℝ (LpCyl 1 4) (LpCyl 1 4)).hasFDerivAt.comp_hasDerivAt 0 hF)
    have e : (fun r : ℝ => (qMap Jbar χT χN β (r • ((ζ, 0, 0) : QDom))).2) = fun _ => 0 :=
      funext fun r => hsnd r
    rw [e] at hF2
    exact hF2.unique (hasDerivAt_const 0 0)

/-! ### The normal direction -/

lemma cToVec_rsmul (r : ℝ) (a : ℂ) : cToVec (r • a) = r • cToVec a := by
  rw [Complex.real_smul, cToVec_smul]

lemma qPt_normal_snd (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (q : ℝ × ℝ)
    (b1 b2 b3 : ℂ) :
    (qPt Jbar χT χN β q 0 0 0 0 b1 b2 b3).2 = (Real.exp (-χN q.1) : ℂ) *
      ((Real.exp (χN q.1) : ℂ) * (((deriv χN q.1 : ℝ) : ℂ) * b1 + b2) +
        (Jbar (cylInf q.1 q.2, (Real.exp (χN q.1) : ℂ) * b1)
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2, (Real.exp (χN q.1) : ℂ) * b3)).2) := by
  simp [qPt]

/-- The pointwise difference quotient on the normal ray. -/
lemma hasDerivAt_normal_ray (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χN : ℝ → ℝ) (q : ℝ × ℝ) (b1 b2 b3 : ℂ) :
    HasDerivAt (fun r : ℝ => (Real.exp (-χN q.1) : ℂ) *
      ((Real.exp (χN q.1) : ℂ) * (((deriv χN q.1 : ℝ) : ℂ) * ((r : ℂ) * b1) + (r : ℂ) * b2) +
        (Jbar (cylInf q.1 q.2, (Real.exp (χN q.1) : ℂ) * ((r : ℂ) * b1))
          (((2 * π : ℝ) : ℂ) * Complex.I * cylInf q.1 q.2,
            (Real.exp (χN q.1) : ℂ) * ((r : ℂ) * b3))).2))
      (((deriv χN q.1 : ℝ) : ℂ) * b1 + b2 + Complex.I * b3 +
        QS.tN Jbar (cylInf q.1 q.2) b1) 0 := by
  set z := cylInf q.1 q.2
  set e : ℂ := (Real.exp (χN q.1) : ℂ)
  set e' : ℂ := (Real.exp (-χN q.1) : ℂ)
  set d : ℂ := ((deriv χN q.1 : ℝ) : ℂ)
  have hr : HasDerivAt (fun r : ℝ => (r : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have hb : ∀ b : ℂ, HasDerivAt (fun r : ℝ => e * ((r : ℂ) * b)) (e * b) 0 := fun b => by
    simpa using (hr.mul_const b).const_mul e
  -- the `Jbar` factor
  have hJd : HasFDerivAt (fun w : ℂ => Jbar (z, w)) (QS.dW Jbar z) (e * (((0 : ℝ) : ℂ) * b1)) := by
    simp only [Complex.ofReal_zero, zero_mul, mul_zero]
    have hU : IsOpen (Set.univ ×ˢ ball (0 : ℂ) ρ) :=
      (isOpen_univ (X := ℂ)).prod (isOpen_ball (x := (0 : ℂ)))
    have hda : DifferentiableAt ℝ Jbar (z, 0) :=
      (hJ.contDiffAt (hU.mem_nhds ⟨mem_univ _, mem_ball_self (x := (0 : ℂ)) hρ⟩)).differentiableAt (by simp)
    exact (hda.comp (0 : ℂ) ((differentiableAt_const z).prodMk differentiableAt_id)).hasFDerivAt
  have hc := hJd.comp_hasDerivAt (0 : ℝ) (hb b1)
  have hu : HasDerivAt (fun r : ℝ => (((2 * π : ℝ) : ℂ) * Complex.I * z, e * ((r : ℂ) * b3)))
      ((0 : ℂ), e * b3) 0 := (hasDerivAt_const _ _).prodMk (hb b3)
  have hcu := hc.clm_apply hu
  have h2 := ((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcu)
  have hlin : HasDerivAt (fun r : ℝ => e * (d * ((r : ℂ) * b1) + (r : ℂ) * b2)) (e * (d * b1 + b2)) 0 := by
    simpa using (((hr.mul_const b1).const_mul d).add (hr.mul_const b2)).const_mul e
  have htot := (hlin.add h2).const_mul e'
  refine htot.congr_deriv ?_
  have hsm : e * b1 = (Real.exp (χN q.1)) • b1 := (Complex.real_smul ..).symm
  have key : QS.dW Jbar z (e * b1) = (Real.exp (χN q.1)) • QS.dW Jbar z b1 := by
    rw [hsm, map_smul]
  have hee : e' * e = 1 := exp_mul_exp_neg _
  have htN : QS.tN Jbar z b1 = ((QS.dW Jbar z b1) (((2 * π : ℝ) : ℂ) * Complex.I * z, 0)).2 := rfl
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, h0, ContinuousLinearMap.coe_snd',
    Function.comp_apply, Prod.snd_add, jStd_apply, key, ContinuousLinearMap.smul_apply,
    Prod.smul_snd, Complex.real_smul, htN]
  linear_combination (d * b1 + b2 + Complex.I * b3 +
    ((QS.dW Jbar z b1) (((2 * π : ℝ) : ℂ) * Complex.I * z, 0)).2) * hee

/-- **Normal derivative.** -/
theorem fderiv_qMap_normal (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (h0 : ∀ z : ℂ, Jbar (z, 0) = jStd)
    (χT χN β : ℝ → ℝ) (hd : DifferentiableAt ℝ (qMap Jbar χT χN β) 0) (ε : ℝ) (hε : 0 < ε)
    (hmem : ∀ x ∈ ball (0 : QDom) ε,
      MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).2) 4 cylMeasure)
    (ζ : ↥(W1p 4 1)) :
    ((fderiv ℝ (qMap Jbar χT χN β) 0 (0, 0, ζ)).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
      crApply (fun x => normalCoeff Jbar x + deriv χN x.1 • (1 : Mat 1)) (ζ : Triple 1 4) := by
  have hF := hasDerivAt_ray hd ((0, 0, ζ) : QDom)
  have hF2 : HasDerivAt (fun r : ℝ => (qMap Jbar χT χN β (r • ((0, 0, ζ) : QDom))).2)
      (fderiv ℝ (qMap Jbar χT χN β) 0 ((0, 0, ζ) : QDom)).2 0 :=
    ((ContinuousLinearMap.snd ℝ (LpCyl 1 4) (LpCyl 1 4)).hasFDerivAt.comp_hasDerivAt 0 hF)
  -- eventually the ray point lies in the ball
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N,
      (1 / ((n : ℝ) + 1)) • ((0, 0, ζ) : QDom) ∈ ball (0 : QDom) ε := by
    have ht : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) • ((0, 0, ζ) : QDom)) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const ((0, 0, ζ) : QDom)
    exact eventually_atTop.1 (ht.eventually (ball_mem_nhds 0 hε))
  open Classical in
  refine ae_eq_of_hasDerivAt hF2 (by rw [zero_smul, qMap_zero Jbar h0, Prod.snd_zero])
    (fun n => if N ≤ n then
        (fun q => cToVec (qPoint Jbar χT χN β ((1 / ((n : ℝ) + 1)) • ((0, 0, ζ) : QDom)) q).2)
      else ((qMap Jbar χT χN β ((1 / ((n : ℝ) + 1)) • ((0, 0, ζ) : QDom))).2 : ℝ × ℝ → Vec 1))
    (fun n => ?_) _ ?_
  · by_cases hn : N ≤ n
    · rw [if_pos hn]; exact coeFn_toLpOrZero (hmem _ (hN n hn))
    · rw [if_neg hn]
  · obtain ⟨z1, z2, z3⟩ := coeFn_zero_triple 0
    have hall := ae_all_iff.2 fun n : ℕ => qPoint_smul_ae Jbar χT χN β 0 ζ 0 (1 / ((n : ℝ) + 1))
    filter_upwards [hall, z1, z2, z3] with q hq h1 h2 h3
    have hlim := ((continuous_cToVec.tendsto _).comp
      ((hasDerivAt_normal_ray ρ hρ Jbar hJ h0 χN q (vecToC ((ζ : Triple 1 4).1 q))
        (vecToC ((ζ : Triple 1 4).2.1 q)) (vecToC ((ζ : Triple 1 4).2.2 q))).tendsto_slope_zero_right.comp
        tendsto_rn))
    rw [← vecToC_crApply_normal, cToVec_vecToC] at hlim
    refine hlim.congr' ((eventually_ge_atTop N).mono fun n hn => ?_)
    have hqn := hq n
    simp only [Function.comp_apply, if_pos hn, hqn, h1, h2, h3, Pi.zero_apply, vecToC_zero,
      mul_zero, smul_zero, qPt_normal_snd, zero_add]
    rw [← cToVec_rsmul]
    congr 1
    simp only [one_div, inv_inv, Complex.ofReal_zero, zero_mul, mul_zero, h0, jStd_apply,
      zero_add, add_zero, sub_zero]

end QN

end

end FiniteEnergyPlane

/-!
# Reduction of `qMap_smooth_of_isStdTubeStructure` to `exists_smooth_qPoint_rep`

`qMap` agrees with the smooth representative on a ball, so it is smooth there; `qMap 0 = 0` and
the derivative blocks at `0` are identified through difference quotients (`Scratch/JWQ_N6`, `N7`).
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology Set CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

namespace QN

theorem qMap_smooth_of_isStdTubeStructure_aux (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ContDiffOn ℝ ∞ (qMap Jbar χT χN β) (ball 0 ε) ∧ qMap Jbar χT χN β 0 = 0 ∧
      (∀ ζ : ↥(W1p 4 1),
        (((fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
            crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4)) ∧
          (fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).2 = 0) ∧
      ∀ ζ : ↥(W1p 4 1),
        ((fderiv ℝ (qMap Jbar χT χN β) 0 (0, 0, ζ)).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
          crApply (fun x => normalCoeff Jbar x + deriv χN x.1 • (1 : Mat 1)) (ζ : Triple 1 4) := by
  obtain ⟨ε, hε, F, hF, hFx⟩ :=
    exists_smooth_qPoint_rep ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
  have hJ := hstd.1
  have h0 := hstd.2.2.1
  have hmem1 : ∀ x ∈ ball (0 : QDom) ε,
      MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).1) 4 cylMeasure := fun x hx =>
    (Lp.memLp (F x).1).ae_eq (hFx x hx).1
  have hmem2 : ∀ x ∈ ball (0 : QDom) ε,
      MemLp (fun q => cToVec (qPoint Jbar χT χN β x q).2) 4 cylMeasure := fun x hx =>
    (Lp.memLp (F x).2).ae_eq (hFx x hx).2
  have heq : ∀ x ∈ ball (0 : QDom) ε, qMap Jbar χT χN β x = F x := by
    intro x hx
    refine Prod.ext ?_ ?_
    · show toLpOrZero _ = _
      rw [toLpOrZero_eq_toLp (hmem1 x hx)]
      exact Lp.ext ((hmem1 x hx).coeFn_toLp.trans (hFx x hx).1.symm)
    · show toLpOrZero _ = _
      rw [toLpOrZero_eq_toLp (hmem2 x hx)]
      exact Lp.ext ((hmem2 x hx).coeFn_toLp.trans (hFx x hx).2.symm)
  have hC : ContDiffOn ℝ ∞ (qMap Jbar χT χN β) (ball 0 ε) :=
    hF.contDiffOn.congr heq
  have hd : DifferentiableAt ℝ (qMap Jbar χT χN β) 0 :=
    (hC.contDiffAt (ball_mem_nhds 0 hε)).differentiableAt (by simp)
  exact ⟨ε, hε, hC, qMap_zero Jbar h0 χT χN β,
    fun ζ => fderiv_qMap_tangential Jbar h0 χT χN β hd ε hε hmem1 ζ,
    fun ζ => fderiv_qMap_normal ρ hρ Jbar hJ h0 χT χN β hd ε hε hmem2 ζ⟩

end QN

end

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ δT : ℝ) (hδ : δ < 0) (hδT : δT ∈ Set.Ioo (max δ (-(2 * π))) 0)
    (χT χN β : ℝ → ℝ) (hχT : IsSlopeWeight χT π (2 * π + δT)) (hχN : IsSlopeWeight χN π δ)
    (hβ : IsLeftCutoff β) :
    ∃ ε > 0, ContDiffOn ℝ ∞ (qMap Jbar χT χN β) (ball 0 ε) ∧ qMap Jbar χT χN β 0 = 0 ∧
      (∀ ζ : ↥(W1p 4 1),
        (((fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).1 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
            crApply (fun x => deriv χT x.1 • (1 : Mat 1)) (ζ : Triple 1 4)) ∧
          (fderiv ℝ (qMap Jbar χT χN β) 0 (ζ, 0, 0)).2 = 0) ∧
      ∀ ζ : ↥(W1p 4 1),
        ((fderiv ℝ (qMap Jbar χT χN β) 0 (0, 0, ζ)).2 : ℝ × ℝ → Vec 1) =ᵐ[cylMeasure]
          crApply (fun x => normalCoeff Jbar x + deriv χN x.1 • (1 : Mat 1)) (ζ : Triple 1 4) :=
  QN.qMap_smooth_of_isStdTubeStructure_aux ρ b hρ hb Jbar Jinf Sinf hstd δ δT hδ hδT χT χN β hχT hχN hβ
