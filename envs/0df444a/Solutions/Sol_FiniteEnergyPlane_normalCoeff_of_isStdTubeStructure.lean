-- Prove2me | solution 1 for FiniteEnergyPlane.normalCoeff_of_isStdTubeStructure
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-12T18:18:44.232495+00:00
-- url     : https://prove2.me/submissions/69e382f1-122e-4f47-8fd6-cbdf102e58f2

import Definitions.Def_FiniteEnergyPlane_TubeFamily



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
# Q-S: the normal coefficient of a standard tube structure (proof of the sorry'd child in
`Scratch/JWQ_Stmts.lean`, under the namespace `FiniteEnergyPlane.QS`). Part 2: the exponential
decay of `normalCoeff - Sinf`, then the assembly.
-/

namespace FiniteEnergyPlane.QS

open Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff Real

noncomputable section

/-- `L ↦ A ∘ L ∘ B` as a continuous linear map. -/
def sandwich (A B : ℂ × ℂ →L[ℝ] ℂ × ℂ) : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] (ℂ × ℂ →L[ℝ] ℂ × ℂ) :=
  (ContinuousLinearMap.compL ℝ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ) A).comp
    ((ContinuousLinearMap.compL ℝ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).flip B)

theorem sandwich_apply (A B L : ℂ × ℂ →L[ℝ] ℂ × ℂ) : sandwich A B L = A.comp (L.comp B) := rfl

theorem hasFDerivAt_cylJ_w (ρ : ℝ) (hρ : 0 < ρ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ)) (s t : ℝ) :
    HasFDerivAt (fun w => cylJ Jbar s t w)
      ((sandwich (cylScaleInv s t) (cylScale s t)).comp (dW Jbar (cylInf s t))) 0 := by
  have hd : HasFDerivAt (fun w : ℂ => Jbar (cylInf s t, w)) (dW Jbar (cylInf s t)) 0 :=
    hasFDerivAt_w Jbar ρ hJ (cylInf s t) (mem_ball_self hρ)
  exact (sandwich (cylScaleInv s t) (cylScale s t)).hasFDerivAt.comp 0 hd

theorem cylScale_I (s t : ℝ) :
    cylScale s t (Complex.I, 0) = ((((2 * π : ℝ) : ℂ) * Complex.I * cylInf s t), 0) := by
  simp [cylScale]; ring

theorem cylScaleInv_snd (s t : ℝ) (p : ℂ × ℂ) : (cylScaleInv s t p).2 = p.2 := by
  simp [cylScaleInv]

theorem le_infty_nat (m : ℕ) : (m : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
theorem isExpAsymptoticTo_normalCoeff (ρ b : ℝ) (hρ : 0 < ρ)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    IsExpAsymptoticTo (normalCoeff Jbar) Sinf b := by
  intro i j
  have hJ := hstd.1
  have hJinf := hstd.2.2.2.1
  obtain ⟨⟨s₀, hFc⟩, hFb⟩ := hstd.2.2.2.2.2.1
  let F : ℝ × ℝ × ℂ → (ℂ × ℂ →L[ℝ] ℂ × ℂ) := fun q =>
    cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)
  let W' : Set (ℝ × ℝ × ℂ) := Set.Ioi s₀ ×ˢ Set.univ ×ˢ ball (0 : ℂ) ρ
  have hW' : IsOpen W' := isOpen_Ioi.prod (isOpen_univ.prod isOpen_ball)
  let W : Set (ℝ × ℝ) := Set.Ioi s₀ ×ˢ Set.univ
  have hW : IsOpen W := isOpen_Ioi.prod isOpen_univ
  let ι : ℝ × ℝ →L[ℝ] ℝ × ℝ × ℂ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).prod ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod 0)
  have hι : ∀ p : ℝ × ℝ, ι p = (p.1, p.2, 0) := fun p => rfl
  have hpre : ι ⁻¹' W' = W := by
    ext p
    simp only [Set.mem_preimage, hι, W', W, Set.mem_prod, Set.mem_Ioi, Set.mem_univ, true_and,
      mem_ball_self hρ, and_true]
  let ℓ : (ℂ × ℂ →L[ℝ] ℂ × ℂ) →L[ℝ] ℝ := (reImCLM i).comp (evSnd (Complex.I, 0))
  let v₀ : ℝ × ℝ × ℂ := ((0 : ℝ), (0 : ℝ), basisC j)
  let f : ℝ × ℝ → ℝ := fun p => normalCoeff Jbar p i j - Sinf p.2 i j
  -- the key identity on the end
  have key : ∀ p ∈ W, f p = ℓ (fderiv ℝ F (ι p) v₀) := by
    rintro ⟨s, t⟩ hp
    have hs : s₀ < s := hp.1
    have hmem : ((s, t, 0) : ℝ × ℝ × ℂ) ∈ W' := ⟨hs, Set.mem_univ _, mem_ball_self hρ⟩
    have hFd : DifferentiableAt ℝ F (s, t, 0) :=
      (hFc.contDiffAt (hW'.mem_nhds hmem)).differentiableAt (by simp)
    let ιw : ℂ →L[ℝ] ℝ × ℝ × ℂ := (0 : ℂ →L[ℝ] ℝ).prod ((0 : ℂ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℂ))
    have hιw : HasFDerivAt (fun w : ℂ => ((s, t, w) : ℝ × ℝ × ℂ)) ιw 0 :=
      (hasFDerivAt_const s 0).prodMk ((hasFDerivAt_const t 0).prodMk (hasFDerivAt_id 0))
    have h1 : HasFDerivAt (fun w : ℂ => F (s, t, w)) ((fderiv ℝ F (s, t, 0)).comp ιw) 0 :=
      hFd.hasFDerivAt.comp 0 hιw
    have h2 : HasFDerivAt (fun w : ℂ => F (s, t, w))
        ((sandwich (cylScaleInv s t) (cylScale s t)).comp (dW Jbar (cylInf s t)) -
          fderiv ℝ (fun w : ℂ => Jinf (t, w)) 0) 0 :=
      (hasFDerivAt_cylJ_w ρ hρ Jbar hJ s t).sub (hasFDerivAt_w Jinf ρ hJinf t (mem_ball_self hρ))
    have hE := h1.unique h2
    have hE' := congrArg (fun L => reIm i ((L (basisC j)) (Complex.I, 0)).2) hE
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.sub_apply,
      sandwich_apply, cylScale_I, cylScaleInv_snd] at hE'
    have hιwj : ιw (basisC j) = ((0 : ℝ), (0 : ℝ), basisC j) := by simp [ιw]
    rw [hιwj] at hE'
    show normalCoeff Jbar (s, t) i j - Sinf t i j = reImCLM i ((fderiv ℝ F (ι (s, t))
      ((0 : ℝ), (0 : ℝ), basisC j)) (Complex.I, 0)).2
    rw [reImCLM_apply, hι, hE', normalCoeff_eq, sinf_eq ρ b Jbar Jinf Sinf hstd t,
      ← Matrix.sub_apply, ← cMat_sub, cMat_apply]
    rfl
  refine ⟨⟨s₀, ?_⟩, ?_⟩
  · exact ((contDiff_normalCoeff ρ hρ Jbar hJ i j).sub
      ((contDiff_sinf ρ b hρ Jbar Jinf Sinf hstd i j).comp contDiff_snd)).contDiffOn
  · intro m
    obtain ⟨C, s₁, hC⟩ := hFb (m + 1)
    refine ⟨‖ℓ‖ * ‖v₀‖ * ‖ι‖ ^ m * C, max s₁ (s₀ + 1), ?_⟩
    intro s hs t
    have hp : ((s, t) : ℝ × ℝ) ∈ W := ⟨by simp only [Set.mem_Ioi]; linarith [le_max_right s₁ (s₀ + 1)],
      Set.mem_univ _⟩
    have hG : ContDiffOn ℝ ∞ (fderiv ℝ F) W' := hFc.fderiv_of_isOpen hW' (by simp)
    have hGι : ContDiffOn ℝ ∞ (fderiv ℝ F ∘ ι) W := by
      rw [← hpre]
      exact hG.comp ι.contDiff.contDiffOn (fun x hx => hx)
    have e1 : iteratedFDeriv ℝ m (fun p : ℝ × ℝ => normalCoeff Jbar p i j - Sinf p.2 i j) (s, t) =
        iteratedFDerivWithin ℝ m (ℓ ∘ (fun p => (fderiv ℝ F ∘ ι) p v₀)) W (s, t) := by
      rw [← iteratedFDerivWithin_of_isOpen m hW hp]
      exact iteratedFDerivWithin_congr (fun p hp' => key p hp') hp m
    rw [e1]
    have hg2 : ContDiffOn ℝ ∞ (fun p => (fderiv ℝ F ∘ ι) p v₀) W :=
      hGι.clm_apply contDiffOn_const
    have e2 := ℓ.norm_iteratedFDerivWithin_comp_left (hg2 (s, t) hp) hW.uniqueDiffOn hp (le_infty_nat m)
    have e2' := norm_iteratedFDerivWithin_clm_apply_const (c := v₀) (hGι (s, t) hp)
      hW.uniqueDiffOn hp (le_infty_nat m)
    have e3 : iteratedFDerivWithin ℝ m (fderiv ℝ F ∘ ι) W (s, t) =
        (iteratedFDerivWithin ℝ m (fderiv ℝ F) W' (ι (s, t))).compContinuousLinearMap
          fun _ => ι := by
      rw [← hpre]
      exact ι.iteratedFDerivWithin_comp_right hG hW'.uniqueDiffOn
        (by rw [hpre]; exact hW.uniqueDiffOn) (by rw [← Set.mem_preimage, hpre]; exact hp)
        (le_infty_nat m)
    have hιmem : ι (s, t) ∈ W' := by rw [← Set.mem_preimage, hpre]; exact hp
    have e4 : ‖iteratedFDerivWithin ℝ m (fderiv ℝ F ∘ ι) W (s, t)‖ ≤
        ‖iteratedFDeriv ℝ (m + 1) F (s, t, 0)‖ * ‖ι‖ ^ m := by
      rw [e3]
      refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        iteratedFDerivWithin_of_isOpen m hW' hιmem, norm_iteratedFDeriv_fderiv, hι]
    have e5 := hC s (le_trans (le_max_left _ _) hs) t 0 (mem_ball_self hρ)
    have hℓ : 0 ≤ ‖ℓ‖ := ContinuousLinearMap.opNorm_nonneg _
    have hv : 0 ≤ ‖v₀‖ := by positivity
    have hιn : 0 ≤ ‖ι‖ ^ m := pow_nonneg (ContinuousLinearMap.opNorm_nonneg _) m
    calc ‖iteratedFDerivWithin ℝ m (ℓ ∘ (fun p => (fderiv ℝ F ∘ ι) p v₀)) W (s, t)‖
        ≤ ‖ℓ‖ * ‖iteratedFDerivWithin ℝ m (fun p => (fderiv ℝ F ∘ ι) p v₀) W (s, t)‖ := e2
      _ ≤ ‖ℓ‖ * (‖v₀‖ * ‖iteratedFDerivWithin ℝ m (fderiv ℝ F ∘ ι) W (s, t)‖) :=
          mul_le_mul_of_nonneg_left e2' hℓ
      _ ≤ ‖ℓ‖ * (‖v₀‖ * (‖iteratedFDeriv ℝ (m + 1) F (s, t, 0)‖ * ‖ι‖ ^ m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e4 hv) hℓ
      _ ≤ ‖ℓ‖ * (‖v₀‖ * ((C * Real.exp (-(b * s))) * ‖ι‖ ^ m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right e5 hιn) hv) hℓ
      _ = ‖ℓ‖ * ‖v₀‖ * ‖ι‖ ^ m * C * Real.exp (-(b * s)) := by ring

theorem normalCoeff_of_isStdTubeStructure (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    (∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => normalCoeff Jbar x i j)) ∧
      (∀ s t : ℝ, normalCoeff Jbar (s, t + 1) = normalCoeff Jbar (s, t)) ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      IsExpAsymptoticTo (normalCoeff Jbar) Sinf b ∧
      IsPlaneCoeff (normalCoeff Jbar) :=
  ⟨contDiff_normalCoeff ρ hρ Jbar hstd.1, normalCoeff_per Jbar,
    contDiff_sinf ρ b hρ Jbar Jinf Sinf hstd,
    isExpAsymptoticTo_normalCoeff ρ b hρ Jbar Jinf Sinf hstd,
    isPlaneCoeff_normalCoeff ρ hρ Jbar hstd.1 hstd.2.1 hstd.2.2.1⟩

end


end FiniteEnergyPlane.QS

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

theorem solution (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    (∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => normalCoeff Jbar x i j)) ∧
      (∀ s t : ℝ, normalCoeff Jbar (s, t + 1) = normalCoeff Jbar (s, t)) ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      IsExpAsymptoticTo (normalCoeff Jbar) Sinf b ∧
      IsPlaneCoeff (normalCoeff Jbar) :=
  QS.normalCoeff_of_isStdTubeStructure ρ b hρ hb Jbar Jinf Sinf hstd
