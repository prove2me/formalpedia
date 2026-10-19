-- Prove2me | solution 1 for CauchyRiemannIndex.asymptoticCZIndex_eq_of_joined
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:27:44.919626+00:00
-- url     : https://prove2.me/submissions/a69159b8-bc66-4523-a246-58707d3526da

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic
import Theorems.Thm_CauchyRiemannIndex_linearODE_continuous_param
import Theorems.Thm_CauchyRiemannIndex_asymptoticCZIndex_eq_czIndex
import Theorems.Thm_ConleyZehnder_czIndex_eq_of_family
import Mathlib.Analysis.Matrix.Normed

namespace CauchyRiemannIndex

/-- Joint continuity of the fundamental solutions of a continuous family of loops. -/
lemma crj_fund_family_continuous {n : ℕ} (H : C(unitInterval × ℝ, Mat n)) (Ψ : unitInterval → ℝ → Mat n)
    (hΨ : ∀ τ, IsFundamentalSolution (fun t => H (τ, t)) (Ψ τ)) :
    Continuous (fun p : unitInterval × unitInterval => Ψ p.1 p.2) := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let B : unitInterval × ℝ → Mat n →L[ℝ] Mat n :=
    fun p => LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (J₀ n * H p))
  have hB : Continuous B := by
    refine continuous_clm_apply.2 fun y => ?_
    exact (continuous_const.mul H.continuous).mul continuous_const
  exact linearODE_continuous_param B hB (fun _ => 1) continuous_const Ψ (fun τ => (hΨ τ).1)
    (fun τ t => (hΨ τ).2 t)

lemma crj_eq_of_joined (n : ℕ) (S₀ S₁ : ℝ → Mat n)
    (H : C(unitInterval × ℝ, Mat n)) (hH₀ : ∀ t, H (0, t) = S₀ t) (hH₁ : ∀ t, H (1, t) = S₁ t)
    (hH : ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t))) :
    asymptoticCZIndex S₀ = asymptoticCZIndex S₁ := by
  choose Ψ hΨ using fun τ =>
    (fundamentalSolution_existsUnique n (fun t => H (τ, t)) (hH τ).1.1).exists
  let G : C(unitInterval × unitInterval, Mat n) :=
    ⟨fun p => Ψ p.1 p.2, crj_fund_family_continuous H Ψ hΨ⟩
  have hsymp : ∀ s t, ConleyZehnder.IsSymplectic (G (s, t)) := fun s t =>
    fundamentalSolution_symplectic n _ (hH s).1.2.2 (Ψ s) (hΨ s) t
  have h0 : ∀ s, G (s, 0) = 1 := fun s => by
    show Ψ s ((0 : unitInterval) : ℝ) = 1
    simpa using (hΨ s).1
  have h1 : ∀ s, (1 - G (s, 1)).det ≠ 0 := fun s => by
    show (1 - Ψ s ((1 : unitInterval) : ℝ)).det ≠ 0
    simpa using (hH s).2 (Ψ s) (hΨ s)
  let ψ : unitInterval → C(unitInterval, Mat n) := fun s =>
    ⟨fun t => G (s, t), by fun_prop⟩
  have hfam := ConleyZehnder.czIndex_eq_of_family G hsymp h0 h1 (ψ 0) (ψ 1)
    (fun _ => rfl) (fun _ => rfl)
  have e0 : S₀ = fun t => H (0, t) := funext fun t => (hH₀ t).symm
  have e1 : S₁ = fun t => H (1, t) := funext fun t => (hH₁ t).symm
  have b0 := asymptoticCZIndex_eq_czIndex n _ (hH 0).1 (hH 0).2 (Ψ 0) (hΨ 0) (ψ 0) (fun _ => rfl)
  have b1 := asymptoticCZIndex_eq_czIndex n _ (hH 1).1 (hH 1).2 (Ψ 1) (hΨ 1) (ψ 1) (fun _ => rfl)
  rw [e0, e1, b0, b1]
  exact hfam.symm

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (S₀ S₁ : ℝ → Mat n)
    (H : C(unitInterval × ℝ, Mat n)) (hH₀ : ∀ t, H (0, t) = S₀ t) (hH₁ : ∀ t, H (1, t) = S₁ t)
    (hH : ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t))) :
    asymptoticCZIndex S₀ = asymptoticCZIndex S₁ :=
  crj_eq_of_joined n S₀ S₁ H hH₀ hH₁ hH
