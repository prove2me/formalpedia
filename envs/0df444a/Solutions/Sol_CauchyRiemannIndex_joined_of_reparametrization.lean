-- Prove2me | solution 1 for CauchyRiemannIndex.joined_of_reparametrization
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T12:57:31.366891+00:00
-- url     : https://prove2.me/submissions/f1fb6357-f4f5-4d7e-99c4-27ad63b26194

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace CauchyRiemannIndex

open Matrix

/-- Reparametrized fundamental solutions. -/
lemma crj2_fund_comp {n : ℕ} (S : ℝ → Mat n) (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ)
    (b b' : ℝ → ℝ) (hb : ∀ t, HasDerivAt b (b' t) t) (hb0 : b 0 = 0) :
    IsFundamentalSolution (fun t => b' t • S (b t)) (fun t => Ψ (b t)) := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  refine ⟨by simpa [hb0] using hΨ.1, fun t => ?_⟩
  have h := (hΨ.2 (b t)).scomp t (hb t)
  have e : b' t • (J₀ n * S (b t) * Ψ (b t)) = J₀ n * (b' t • S (b t)) * Ψ (b t) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e] at h
  exact h

lemma crj2_deriv_periodic (b b' : ℝ → ℝ) (hb : ∀ t, HasDerivAt b (b' t) t)
    (h1 : ∀ t, b (t + 1) = b t + 1) (t : ℝ) : b' (t + 1) = b' t := by
  have h₁ : HasDerivAt (fun x => b (x + 1)) (b' (t + 1) * (1 + 0)) t :=
    (hb (t + 1)).comp t ((hasDerivAt_id t).add (hasDerivAt_const t (1 : ℝ)))
  have h₂ : HasDerivAt (fun x => b (x + 1)) (b' t + 0) t := by
    have e : (fun x => b (x + 1)) = fun x => b x + 1 := funext h1
    rw [e]; exact (hb t).add (hasDerivAt_const t (1 : ℝ))
  simpa using h₁.unique h₂

theorem crj2_joined_reparam (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hn : IsNondegenerate S) (β β' : ℝ → ℝ) (hβ : ∀ t, HasDerivAt β (β' t) t)
    (hβ' : Continuous β') (h0 : β 0 = 0) (h1 : ∀ t, β (t + 1) = β t + 1) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧
      (∀ t, H (1, t) = β' t • S (β t)) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) := by
  have hβc : Continuous β := continuous_iff_continuousAt.2 fun t => (hβ t).continuousAt
  let b : unitInterval → ℝ → ℝ := fun τ t => (1 - (τ : ℝ)) * t + (τ : ℝ) * β t
  let b' : unitInterval → ℝ → ℝ := fun τ t => (1 - (τ : ℝ)) + (τ : ℝ) * β' t
  have hbd : ∀ τ t, HasDerivAt (b τ) (b' τ t) t := fun τ t => by
    have h := ((hasDerivAt_id t).const_mul (1 - (τ : ℝ))).add ((hβ t).const_mul (τ : ℝ))
    simp only [mul_one, id] at h
    exact h
  have hb0 : ∀ τ, b τ 0 = 0 := fun τ => by simp [b, h0]
  have hb1 : ∀ τ t, b τ (t + 1) = b τ t + 1 := fun τ t => by simp only [b, h1]; ring
  have hb'1 : ∀ τ t, b' τ (t + 1) = b' τ t := fun τ t =>
    crj2_deriv_periodic (b τ) (b' τ) (hbd τ) (hb1 τ) t
  let H : C(unitInterval × ℝ, Mat n) :=
    ⟨fun p => b' p.1 p.2 • S (b p.1 p.2), by
      have hS' := hS.1
      fun_prop⟩
  refine ⟨H, fun t => ?_, fun t => ?_, fun τ => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · simp [H, b, b']
  · simp [H, b, b']
  · exact H.continuous.comp (continuous_const.prodMk continuous_id)
  · intro t
    show b' τ (t + 1) • S (b τ (t + 1)) = b' τ t • S (b τ t)
    rw [hb'1, hb1, hS.2.1]
  · intro t
    exact (hS.2.2 (b τ t)).smul (b' τ t)
  · obtain ⟨Ψ, hΨ, -⟩ := fundamentalSolution_existsUnique n S hS.1
    intro Φ hΦ
    have hcont : Continuous (fun t => H (τ, t)) :=
      H.continuous.comp (continuous_const.prodMk continuous_id)
    have hcomp := crj2_fund_comp S Ψ hΨ (b τ) (b' τ) (hbd τ) (hb0 τ)
    have heq : Φ = fun t => Ψ (b τ t) :=
      (fundamentalSolution_existsUnique n _ hcont).unique hΦ hcomp
    rw [heq]
    have : b τ 1 = 1 := by simpa [hb0 τ] using hb1 τ 0
    simp only [this]
    exact hn Ψ hΨ

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution (n : ℕ) (S : ℝ → Mat n) (hS : IsSymLoop S)
    (hn : IsNondegenerate S) (β β' : ℝ → ℝ) (hβ : ∀ t, HasDerivAt β (β' t) t)
    (hβ' : Continuous β') (h0 : β 0 = 0) (h1 : ∀ t, β (t + 1) = β t + 1) :
    ∃ H : C(unitInterval × ℝ, Mat n), (∀ t, H (0, t) = S t) ∧
      (∀ t, H (1, t) = β' t • S (β t)) ∧
      ∀ τ, IsSymLoop (fun t => H (τ, t)) ∧ IsNondegenerate (fun t => H (τ, t)) :=
  crj2_joined_reparam n S hS hn β β' hβ hβ' h0 h1
