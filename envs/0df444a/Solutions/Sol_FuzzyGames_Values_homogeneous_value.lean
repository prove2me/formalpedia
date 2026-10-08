-- Prove2me | solution 1 for FuzzyGames.Values.homogeneous_value
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:18:59.634553+00:00
-- url     : https://prove2.me/submissions/b5d1c5df-fcf4-4887-9caf-2385f1e54e11

import Mathlib
import Definitions.Def_FuzzyGames_Values_Basic

open FuzzyGames.Values
open MeasureTheory
open scoped Topology

theorem solution (n : ℕ) (v : Vn n) (hv : IsPosHomogeneous v.1) :
    (∀ t : ℝ, 0 < t → fderiv ℝ v.1 (t • (1 : Fin n → ℝ)) = fderiv ℝ v.1 1) ∧
      diagValue v.1 = fun i => fderiv ℝ v.1 1 (Pi.single i 1) := by
  have hd : Differentiable ℝ v.1 := v.property.1.differentiable (by simp)
  have hder : ∀ t : ℝ, 0 < t →
      fderiv ℝ v.1 (t • (1 : Fin n → ℝ)) = fderiv ℝ v.1 1 := by
    intro t ht
    have hnonneg : ∀ᶠ x : Fin n → ℝ in 𝓝 (1 : Fin n → ℝ), 0 ≤ x := by
      apply Filter.eventually_all.mpr
      intro i
      simpa using ((continuous_apply i).continuousAt (x := (1 : Fin n → ℝ))).eventually
        (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1))
    have heq : (fun x : Fin n → ℝ => v.1 (t • x)) =ᶠ[𝓝 1]
        (fun x => t • v.1 x) := hnonneg.mono fun x hx => hv t ht x hx
    have hleft := (hd (t • (1 : Fin n → ℝ))).hasFDerivAt.comp 1
      ((hasFDerivAt_id (1 : Fin n → ℝ)).const_smul t)
    have hright := (hd (1 : Fin n → ℝ)).hasFDerivAt.const_smul t
    have he := (hleft.congr_of_eventuallyEq heq.symm).unique hright
    apply ContinuousLinearMap.ext
    intro x
    have hx := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L x) he
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at hx
    exact mul_left_cancel₀ (ne_of_gt ht) hx
  refine ⟨hder, ?_⟩
  funext i
  unfold diagValue
  calc
    (∫ t in (0 : ℝ)..1, fderiv ℝ v.1 (t • (1 : Fin n → ℝ)) (Pi.single i 1)) =
        ∫ _ in (0 : ℝ)..1, fderiv ℝ v.1 1 (Pi.single i 1) := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun t ht => by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        rw [hder t ht.1]
    _ = _ := by simp

#print axioms solution
