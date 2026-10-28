-- Prove2me | solution 1 for CountingMatroid.Bridge.intersectionSolver_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:43:56.509538+00:00
-- url     : https://prove2.me/submissions/8d2e60ad-5d09-43a3-9f09-01cec43ddbe5

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_intersectionSolver_correct
import Theorems.Thm_CountingMatroid_Analysis_FeasibilitySolver_commonBaseCount_pos_iff_common_independent
import Theorems.Thm_CountingMatroid_Analysis_IntersectionSearchCost_intersectionSolver_bounded
import Theorems.Thm_CountingMatroid_Analysis_ResourceBound_output_resource_bound
import Theorems.Thm_CountingMatroid_Analysis_OutputAccuracy_output_accuracy

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations CountingMatroid.Model.Subroutines
open CountingMatroid.Bridge

/-- Accuracy and source resource bounds for the named augmenting-path solver.
This fixes the implementation to compile, without choosing an unspecified witness. -/
theorem solution :
    ∃ (C degree : ℕ),
      ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (o₁ o₂ : IndependenceOracle n) (p : InputParams),
        FullGround M₁ M₂ → CommonRank r M₁ M₂ →
        ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
        let law := Model.Run.outputLaw Analysis.IntersectionSearch.intersectionSolver n r o₁ o₂ p
        let Z : ℚ := commonBaseCount M₁ M₂
        let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹)
        law.toOuterMeasure
            {x | x.1 < (1 - p.ε) * Z ∨ (1 + p.ε) * Z < x.1} ≤
            ENNReal.ofReal (p.δ : ℝ) ∧
        (Z = 0 → ∀ x ∈ law.support, x.1 = 0) ∧
        ∀ x ∈ law.support,
          0 ≤ x.1 ∧
          x.2.oracleCalls ≤ C * (size + 1) ^ degree ∧
          x.2.bitOps ≤ C * (size + 1) ^ degree := by
  classical
  let contract : FeasibilityContract := {
    implementation := Analysis.IntersectionSearch.intersectionSolver
    callConstant := 100000
    callDegree := 8
    bitConstant := 100000
    bitDegree := 8
    correct := by
      intro n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
      rw [Analysis.FeasibilitySolver.intersectionSolver_correct n r M₁ M₂ o₁ o₂ hfull h₁ h₂]
      exact Bool.decide_congr
        (Analysis.FeasibilitySolver.commonBaseCount_pos_iff_common_independent n r M₁ M₂ hr).symm
    bounded := Analysis.IntersectionSearchCost.intersectionSolver_bounded }
  obtain ⟨C, degree, hresource⟩ :=
    CountingMatroid.Analysis.ResourceBound.output_resource_bound contract
  refine ⟨C, degree, ?_⟩
  intro n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂
  have haccuracy :=
    CountingMatroid.Analysis.OutputAccuracy.output_accuracy
      contract.implementation contract.correct n r M₁ M₂ o₁ o₂ p
      hfull hr h₁ h₂
  have hrle : r ≤ n := by
    have hle : M₁.eRank ≤ (n : ENat) := by
      calc
        M₁.eRank ≤ M₁.E.encard := M₁.eRank_le_encard_ground
        _ = (n : ENat) := by simp [hfull.1]
    rw [hr.1] at hle
    exact_mod_cast hle
  exact ⟨haccuracy.1, haccuracy.2, hresource n r o₁ o₂ p hrle⟩
