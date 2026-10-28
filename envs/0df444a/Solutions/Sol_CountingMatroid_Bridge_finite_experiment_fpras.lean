-- Prove2me | solution 1 for CountingMatroid.Bridge.finite_experiment_fpras
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T19:49:04.046993+00:00
-- url     : https://prove2.me/submissions/eb47f2a9-c1fa-4a4e-9ea7-d2b75e3c35ac

import Mathlib
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_Presampling
import Theorems.Thm_CountingMatroid_countingmatroid_main
import Theorems.Thm_CountingMatroid_Analysis_SingleRunAccuracy_fairTape_support_iff_length
import Theorems.Thm_CountingMatroid_Bridge_presampled_bits_polynomial
import Theorems.Thm_CountingMatroid_Bridge_polynomial_source_bound_to_mission
import Theorems.Thm_CountingMatroid_Bridge_exactOracles_to_source
import Theorems.Thm_CountingMatroid_Bridge_commonBaseCount_eq_mission
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_event_card
import Theorems.Thm_CountingMatroid_Bridge_outputLaw_presampled

set_option autoImplicit false
set_option maxHeartbeats 800000

open CountingMatroid CountingMatroid.Model CountingMatroid.Model.Run CountingMatroid.Model.Operations
open CountingMatroid.Bridge

/-- The original mission's mathematical approximation specification is
already realized by one finite fair-bit experiment with a polynomial bit
budget and polynomial source charges. This is NOT a register-machine
realization: `presampledOutcome` is still the mathematical source evaluator.
The remaining implementation obligation must produce one fixed program. -/
theorem solution :
    ∃ (solver : Subroutines.FeasibilityImplementation) (C d : ℕ), 0 < C ∧
      ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (p : InputParams),
        M₁.E = Set.univ → M₂.E = Set.univ →
        M₁.eRank = (r : ℕ∞) → M₂.eRank = (r : ℕ∞) →
        OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O →
        let K := (Program.schedule n p).val.repetitions * blockLength n r p
        let B := OAI.CommonBasesFPRAS.resourceBound C d n r p.ε p.δ
        let Z := OAI.CommonBasesFPRAS.commonBaseCount M₁ M₂
        K ≤ B ∧
        (Set.ncard {bits : List Bool | bits.length = K ∧
          ((presampledOutcome solver n r (O false) (O true) p bits).1 < (1-p.ε)*(Z:ℚ) ∨
          (1+p.ε)*(Z:ℚ) < (presampledOutcome solver n r (O false) (O true) p bits).1)} : ENNReal)
            * (1/2 : ENNReal)^K ≤ ENNReal.ofReal (p.δ : ℝ) ∧
        ∀ bits : List Bool, bits.length = K →
          let out := presampledOutcome solver n r (O false) (O true) p bits
          0 ≤ out.1 ∧ (Z = 0 → out.1 = 0) ∧
          out.2.oracleCalls ≤ B ∧ out.2.bitOps ≤ B := by
  obtain ⟨solver, Cs, ds, _, hs⟩ := CountingMatroid.countingmatroid_main
  obtain ⟨Ck, dk, hk⟩ := presampled_bits_polynomial
  let D := max ds dk
  let A := Cs + Ck + 1
  refine ⟨solver, A * 6^D, D, by dsimp [A]; positivity, ?_⟩
  intro n r M₁ M₂ O p hE₁ hE₂ hr₁ hr₂ hO
  dsimp only
  let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  have hX : 0 < X := by dsimp [X]; omega
  have hdom (c e : ℕ) (hc : c ≤ A) (he : e ≤ D) :
      c * X^e ≤ OAI.CommonBasesFPRAS.resourceBound (A * 6^D) D n r p.ε p.δ := by
    exact (Nat.mul_le_mul hc (Nat.pow_le_pow_right hX he)).trans
      (polynomial_source_bound_to_mission A D n r p)
  have horacles := exactOracles_to_source M₁ M₂ O hO
  have hmain := hs n r M₁ M₂ (O false) (O true) p ⟨hE₁, hE₂⟩
    ⟨hr₁, hr₂⟩ horacles.1 horacles.2
  dsimp only at hmain
  rw [commonBaseCount_eq_mission] at hmain
  refine ⟨(hk n r p).trans (hdom Ck dk (by dsimp [A]; omega) (le_max_right _ _)), ?_, ?_⟩
  · rw [outputLaw_event_card] at hmain
    exact hmain.1
  · intro bits hbits
    have hmem : presampledOutcome solver n r (O false) (O true) p bits ∈
        (outputLaw solver n r (O false) (O true) p).support := by
      rw [outputLaw_presampled]
      rw [PMF.mem_support_map_iff]
      exact ⟨bits,
        (Analysis.SingleRunAccuracy.fairTape_support_iff_length _ _).mpr hbits, rfl⟩
    obtain ⟨hpos, hcalls, hsteps⟩ := hmain.2.2 _ hmem
    refine ⟨hpos, ?_, hcalls.trans (hdom Cs ds (by dsimp [A]; omega) (le_max_left _ _)),
      hsteps.trans (hdom Cs ds (by dsimp [A]; omega) (le_max_left _ _))⟩
    intro hz
    exact hmain.2.1 (by simp [hz]) _ hmem
