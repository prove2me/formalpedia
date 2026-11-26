-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_collatzThreeBlockFairBinMass_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:59:59.761299+00:00
-- url     : https://prove2.me/submissions/cb5f44fd-a4f6-4369-86e1-8506360eb4ed

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_exists_collatzThreeBlockEnvelopeMass_le
import Theorems.Thm_FirstPassageLinearTransport_collatzThreeBlockFlatMass_tilt_eq
import Theorems.Thm_FirstPassageLinearTransport_collatzThreeBlockFlatMass_fair_le_tilt

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℕ, ∀ B q : ℝ,
        0 < a → 0 < b → 0 ≤ B → 0 ≤ q →
          collatzThreeBlockFlatMass (1 / 2) a b B q ≤
            C * (B + 1) * (q + 2) /
                (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
              Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
                collatzTiltLambda * (q - B)) := by
  obtain ⟨C, hC, hEnvelope⟩ := exists_collatzThreeBlockEnvelopeMass_le
  refine ⟨C, hC, ?_⟩
  intro a b B q ha hb hB hq
  have htilt := hEnvelope a b B q (q - B) ha hb hB hq
  calc
    collatzThreeBlockFlatMass (1 / 2) a b B q ≤
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          collatzThreeBlockFlatMass collatzTilt a b B q :=
      collatzThreeBlockFlatMass_fair_le_tilt
    _ = Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          collatzThreeBlockEnvelopeMass a b B q (q - B) := by
      rw [collatzThreeBlockFlatMass_tilt_eq]
    _ ≤ Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) *
          (C * (B + 1) * (q + 2) /
            (Real.sqrt a * Real.sqrt a * Real.sqrt b)) :=
      mul_le_mul_of_nonneg_left htilt (Real.exp_pos _).le
    _ = C * (B + 1) * (q + 2) /
          (Real.sqrt a * Real.sqrt a * Real.sqrt b) *
        Real.exp (-(collatzFairTiltRate * ((2 * a + b : ℕ) : ℝ)) -
          collatzTiltLambda * (q - B)) := by ring
end FirstPassageLinearTransport
