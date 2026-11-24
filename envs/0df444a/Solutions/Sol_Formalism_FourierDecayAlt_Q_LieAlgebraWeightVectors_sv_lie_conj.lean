-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_lie_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:45.943881+00:00
-- url     : https://prove2.me/submissions/f2a21b31-121a-4665-98e3-4f4984b28b16

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {X h₀ : Mx k r} (hX : inLieW k r z X)
    (hh₀ : h₀ ∈ UWset k r z) : inLieW k r z (h₀⁻¹ * X * h₀) := by
  have hu := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hi1 : h₀ * h₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hU : h₀ᴴ * Hpk k r * h₀ = Hpk k r := hh₀.1
  have A : (h₀⁻¹)ᴴ * Hpk k r = Hpk k r * h₀ := by
    calc (h₀⁻¹)ᴴ * Hpk k r = (h₀⁻¹)ᴴ * (h₀ᴴ * Hpk k r * h₀) := by rw [hU]
      _ = (h₀ * h₀⁻¹)ᴴ * Hpk k r * h₀ := by rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * h₀ := by rw [hi1, conjTranspose_one, Matrix.one_mul]
  have B : Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r := by
    calc Hpk k r * h₀⁻¹ = h₀ᴴ * Hpk k r * h₀ * h₀⁻¹ := by rw [hU]
      _ = h₀ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hi1, Matrix.mul_one]
  refine ⟨?_, ?_, fun a => ⟨?_, ?_⟩⟩
  · calc (h₀⁻¹ * X * h₀)ᴴ * Hpk k r + Hpk k r * (h₀⁻¹ * X * h₀)
        = h₀ᴴ * (Xᴴ * ((h₀⁻¹)ᴴ * Hpk k r)) + (Hpk k r * h₀⁻¹) * X * h₀ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = h₀ᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * h₀ := by
          rw [A, B]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 0 := by rw [hX.1]; simp
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh₀.2.2, hX.2.1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).1, (hX.2.2 a).1, Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hh₀.2.1 a).2, (hX.2.2 a).2, Matrix.mulVec_zero]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
