-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.lieL_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:39:31.253641+00:00
-- url     : https://prove2.me/submissions/37072dc6-073f-48f6-9b79-ed0473772ba7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} {X Y : Mx k r} (hX : X ∈ LieL k r i) (hY : Y ∈ LieL k r i) :
    X - Y ∈ LieL k r i := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  have a1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX1
  have b1 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X - Y)ᴴ * Hpk k r + Hpk k r * (X - Y) = 0
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) - (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [a1, b1, sub_zero]
  · obtain ⟨x1, x2⟩ := hX2 a ha
    obtain ⟨y1, y2⟩ := hY2 a ha
    exact ⟨by rw [Matrix.sub_mulVec, x1, y1, sub_zero], by rw [Matrix.sub_mulVec, x2, y2, sub_zero]⟩
end Formalism.FourierDecayAlt.Q.EabGlW
