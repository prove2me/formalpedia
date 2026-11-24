-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.lieL_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:57.35328+00:00
-- url     : https://prove2.me/submissions/63dca381-7ae5-47f3-bdb1-193600444d7e

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
    X + Y ∈ LieL k r i := by
  obtain ⟨hX1, hX2⟩ := hX
  obtain ⟨hY1, hY2⟩ := hY
  have a1 : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX1
  have b1 : Yᴴ * Hpk k r + Hpk k r * Y = 0 := hY1
  refine ⟨?_, fun a ha => ?_⟩
  · show (X + Y)ᴴ * Hpk k r + Hpk k r * (X + Y) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [a1, b1, add_zero]
  · obtain ⟨x1, x2⟩ := hX2 a ha
    obtain ⟨y1, y2⟩ := hY2 a ha
    exact ⟨by rw [Matrix.add_mulVec, x1, y1, add_zero], by rw [Matrix.add_mulVec, x2, y2, add_zero]⟩
end Formalism.FourierDecayAlt.Q.EabGlW
