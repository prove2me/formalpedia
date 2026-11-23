-- Prove2me | solution 1 for Formalism.L2.S.L6.UnitaryStandardVectors.lastDiag_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:08.757236+00:00
-- url     : https://prove2.me/submissions/c351938c-a6f7-454a-9133-46cf12aaf6e6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ZeroOfBlk
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LastDiagMulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.L6 Formalism.L2.S.L6.UnitaryStandardVectors
variable {r : ℕ}
namespace Formalism.L2.S.L6.UnitaryStandardVectors
theorem _root_.solution (t : ℂ) (α : Fin (r + 1) → ℂ) :
    lastDiag t *ᵥ α = Pi.single (Fin.last r) (t * α (Fin.last r)) := by
  ext i
  by_cases hi : i = Fin.last r
  · subst hi
    simp [lastDiag, Matrix.mulVec, dotProduct]
  · simp [lastDiag, Matrix.mulVec, dotProduct, hi]
end Formalism.L2.S.L6.UnitaryStandardVectors
