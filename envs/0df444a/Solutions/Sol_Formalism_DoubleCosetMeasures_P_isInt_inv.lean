-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isInt_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:18.329917+00:00
-- url     : https://prove2.me/submissions/833d9649-c348-448e-a187-fd6e86c678d0

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_adjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution {A : Matrix (Fin n) (Fin n) K} (hA : IsInt R A) (hd : A.det = 1) :
    IsInt R A⁻¹ := by
  rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
  exact isInt_adjugate R hA
end Formalism.DoubleCosetMeasures.P
