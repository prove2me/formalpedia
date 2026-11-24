-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.levPos_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:29:33.957389+00:00
-- url     : https://prove2.me/submissions/c04db7d9-fb76-401f-879f-c5db9597466c

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro a b h
  have h' : a.val + 1 = b.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)
end Formalism.FourierDecayAlt.P.LongWeylElement
