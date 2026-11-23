-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.dg_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:56.65263+00:00
-- url     : https://prove2.me/submissions/a71583ae-4a3b-495c-ae57-13d88578e5e3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_blk_last_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (l : List ℕ) (s : ℕ) (k : Kˣ) (j : Fin (l ++ [s]).sum) (hj : l.sum ≤ j.val) :
    dg (l ++ [s]) (Function.update (1 : ℕ → Kˣ) l.length k) j = k := by
  unfold dg
  rw [(blk_last_iff l s j j.2).2 hj, Function.update_self]
end Formalism.FourierDecayAlt.P.KernelScalingBack
