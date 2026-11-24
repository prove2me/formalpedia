-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.compactHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:21:28.241795+00:00
-- url     : https://prove2.me/submissions/ae4ffb9b-2904-4dcd-a7bf-b943be8fc128

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_push
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_haar_ne_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Grp_range_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_compact_right_inv

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
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution : CompactHaarExists := by
  intro k r U h hc
  have : CompactSpace (Grp U h) := isCompact_iff_compactSpace.mp hc
  have : (Measure.haar : Measure (Grp U h)).IsMulRightInvariant := compact_right_inv _
  refine ⟨(Measure.haar : Measure (Grp U h)).map (Grp.val : Grp U h → Mt k r), ?_⟩
  exact haar_push _ (haar_ne_zero _) _ Grp.emb (fun a b => rfl) U Grp.range_val
end Formalism.FourierDecayAlt.P.B2x3
