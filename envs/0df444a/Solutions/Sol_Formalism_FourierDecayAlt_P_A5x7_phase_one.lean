-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x7.phase_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:04.342805+00:00
-- url     : https://prove2.me/submissions/ecd4d4a6-a5b8-4142-91b3-11857e96010d

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsIntOfLatOfLe
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsOpenIsIntSet
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_mem_intSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x7
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x7
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (w : Point K)
    (p : lowW K w.1 w.2 × upUniG K w.1.sum)
    (h1 : p.1 ∈ intSub R (lowW K w.1 w.2)) (h2 : p.2 ∈ intSub R (upUniG K w.1.sum)) :
    phase ψ p = 1 := by
  have hV := ((mem_intSub R _ p.1).1 h1).1
  have hU := ((mem_intSub R _ p.2).1 h2).1
  unfold phase
  apply hψ
  refine R.add_mem ?_ ?_
  · unfold sLow
    refine Subring.sum_mem _ (fun j _ => ?_)
    split_ifs
    · exact hV _ _
    · exact R.zero_mem
  · unfold sUp
    refine Subring.sum_mem _ (fun j _ => ?_)
    split_ifs
    · exact hU _ _
    · exact R.zero_mem
end Formalism.FourierDecayAlt.P.A5x7
