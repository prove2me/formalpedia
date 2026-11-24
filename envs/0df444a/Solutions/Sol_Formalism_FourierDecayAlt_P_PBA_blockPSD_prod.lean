-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.blockPSD_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:59:42.674826+00:00
-- url     : https://prove2.me/submissions/96066416-3297-40ed-88fb-7c2238b2307c

import Definitions.Def_Formalism_HermitianCurvature_StatementKB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockOfCauchySchwarz
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBA_blockPSD_ones

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {α β ι : Type} {Y₁ : Finset α} {Y₂ : Finset β} (s : Finset ι) (a : ι → α → α → ℂ)
    (w : ι → α → β → ℂ) (b : ι → β → β → ℂ) (h : ∀ v ∈ s, KB.BlockPSD Y₁ Y₂ (a v) (w v) (b v)) :
    KB.BlockPSD Y₁ Y₂ (fun p q => ∏ v ∈ s, a v p q) (fun p q => ∏ v ∈ s, w v p q)
      (fun p q => ∏ v ∈ s, b v p q) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using blockPSD_ones Y₁ Y₂
  · intro v t hv ih h
    simp only [Finset.prod_insert hv]
    exact blockPSD_mul (h v (Finset.mem_insert_self v t)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))
end Formalism.FourierDecayAlt.P.PBA
