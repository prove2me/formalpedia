-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux8.CkOn_pi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:42:19.935812+00:00
-- url     : https://prove2.me/submissions/455e3282-cd14-4cb7-924d-2bf4b5971052

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux8
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.Ux8
theorem _root_.solution {m : ℕ∞} {F : B.Mat k r → ι → E} (h : ∀ i, B.CkOn m (B.GV k r) (fun g => F g i)) :
    B.CkOn m (B.GV k r) F := by
  intro g₀ hg₀
  choose U f' hU hgU hcd heq using fun i => h i g₀ hg₀
  refine ⟨⋂ i, U i, fun g i => f' i g, isOpen_iInter_of_finite hU, Set.mem_iInter.2 hgU, ?_, ?_⟩
  · exact contDiffOn_pi.2 fun i => (hcd i).mono (Set.iInter_subset _ i)
  · intro g hg hgV
    funext i
    exact heq i g (Set.mem_iInter.1 hg i) hgV
end Formalism.FourierDecayAlt.P.Ux8
