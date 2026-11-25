-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.sImg_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:33.67396+00:00
-- url     : https://prove2.me/submissions/c70aa170-d61c-457a-9b9e-a028ccba3330

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg jc x (i, jc.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _ k
end Formalism.L2.Pj.LocAlg
