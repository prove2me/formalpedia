-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.sImg_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:32.306684+00:00
-- url     : https://prove2.me/submissions/1a350137-d0e7-4f9a-925d-bdcc8a219be8

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
theorem _root_.solution (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    sImg jc x (i, jc) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _
end Formalism.L2.Pj.LocAlg
