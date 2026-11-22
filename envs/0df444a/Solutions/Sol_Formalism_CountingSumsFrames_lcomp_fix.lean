-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:49.962802+00:00
-- url     : https://prove2.me/submissions/80e9e604-b268-46f8-b0c8-128da112816b

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_lcomp_cons

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
namespace Formalism.CountingSumsFrames
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι] (P : ι → V →ₗ[K] V)
    (hPP : ∀ j x, P j (P j x) = P j x) (hcomm : ∀ j j' x, P j (P j' x) = P j' (P j x)) :
    ∀ l : List ι, ∀ j ∈ l, ∀ u, P j (lcomp P l u) = lcomp P l u
  | [], j, hj, _ => by simp at hj
  | a :: l, j, hj, u => by
    rw [lcomp_cons, LinearMap.comp_apply]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact hPP j _
    · rw [hcomm j a, solution P hPP hcomm l j hj' u]
end Formalism.CountingSumsFrames
