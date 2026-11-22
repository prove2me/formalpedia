-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_keep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:49.991804+00:00
-- url     : https://prove2.me/submissions/e63b68e9-d318-4211-9533-4b07c46f4613

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
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [LinearOrder ι]
namespace Formalism.CountingSumsFrames
theorem _root_.solution (φ : ι → V →ₗ[K] V) (C : Set V) :
    ∀ l : List ι, (∀ j ∈ l, ∀ u ∈ C, φ j u ∈ C) → ∀ u ∈ C, lcomp φ l u ∈ C
  | [], _, u, hu => hu
  | i :: l, h, u, hu => by
    rw [lcomp_cons, LinearMap.comp_apply]
    exact h i List.mem_cons_self _ (solution φ C l (fun j hj => h j (List.mem_cons_of_mem _ hj)) u hu)
end Formalism.CountingSumsFrames
