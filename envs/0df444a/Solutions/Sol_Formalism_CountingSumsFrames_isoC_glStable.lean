-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isoC_glStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:35.447469+00:00
-- url     : https://prove2.me/submissions/3e3cc77e-15d3-426e-bf19-4e8a7d319edd

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (la : Fin r → ℤ) (c d : Fin r) :
    ∀ x ∈ IsoC p LL j univ la, glAct p LL j c d x ∈ IsoC p LL j univ la := by
  intro x hx
  unfold IsoC at hx ⊢
  rw [Submodule.mem_sInf] at hx ⊢
  intro S hS
  exact hS.2 c (Finset.mem_univ _) d (Finset.mem_univ _) x (hx S hS)
end Formalism.CountingSumsFrames
