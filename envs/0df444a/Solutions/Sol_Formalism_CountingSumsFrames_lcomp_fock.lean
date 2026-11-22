-- Prove2me | solution 1 for Formalism.CountingSumsFrames.lcomp_fock
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:27:15.413323+00:00
-- url     : https://prove2.me/submissions/5e8fb247-b216-432c-8e19-823c701dd99c

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
theorem _root_.solution {p : ℕ} [Fact p.Prime] {σ : Type} {ι : Type*} [LinearOrder ι]
    (P : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hsa : ∀ j F G, fock p (P j F) G = fock p F (P j G)) (z : MvPolynomial σ ℚ_[p]) (hz : ∀ j, P j z = z) :
    ∀ l : List ι, ∀ u, fock p z (lcomp P l u) = fock p z u
  | [], u => rfl
  | a :: l, u => by
    rw [lcomp_cons, LinearMap.comp_apply, ← hsa a z, hz a, solution P hsa z hz l u]
end Formalism.CountingSumsFrames
