-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G3.twistSub_X_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:58:18.537178+00:00
-- url     : https://prove2.me/submissions/3cf79767-ba19-491e-8c01-a8b9a6390ba2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_TwistSubXMemSupported
import Theorems.Thm_P2M_Formalism_MainNotions_TestSideWords_TwistedFiltration_G3_X_mem_supported__ad5886e30d80

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
open Classical
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
theorem _root_.solution (w : Set ι) (j : Fin n) (v : ι × Fin n) (hv : v.1 ∉ w) :
    twistSub (R := R) LL S j (X v) ∈ supported (GLLaurent R n) {x : ι × Fin n | x.1 ∉ w} := by
  unfold twistSub
  rw [eval₂Hom_X']
  split_ifs
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (X_mem_supported' w _ hv)
  · exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (X_mem_supported' w _ hv)
  · exact X_mem_supported' w _ hv
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G3
