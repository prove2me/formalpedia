-- Prove2me | solution 1 for Formalism.CountingSumsFrames.intPol_torsionFree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:51:52.613879+00:00
-- url     : https://prove2.me/submissions/d12594cd-d11f-4889-99e2-a972c468f5a2

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
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) : Module.IsTorsionFree ℤ_[p] L :=
  Module.IsTorsionFree.of_smul_eq_zero fun a x h => by
    by_cases ha : a = 0
    · exact Or.inl ha
    · right
      apply Subtype.ext
      have h' : (a • (x : MvPolynomial σ ℚ_[p])) = 0 := by
        have := congrArg Subtype.val h
        simpa using this
      rw [← algebraMap_smul ℚ_[p] a (x : MvPolynomial σ ℚ_[p]), smul_eq_zero] at h'
      rcases h' with h' | h'
      · exact absurd (PadicInt.ext (h'.trans PadicInt.coe_zero.symm)) ha
      · simpa using h'
end Formalism.CountingSumsFrames
