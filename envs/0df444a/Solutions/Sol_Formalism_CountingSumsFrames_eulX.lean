-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eulX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:31.368273+00:00
-- url     : https://prove2.me/submissions/66ea1af5-e130-4d65-a12e-3ce1181c034d

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_GM_ProjS_eulL_of_support


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
theorem _root_.solution {σ : Type} {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c : Fin s) :
    ProjS.eulL t (X (t c) : MvPolynomial σ ℚ_[p]) = X (t c) := by
  classical
  rw [ProjS.eulL_of_support t 1 (X (t c)) ?_, Nat.cast_one, one_smul]
  intro m hm
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; rw [Finsupp.single_apply, if_neg (fun h => hb (ht h).symm)]
  · simp
end Formalism.CountingSumsFrames
