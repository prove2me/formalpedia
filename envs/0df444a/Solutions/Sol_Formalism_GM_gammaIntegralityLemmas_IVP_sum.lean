-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.IVP.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:17.762344+00:00
-- url     : https://prove2.me/submissions/4b5b721a-fb1f-45d7-972f-1c6d31bad022

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset Polynomial
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
namespace IVP
theorem _root_.solution {ι : Type} {D : ℕ} (s : Finset ι) (g : ι → ℕ → ℚ_[p]) (h : ∀ i ∈ s, IVP p D (g i)) :
    IVP p D (fun m => ∑ i ∈ s, g i m) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IVP.zero (p := p) D
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact IVP.add (h a (mem_insert_self _ _)) (ih (fun i hi => h i (mem_insert_of_mem hi)))
end IVP
end Formalism.GM.gammaIntegralityLemmas
