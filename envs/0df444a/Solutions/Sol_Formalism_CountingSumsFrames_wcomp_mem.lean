-- Prove2me | solution 1 for Formalism.CountingSumsFrames.wcomp_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:56:21.911797+00:00
-- url     : https://prove2.me/submissions/244b6a5b-423f-412f-ab96-76bba59f9beb

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_CountingSumsFrames_compP_and
import Theorems.Thm_Formalism_CountingSumsFrames_compP_true
import Theorems.Thm_Formalism_CountingSumsFrames_compP_congr
import Theorems.Thm_Formalism_CountingSumsFrames_vdm

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ c, ∀ x ∈ S, glAct p LL j c c x ∈ S) (μ : Fin r → ℤ) :
    ∀ x ∈ S, compP (fun m => ∀ c, wt LL j c m = μ c) x ∈ S := by
  have key : ∀ s : Finset (Fin r), ∀ x ∈ S, compP (fun m => ∀ c ∈ s, wt LL j c m = μ c) x ∈ S := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x hx
      rw [compP_congr (fun m => ∀ c ∈ (∅ : Finset (Fin r)), wt LL j c m = μ c) (fun _ => True)
        (fun m => by simp), compP_true]
      exact hx
    | @insert a s ha ih =>
      intro x hx
      rw [compP_congr (fun m => ∀ c ∈ insert a s, wt LL j c m = μ c)
        (fun m => wt LL j a m = μ a ∧ ∀ c ∈ s, wt LL j c m = μ c) (fun m => by simp), compP_and]
      exact vdm (glAct p LL j a a) (wt LL j a) (fun y m => coeff_cartan LL j a y m) S (hS a) _ (ih x hx) (μ a)
  intro x hx
  rw [compP_congr (fun m => ∀ c, wt LL j c m = μ c) (fun m => ∀ c ∈ (Finset.univ : Finset (Fin r)), wt LL j c m = μ c)
    (fun m => by simp)]
  exact key Finset.univ x hx
end Formalism.CountingSumsFrames
