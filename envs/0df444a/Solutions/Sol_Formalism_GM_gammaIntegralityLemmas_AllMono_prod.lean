-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:58.246795+00:00
-- url     : https://prove2.me/submissions/55167807-bdb0-4038-a637-0392f506abfe

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_mul
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [DecidableEq σ] {M : Type} [AddCommMonoid M]
variable (Q : M → (σ →₀ ℕ) → Prop)
namespace Formalism.GM.gammaIntegralityLemmas
namespace AllMono
theorem _root_.solution (hQ : ∀ d d' β β', Q d β → Q d' β' → Q (d + d') (β + β')) (hQ0 : Q 0 0)
    {ι : Type} (s : Finset ι) (d : ι → M) (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q (d i) (P i)) : AllMono Q (∑ i ∈ s, d i) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AllMono.one Q hQ0
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    exact (h a (mem_insert_self _ _)).mul Q hQ (ih (fun i hi => h i (mem_insert_of_mem hi)))
end AllMono
end Formalism.GM.gammaIntegralityLemmas
