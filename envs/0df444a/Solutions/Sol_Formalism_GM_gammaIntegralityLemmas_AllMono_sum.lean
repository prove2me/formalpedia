-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.AllMono.sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:09.099607+00:00
-- url     : https://prove2.me/submissions/024fef10-8e45-4be9-94f5-e2c9beee0557

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_zero
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_zero

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
theorem _root_.solution {ι : Type} (s : Finset ι) {d : M} (P : ι → MvPolynomial σ ℚ_[p])
    (h : ∀ i ∈ s, AllMono Q d (P i)) : AllMono Q d (∑ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using AllMono.zero Q d
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact (h a (mem_insert_self _ _)).add Q (ih (fun i hi => h i (mem_insert_of_mem hi)))
end AllMono
end Formalism.GM.gammaIntegralityLemmas
