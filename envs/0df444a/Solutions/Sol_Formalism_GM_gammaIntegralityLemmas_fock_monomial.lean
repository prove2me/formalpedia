-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:02.276288+00:00
-- url     : https://prove2.me/submissions/002f3f5b-57cd-4631-a505-467c67093e14

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_eq_sum

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
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (α α' : σ →₀ ℕ) (c c' : ℚ_[p]) :
    Formalism.GM.M.fock p (monomial α c) (monomial α' c') = if α = α' then c * c' * wf α else 0 := by
  rw [fock_eq_sum _ _ {α} support_monomial_subset, Finset.sum_singleton, coeff_monomial, coeff_monomial]
  by_cases h : α = α'
  · subst h; simp
  · simp [h, Ne.symm h]
end Formalism.GM.gammaIntegralityLemmas
