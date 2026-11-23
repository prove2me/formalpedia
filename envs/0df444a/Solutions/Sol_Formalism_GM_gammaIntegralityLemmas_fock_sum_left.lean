-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:02.529383+00:00
-- url     : https://prove2.me/submissions/82b486fb-b822-4682-8436-99e212cebbef

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_add_left
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_zero_left

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
theorem _root_.solution {ι : Type} (t : Finset ι) (F : ι → MvPolynomial σ ℚ_[p]) (G : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.M.fock p (∑ i ∈ t, F i) G = ∑ i ∈ t, Formalism.GM.M.fock p (F i) G := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]
end Formalism.GM.gammaIntegralityLemmas
