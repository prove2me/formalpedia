-- Prove2me | solution 1 for Formalism.FG.InjVAux.good_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:11.505287+00:00
-- url     : https://prove2.me/submissions/b3eeedfc-e6db-4320-8b8a-2295caad0377

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_mul
import Theorems.Thm_Formalism_FG_InjVAux_good_one
import Theorems.Thm_Formalism_FG_InjVAux_Good_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG
open Formalism.FG.InjVAux
open MvPowerSeries
variable {R : Type*} [CommRing R] {τ : Type*}
namespace Formalism.FG.InjVAux
theorem _root_.solution {N : ℕ} {ι : Type*} (s : Finset ι) (k : ι → ℕ)
    (x x' : ι → MvPowerSeries τ R) (h : ∀ i ∈ s, Good N (k i) (x i) (x' i)) :
    Good N (∑ i ∈ s, k i) (∏ i ∈ s, x i) (∏ i ∈ s, x' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one N
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
end Formalism.FG.InjVAux
