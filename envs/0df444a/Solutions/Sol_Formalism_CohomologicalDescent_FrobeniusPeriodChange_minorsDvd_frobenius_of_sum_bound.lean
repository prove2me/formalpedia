-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.minorsDvd_frobenius_of_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:03:35.952792+00:00
-- url     : https://prove2.me/submissions/fe9bcade-6352-4175-87ef-f87927d8596c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_base_change_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_natCast_prime_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minor_reduction_holds
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_divide_all_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (U' : ι → Fin n → ℤ)
    (hN : LatW l W.N h u U') (i : ι) (r S : ℕ)
    (hS : ∀ J : Finset (Fin n), J.card = r → (S : ℤ) ≤ ∑ j ∈ J, U' i j) :
    MinorsDvd ((X : F⟦X⟧) ^ S) r (W.Phi l σ i) := by
  have h2 := (minors_divide_all_holds (O⟦X⟧) n n r _ _).1 (hN.2.1 i r S hS)
  apply (frobenius_base_change_holds F n l h _ _ _ (Fact.out : l.Prime).pos).2
  intro f g _ _
  exact (minor_reduction_holds O F W.red (l : O) n r S (W.N.P i) f g (reduction_natCast_prime_eq_zero l W.red)).2 (h2 f g)
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
