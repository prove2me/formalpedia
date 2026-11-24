-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_sym_Dn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:40.589805+00:00
-- url     : https://prove2.me/submissions/b2e591e3-b6c8-4357-929e-deb097d9fdf4

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_mu
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution (q w i : ℕ) (hq : 0 < q) (hi : i ≤ w) :
    ((w.descFactorial i : ℕ) : ℤ) ∣ Dn 1 w i (fun _ : Fin q => 0) := by
  unfold Dn
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hsub : (Finset.range i).image (fun c => c + q) ⊆ Finset.range (q + w + i) := by
    intro k hk
    simp only [Finset.mem_image, Finset.mem_range] at hk ⊢
    omega
  refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  rw [Finset.prod_image (by intro a _ b _ hab; simpa using hab)]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun c hc => ?_
  rw [Finset.mem_range] at hc
  have e : ((c + q : ℕ) : ℤ) - (q : ℤ) = (c : ℤ) := by push_cast; ring
  simp only [e]
  have hmu := ld_sym_mu q w i hq hi (c : ℤ) (by positivity) (by exact_mod_cast hc)
  have hc' : ((w - c : ℕ) : ℤ) = (w : ℤ) - (c : ℤ) := by rw [Nat.cast_sub (by omega)]
  rw [hc']
  exact dvd_pow_self _ hmu
end Formalism.CohomologicalDescent.LD
