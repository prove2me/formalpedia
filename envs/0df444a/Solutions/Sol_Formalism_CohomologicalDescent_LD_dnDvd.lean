-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.dnDvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:10:11.767215+00:00
-- url     : https://prove2.me/submissions/5d3e54a0-844e-4142-bd9d-74b5f22679db

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_muLe
import Theorems.Thm_Formalism_CohomologicalDescent_LD_muRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution : DnDvd := by
  intro p w i q m lam2 hb
  unfold Dn
  have hfac : ∀ k ∈ Finset.range (q + w + i),
      ((w : ℤ) - ((k : ℤ) - (q : ℤ))) ^ mu p w i lam2 ((k : ℤ) - (q : ℤ)) ∣
        (((if k ∈ Finset.Ico (m + 1) (w + q) then (w + q - k) ^ p else 1 : ℕ)) : ℤ) := by
    intro k _
    by_cases hmu : mu p w i lam2 ((k : ℤ) - (q : ℤ)) = 0
    · rw [hmu, pow_zero]
      exact one_dvd _
    · have h := muRange p w i q m lam2 _ hb hmu
      have hk : k ∈ Finset.Ico (m + 1) (w + q) := Finset.mem_Ico.mpr (by omega)
      rw [if_pos hk]
      have he : ((w : ℤ) - ((k : ℤ) - (q : ℤ))) = ((w + q - k : ℕ) : ℤ) := by omega
      rw [he, Nat.cast_pow]
      exact pow_dvd_pow _ (muLe p w i q lam2 _)
  refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ hfac) ?_
  rw [← Nat.cast_prod, Finset.prod_ite_mem]
  have hsub : Finset.range (q + w + i) ∩ Finset.Ico (m + 1) (w + q) = Finset.Ico (m + 1) (w + q) := by
    refine Finset.inter_eq_right.mpr ?_
    intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact Finset.mem_range.mpr (by omega)
  rw [hsub, Finset.prod_pow, Finset.prod_Ico_eq_prod_range]
  have hH : w + q - (m + 1) = w + q - m - 1 := by omega
  have hprod : ∏ j ∈ Finset.range (w + q - (m + 1)), (w + q - (m + 1 + j)) = (w + q - m - 1).factorial := by
    rw [hH, ← Nat.descFactorial_self, Nat.descFactorial_eq_prod_range]
    refine Finset.prod_congr rfl ?_
    intro j _
    omega
  rw [hprod]
end Formalism.CohomologicalDescent.LD
