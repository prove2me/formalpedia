-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.lemmaD_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:47.843404+00:00
-- url     : https://prove2.me/submissions/a9a11c49-048c-446a-a2e4-d3f03fc68635

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnNeZero
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeIffKilled
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_mem
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_unique
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_sym_Dn
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
theorem _root_.solution : LemmaD_sym := by
  intro l q w hl eL _ i μ hd
  rw [expLeIffKilled l _ _ μ eL _ hl (dnNeZero 1 w i q _)]
  intro x hx
  refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
  by_cases hne : x = 0
  · rw [hne, smul_zero]
    exact Submodule.zero_mem _
  obtain ⟨hsum, c, rfl⟩ := ld_sym_unique q w μ x hx hne
  have hd' : μ (ldZ q) + i = w := by
    have := hd
    simp only [IsDepth, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul] at this
    exact this
  have hsplit : μ (ldZ q) + ∑ a ∈ Finset.univ.erase (ldZ q), μ a = w := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ _)]
    exact hsum
  have hSi : ∑ a ∈ Finset.univ.erase (ldZ q), μ a = i := by omega
  obtain ⟨c', hc', hmem⟩ := ld_sym_mem q w μ (Finset.univ.erase (ldZ q)) (Finset.notMem_erase _ _) (by omega)
  have hv : ldSv q w μ (Finset.univ.erase (ldZ q)) = ∏ a, X (a, ldZ q) ^ μ a := by
    unfold ldSv
    rw [hSi, ← Finset.mul_prod_erase _ _ (Finset.mem_univ (ldZ q))]
    have : w - i = μ (ldZ q) := by omega
    rw [this]
  rw [hv] at hmem
  rw [hSi] at hc'
  have hdvd : ((c' : ℕ) : ℤ) ∣ Dn 1 w i (fun _ : Fin q => 0) := by
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq
      have hi0 : i = 0 := by
        rw [← hSi]
        refine Finset.sum_eq_zero fun a ha => ?_
        have hlt := a.isLt
        exact absurd (Fin.ext (show a.val = (ldZ 0).val from by have h0 : (ldZ 0).val = 0 := rfl; omega)) (Finset.ne_of_mem_erase ha)
      subst hi0
      have : c' = 1 := by simpa using hc'
      rw [this]
      simp
    · exact dvd_trans (Int.natCast_dvd_natCast.mpr hc') (ld_sym_Dn q w i hq (by omega))
  obtain ⟨e, he⟩ := hdvd
  rw [smul_smul, he]
  have : (1 * ((l : ℤ) ^ eL * ((c' : ℤ) * e)) * c) = ((l : ℤ) ^ eL * e * c) * (c' : ℤ) := by ring
  rw [this, mul_smul]
  exact Submodule.smul_mem _ _ hmem
end Formalism.CohomologicalDescent.LD
