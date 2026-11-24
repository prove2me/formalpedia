-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.peelBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:30:35.993302+00:00
-- url     : https://prove2.me/submissions/d0a820e7-b0ca-43ea-aab9-9090f623aa74

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_expLeMono
import Theorems.Thm_Formalism_CohomologicalDescent_LD_dnVal
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_blockWt_anti
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylDominanceZ
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldrow_weight_rowW
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
theorem _root_.solution : PeelBound := by
  intro hD l q w m lam2 hl ha hb eL heL μ
  have hbw : ∀ b, lam2 b ≤ w := fun b => (hb b).2
  have hl1 : 0 < l - 1 := by have := hl.two_le; omega
  by_cases hμ : μ (Fin.castAdd q (0 : Fin 1)) ≤ w
  · have hd : IsDepth 1 q w μ (w - μ (Fin.castAdd q (0 : Fin 1))) := by
      simp only [IsDepth, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton, one_mul]
      omega
    have h1 := hD l q w lam2 hl ha hbw eL heL _ μ hd
    refine expLeMono l _ _ μ _ _ ?_ h1
    refine Nat.add_le_add_left ?_ eL
    refine (Nat.le_div_iff_mul_le hl1).mpr ?_
    have h2 := dnVal l 1 w (w - μ (Fin.castAdd q (0 : Fin 1))) q m lam2 hl hb
    rw [one_mul] at h2
    rw [mul_comm]
    exact h2
  · intro x hx
    have hx0 : x = 0 := by
      by_contra hne
      obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
      have hdom := (dualWeylDominanceZ (1 + q) (1 + q) (blockWt 1 q w lam2) le_rfl
        (ld_blockWt_anti 1 q w lam2 ha hbw) x hx.1 d hd).1 1
      have hf : (Finset.univ.filter fun a : Fin (1 + q) => a.val < 1) = {Fin.castAdd q (0 : Fin 1)} := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, Fin.ext_iff,
          Fin.val_castAdd, Fin.val_zero]
        omega
      rw [hf, Finset.sum_singleton, Finset.sum_singleton] at hdom
      have hwt : Finsupp.weight (rowW (1 + q) (1 + q)) d = μ := hx.2 (MvPolynomial.mem_support_iff.mp hd)
      rw [← ldrow_weight_rowW, hwt] at hdom
      have hnu : rowNu (r := 1 + q) (blockWt 1 q w lam2) (Fin.castAdd q (0 : Fin 1)) = w := by
        unfold rowNu
        rw [dif_pos (Fin.castAdd q (0 : Fin 1)).isLt]
        exact Fin.append_left _ _ 0
      rw [hnu] at hdom
      exact hμ hdom
    refine ⟨1, (Nat.prime_iff_prime_int.mp hl).not_dvd_one, ?_⟩
    rw [hx0, smul_zero]
    exact Submodule.zero_mem _
end Formalism.CohomologicalDescent.LD
