-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.initial_minor_degree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:08:36.190259+00:00
-- url     : https://prove2.me/submissions/2e59d3c6-8365-4ee1-9a07-d324cf491a85

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_add
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_single
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDeg_zero
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_support_prod_eq_of_additive
import Theorems.Thm_P2M_Formalism_GradedWeylDivisibility_support_X_subset__c6434ddb5fe3
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {r s : ℕ} (I : Fin s → Fin r) (hs : s ≤ r) (a : Fin r)
    (m : Fin r × Fin r →₀ ℕ) (hm : m ∈ (initMinor ℤ I hs).support) :
    rowDeg m a ≤ if 0 < s then 1 else 0 := by
  classical
  by_cases hI : Function.Injective I
  · unfold initMinor at hm
    rw [Matrix.det_apply] at hm
    have h1 := support_sum hm
    rw [Finset.mem_biUnion] at h1
    obtain ⟨σ, -, hσ⟩ := h1
    rw [Units.smul_def] at hσ
    have hσ' := support_smul hσ
    simp only [Matrix.of_apply] at hσ'
    have h := support_prod_eq_of_additive (fun m => rowDeg m a) (rowDeg_zero a)
      (fun x y => rowDeg_add x y a) Finset.univ
      (fun i : Fin s => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin r) ℤ))
      (fun i => if I (σ i) = a then 1 else 0)
      (by
        intro i _ m' hm'
        have := support_X_subset' (R := ℤ) _ hm'
        rw [Finset.mem_singleton] at this
        subst this
        exact rowDeg_single _ _ _) m hσ'
    rw [h, Equiv.sum_comp σ (fun p => if I p = a then 1 else 0), Finset.sum_boole]
    have hc : (Finset.univ.filter fun p => I p = a).card ≤ 1 := Finset.card_le_one.mpr (by
      intro p hp q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
      exact hI (hp.trans hq.symm))
    split_ifs with h0
    · simpa using hc
    · have : s = 0 := by omega
      subst this
      simp
  · exfalso
    simp only [Function.Injective, not_forall] at hI
    obtain ⟨p, q, hpq, hne⟩ := hI
    have h0 : initMinor ℤ I hs = 0 := by
      unfold initMinor
      apply Matrix.det_zero_of_row_eq hne
      funext j
      simp [hpq]
    rw [h0, support_zero] at hm
    exact Finset.notMem_empty _ hm
end Formalism.CohomologicalDescent.LD
