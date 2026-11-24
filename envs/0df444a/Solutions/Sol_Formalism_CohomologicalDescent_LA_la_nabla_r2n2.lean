-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_nabla_r2n2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:28.794863+00:00
-- url     : https://prove2.me/submissions/688e70e5-971c-4d7e-bebe-3b7babfb13de

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_weyl_r2n2
import Theorems.Thm_Formalism_CohomologicalDescent_LA_prod_initial_minors_mem_det_span
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylSat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_weylLeDual
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
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution (hn : 2 ≤ 2) (ν : Fin 2 → ℕ) (hν : Antitone ν) :
    dualWeyl ℤ 2 2 ν = detPowMulMonomialSpan (ν 1) (ν 0 - ν 1) := by
  apply le_antisymm
  · rw [standardMonomialSpan 2 2 ν hν]
    apply Submodule.span_le.2
    rintro _ ⟨K, sz, hsz, I, hshape, rfl⟩
    have h1 := prod_initial_minors_mem_det_span sz hsz I Finset.univ
    have c1 : (∑ k : Fin K, if sz k = 2 then 1 else 0) = ν 1 := by
      rw [← hshape]
      unfold shapeDeg
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro k _
      have := hsz k
      have e : ((1 : Fin 2).val < sz k) ↔ sz k = 2 := by
        simp only [Fin.val_one]
        omega
      simp only [e]
    have c0 : (∑ k : Fin K, if sz k = 1 then 1 else 0) + (∑ k : Fin K, if sz k = 2 then 1 else 0)
        = ν 0 := by
      rw [← hshape]
      unfold shapeDeg
      rw [Finset.card_filter, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have := hsz k
      simp only [Fin.val_zero]
      split_ifs <;> omega
    have c2 : (∑ k : Fin K, if sz k = 1 then 1 else 0) = ν 0 - ν 1 := by omega
    rw [c1, c2] at h1
    exact h1
  · unfold detPowMulMonomialSpan
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.2
    rintro _ ⟨p, q, h, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    apply dualWeylSat ℤ 2 2 ν (((p + q).choose q : ℕ) : ℤ) _
      (by exact_mod_cast (Nat.choose_pos (by omega)).ne')
    apply weylLeDual ℤ 2 2 hn ν hν
    rw [la_weyl_r2n2]
    refine ⟨_, Submodule.subset_span ⟨p, q, h, rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [MvPolynomial.smul_eq_C_mul, map_natCast]
    ring
end Formalism.CohomologicalDescent.LA
