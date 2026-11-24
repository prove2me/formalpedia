-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.colLexInitMinor_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:52.190038+00:00
-- url     : https://prove2.me/submissions/a500f55e-52e8-47e6-bcfd-e95a17d15bbb

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColLexInitMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcminor_initMinor_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
open scoped MonomialOrder
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h : MinorExpLt) : ColLexInitMinor := by
  intro R _ _ r n s I hs hI
  rw [lcminor_initMinor_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin s)))]
  simp only [Equiv.Perm.one_apply, Equiv.Perm.sign_one, Units.val_one, Int.cast_one]
  set g := ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin s)),
    monomial (∑ q : Fin s, Finsupp.single (I (σ q), Fin.castLE hs q) 1)
      (((Equiv.Perm.sign σ : ℤ) : R)) with hg_def
  set e := ∑ q : Fin s, Finsupp.single (I q, Fin.castLE hs q) 1 with he
  have hdf : (colLex r n).degree (monomial e (1 : R)) = e := by
    classical
    rw [MonomialOrder.degree_monomial]
    simp
  by_cases hg : g = 0
  · rw [hg, add_zero, hdf, MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
  · have hne : (Finset.univ.erase (1 : Equiv.Perm (Fin s))).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      apply hg
      rw [hg_def, h0, Finset.sum_empty]
    have hlt : (colLex r n).toSyn ((colLex r n).degree g) <
        (colLex r n).toSyn ((colLex r n).degree (monomial e (1 : R))) := by
      rw [hdf]
      refine lt_of_le_of_lt MonomialOrder.degree_sum_le ?_
      obtain ⟨σ0, hσ0⟩ := hne
      rw [Finset.sup_lt_iff (lt_of_le_of_lt bot_le (h r n s I hs hI σ0 (Finset.ne_of_mem_erase hσ0)))]
      intro σ hσ
      exact lt_of_le_of_lt (MonomialOrder.degree_monomial_le _) (h r n s I hs hI σ (Finset.ne_of_mem_erase hσ))
    rw [MonomialOrder.degree_add_of_lt hlt, MonomialOrder.leadingCoeff_add_of_lt hlt, hdf,
      MonomialOrder.leadingCoeff_monomial]
    exact ⟨rfl, rfl⟩
end Formalism.GradedWeylDivisibility
