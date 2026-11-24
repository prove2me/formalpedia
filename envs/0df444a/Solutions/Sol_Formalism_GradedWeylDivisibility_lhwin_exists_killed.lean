-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lhwin_exists_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:51:11.678802+00:00
-- url     : https://prove2.me/submissions/ed32968b-fa0c-4d9a-b2ab-d9b84bc8f10c

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwinLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_rowDiv_shift
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_weight_ht
import Theorems.Thm_Formalism_GradedWeylDivisibility_lhwin_nonneg

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
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h2 : RowDivClosedGraded) {r n : ℕ}
    (M : Submodule ℚ (MvPolynomial (Fin r × Fin n) ℚ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℚ a b k v = 0 := by
  classical
  have hex : ∃ N : ℕ, ∃ v ∈ M, v ≠ 0 ∧ IsWeightedHomogeneous (lhwinHt r n) v (N : ℤ) := by
    obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨d, hd⟩ := ne_zero_iff.mp hf0
    refine ⟨∑ a : Fin r, a.val * Finsupp.weight (rowW r n) d a,
      weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) d) f,
      h2 r n M hM f hfM _, ?_, ?_⟩
    · intro h
      apply hd
      have := congrArg (coeff d) h
      rwa [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    · intro e he
      rw [coeff_weightedHomogeneousComponent] at he
      split_ifs at he with hμ
      · rw [lhwin_weight_ht, hμ]; push_cast; rfl
      · exact absurd rfl he
  obtain ⟨v, hvM, hv0, hvH⟩ := Nat.find_spec hex
  refine ⟨v, hvM, hv0, fun a b hab k hk => ?_⟩
  by_contra hne'
  have hH := lhwin_rowDiv_shift ℚ _ a b k v hvH
  have hnn := lhwin_nonneg hne' hH
  have hab' : (a.val : ℤ) < b.val := by exact_mod_cast (Fin.lt_def.mp hab)
  have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
  have hlt : ((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val) < (Nat.find hex : ℕ) := by
    nlinarith
  have hmin := Nat.find_min hex (m := (((Nat.find hex : ℕ) : ℤ) + k * ((a.val : ℤ) - b.val)).toNat)
    (by omega)
  apply hmin
  refine ⟨_, hM a b k v hvM, hne', ?_⟩
  rw [Int.toNat_of_nonneg hnn]
  exact hH
end Formalism.GradedWeylDivisibility
