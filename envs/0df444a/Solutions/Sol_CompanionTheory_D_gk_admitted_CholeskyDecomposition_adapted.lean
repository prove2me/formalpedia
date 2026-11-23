-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.CholeskyDecomposition.adapted
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:42.355884+00:00
-- url     : https://prove2.me/submissions/be48de03-cc16-4cae-bb59-610b77414636

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaAll
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_pr_pr
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_rev_cast
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_ht_eq_zero
import Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_lt_of_sign
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open Matrix PI.UpqRep
open CompanionTheory.D.gk.admitted.CholeskyDecomposition
variable {n : ℕ}
namespace CompanionTheory.D.gk.admitted.CholeskyDecomposition
theorem _root_.solution {ε : Fin n → Bool} (hε : Monotone ε) : Adapted (pr ε) (ht ε) (wt ε) := by
  have hpos : ∀ i : Fin n, ε i = true → ε i.rev = false → 0 < 2 * (i : ℤ) + 1 - n := by
    intro i h1 h2
    have h3 := lt_of_sign hε h2 h1
    rw [rev_cast] at h3
    linarith
  have hneg : ∀ i : Fin n, ε i = false → ε i.rev = true → 2 * (i : ℤ) + 1 - n < 0 := by
    intro i h1 h2
    have h3 := lt_of_sign hε h1 h2
    rw [rev_cast] at h3
    linarith
  refine ⟨pr_pr ε, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 : ε i ≤ ε j := hε hij
    have h2 : ε j.rev ≤ ε i.rev := hε (Fin.rev_le_rev.mpr hij)
    have hij' : (i : ℤ) ≤ j := by exact_mod_cast hij
    unfold ht
    split_ifs with a b b
    · exact le_refl _
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → y = x → ¬w = z → z = true ∧ w = false := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hz, hw⟩ := key _ _ _ _ h1 h2 a b
      exact (hpos j hz hw).le
    · have key : ∀ x y z w : Bool, x ≤ z → w ≤ y → ¬y = x → w = z → x = false ∧ y = true := by
        intro x y z w
        cases x <;> cases y <;> cases z <;> cases w <;> simp (config := { decide := true })
      obtain ⟨hx, hy⟩ := key _ _ _ _ h1 h2 a b
      exact (hneg i hx hy).le
    · linarith
  · intro i
    unfold ht pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp only [h, h', ↓reduceIte, Fin.rev_rev]
      rw [rev_cast]
      ring
  · intro i h
    have h' := ht_eq_zero.mp h
    unfold pr
    rw [if_pos h']
  · intro i j hi hij
    have hi' : ¬ε i.rev = ε i := fun e => hi (ht_eq_zero.mpr e)
    have hj' : ¬ε j.rev = ε j := fun e => hi (hij.trans (ht_eq_zero.mpr e))
    unfold ht at hij
    rw [if_neg hi', if_neg hj'] at hij
    ext
    omega
  · intro i
    unfold wt sg
    split_ifs <;> norm_num
  · intro i
    unfold wt sg
    split_ifs <;> simp
  · intro i
    unfold wt pr
    by_cases h : ε i.rev = ε i
    · simp [h]
    · have h' : ¬ε i = ε i.rev := fun e => h e.symm
      simp [h, h']
  · intro i j hi hj
    have hi' := ht_eq_zero.mp hi
    have hj' := ht_eq_zero.mp hj
    have key : ∀ a b : Fin n, ε a.rev = ε a → ε b.rev = ε b → ε a = false → ε b = true → False := by
      intro a b ha hb h1 h2
      have t1 := lt_of_sign hε (ha.trans h1) h2
      have t2 := lt_of_sign hε h1 (hb.trans h2)
      rw [rev_cast] at t1 t2
      linarith
    have he : ε i = ε j := by
      cases h1 : ε i <;> cases h2 : ε j
      · rfl
      · exact (key i j hi' hj' h1 h2).elim
      · exact (key j i hj' hi' h2 h1).elim
      · rfl
    unfold wt sg
    rw [if_pos hi', if_pos hj', he]
end CompanionTheory.D.gk.admitted.CholeskyDecomposition
