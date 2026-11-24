-- Prove2me | solution 1 for Formalism.REAL.compact_casimir_positions_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:03.944211+00:00
-- url     : https://prove2.me/submissions/3b4b4f1e-81a8-443a-b420-2e0c4a2d6597

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_fin_one_fun_eq_const_apply_zero
import Theorems.Thm_Formalism_REAL_positions_one_apply
import Theorems.Thm_Formalism_REAL_CasK_apply
import Theorems.Thm_Formalism_REAL_bool_trichotomy_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {ε : Fin n → Bool} (F : Arr V n 1)
    (hz : ∀ a b, ε a = ε b → F (fun _ => (a, b)) = 0) :
    CasK ε (positionsE V n 1) F = (n : ℂ) • F := by
  apply PiLp.ext
  intro α
  rw [fin_one_fun_eq_const_apply_zero α, PiLp.smul_apply]
  obtain ⟨a, b⟩ := α 0
  rw [CasK_apply]
  by_cases hab : ε a = ε b
  · rw [hz a b hab, smul_zero]
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro d _
    split_ifs with hcd
    · simp only [positions_one_apply]
      have hd : ∀ x, F (fun _ => (x, x)) = 0 := fun x => hz x x rfl
      by_cases h1 : a = c <;> by_cases h2 : b = d
      · subst h1; subst h2; simp [hz _ _ hab, hd]
      · subst h1; simp [hz _ _ hab, hd, h2]
      · subst h2; simp [hz _ _ hab, hd, h1]
      · simp [h1, h2]
    · rfl
  · have key : ∀ c d, (if ε c = ε d then positionsE V n 1 c d (positionsE V n 1 d c F) (fun _ => (a, b))
        else 0) = (if c = a then (if ε d = ε a then F (fun _ => (a, b)) else 0) else 0) +
          (if d = b then (if ε c = ε b then F (fun _ => (a, b)) else 0) else 0) := by
      intro c d
      have hab' : a ≠ b := fun h => hab (h ▸ rfl)
      by_cases hcd : ε c = ε d
      · rw [if_pos hcd]
        simp only [positions_one_apply]
        by_cases h1 : c = a
        · subst h1
          have hbd : b ≠ d := by rintro rfl; exact hab hcd
          simp [hbd, Ne.symm hbd, Ne.symm hab', hcd.symm]
        · by_cases h2 : d = b
          · subst h2
            simp [h1, Ne.symm h1, hab', hcd]
          · simp [h1, Ne.symm h1, h2, Ne.symm h2]
      · rw [if_neg hcd]
        have e1 : (if c = a then (if ε d = ε a then F (fun _ => (a, b)) else 0) else 0) = 0 := by
          split_ifs with h1 h2
          · subst h1; exact absurd h2.symm hcd
          · rfl
          · rfl
        have e2 : (if d = b then (if ε c = ε b then F (fun _ => (a, b)) else 0) else 0) = 0 := by
          split_ifs with h1 h2
          · subst h1; exact absurd h2 hcd
          · rfl
          · rfl
        rw [e1, e2, add_zero]
    simp only [key, Finset.sum_add_distrib, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_add_distrib]
    have : ∀ d : Fin n, ((if ε d = ε a then F (fun _ => (a, b)) else 0) +
        (if ε d = ε b then F (fun _ => (a, b)) else 0)) = F (fun _ => (a, b)) := by
      intro d
      rcases bool_trichotomy_of_ne (ε a) (ε b) (ε d) hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [if_pos h1, if_neg h2, add_zero]
      · rw [if_neg h2, if_pos h1, zero_add]
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [Nat.cast_smul_eq_nsmul]
end Formalism.REAL
