-- Prove2me | solution 1 for Formalism.FG.additive_law_example
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:58.28994+00:00
-- url     : https://prove2.me/submissions/5fc683ee-ce5b-483d-a773-5ded1ae0e9a2

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_AdditiveLawExample
import Theorems.Thm_Formalism_FG_FormalGroupSubstitution_subst_X_add_X
import Theorems.Thm_P2M_Formalism_FG_FormalGroupSubstitution_subst_X__cb4c70d05671
import Theorems.Thm_Formalism_FG_FormalGroupSubstitution_atXv_X
import Theorems.Thm_Formalism_FG_FormalGroupSubstitution_atYv_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FG
open MvPowerSeries Formalism.FG.FormalGroupSubstitution
namespace Formalism.FG
theorem _root_.solution : Formalism.FG.AddLawExample := by
  unfold AddLawExample
  have hF : ∀ i : Fin 2, constantCoeff
      (vX i + vY i : MvPowerSeries (Fin 2 × Fin 2) ℤ) = 0 := fun i => by simp
  refine ⟨⟨hF, ?_, ?_, ?_, ?_⟩, ?_, ⟨fun i => by simp, ?_⟩, ⟨hF, ⟨fun j => by simp, ?_⟩, ?_⟩⟩
  · intro i x
    obtain ⟨a, b⟩ := x
    fin_cases a <;> fin_cases b <;> fin_cases i <;> simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp
  · intro i
    have hin : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 (Fin.castSucc y.1) y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 0 j + v3 1 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    have hin' : ∀ j : Fin 2, subst (fun y : Fin 2 × Fin 2 => (v3 y.1.succ y.2 :
        MvPowerSeries (Fin 3 × Fin 2) ℤ)) (vX j + vY j : MvPowerSeries (Fin 2 × Fin 2) ℤ) =
        v3 1 j + v3 2 j := fun j => by
      rw [subst_X_add_X _ (fun s => by simp)]
      rfl
    simp only [hin, hin']
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp),
      subst_X_add_X _ (fun s => by split_ifs <;> simp)]
    simp only [show ((1 : Fin 2) = 0) = False from by decide,
      if_true, if_false]
    rw [add_assoc]
  · intro i
    rw [subst_X_add_X _ (fun s => by simp)]
    rw [show Fin.rev (0 : Fin 2) = 1 from rfl, show Fin.rev (1 : Fin 2) = 0 from rfl, add_comm]
  · intro i
    rw [subst_X' _ hF]
    rw [subst_X_add_X _ (fun s => by split_ifs <;> simp [atXv_X, atYv_X])]
    simp [atXv_X, atYv_X]
  · intro j i
    simp [coeff_X, Finsupp.single_eq_single_iff]
  · intro j
    rw [subst_X' _ hF, atXv_X, atYv_X]
end Formalism.FG
