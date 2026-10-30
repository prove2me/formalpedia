-- Prove2me | solution 1 for CapacitatedAssort.General.theorem_4
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:12:51.097993+00:00
-- url     : https://prove2.me/submissions/08a5f443-620a-4c76-8918-711dec111409

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Algorithm

open CapacitatedAssort.General

noncomputable def s226ca_D : Instance 1 1 where
  a := fun _ _ => 1
  w := fun _ => 0
  W := 0
  split := 0
  g := fun _ => -1

theorem solution : ¬ ((∀ {n M : ℕ} (D : Instance n M), Standing D →
      MixedMonotone D.split D.g → ScalingStable D.split D.g →
      ∀ ε : ℝ, 0 < ε → ∃ S : Finset (Fin n),
        output D ε = some S ∧ Feasible D S ∧ (1-ε) * optimum D ≤ value D S) ∧
    (∀ M : ℕ, 0 < M → ∃ C : ℝ, 0 < C ∧
      ∀ {n : ℕ} (D : Instance n M), Standing D →
      MixedMonotone D.split D.g → ScalingStable D.split D.g →
      ∀ ε : ℝ, 0 < ε → ε < 1 → 2 ≤ (n : ℝ) * ratio D →
        (operations D ε : ℝ) ≤ C * runtimeScale D ε)) := by
  intro H
  have hSt : Standing s226ca_D := by
    refine ⟨by norm_num, by norm_num, by simp [s226ca_D], ?_, ?_, ?_⟩
    · intro i m; simp [s226ca_D]
    · intro i; simp [s226ca_D]
    · simp [s226ca_D]
  have hMono : MixedMonotone s226ca_D.split s226ca_D.g := by
    intro m x s t _
    simp [s226ca_D]
  have hStab : ScalingStable s226ca_D.split s226ca_D.g := by
    intro u v _ _
    refine ⟨fun _ => 0, ⟨fun _ => le_refl 0, 0, 1, le_refl 0, one_pos, ?_⟩, 1, one_pos, ?_⟩
    · intro δ _ _; simp
    · intro δ _ _ x; simp [s226ca_D]
  obtain ⟨S, -, -, hS⟩ := H.1 s226ca_D hSt hMono hStab (1/2) (by norm_num)
  have hval : ∀ T, value s226ca_D T = -1 := fun T => rfl
  have hopt : optimum s226ca_D = -1 := by
    classical
    unfold optimum
    simp only []
    split_ifs with h
    · have : value s226ca_D = fun _ => -1 := funext hval
      rw [this]; exact Finset.sup'_const h (-1)
    · exact absurd ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [Feasible, weight, s226ca_D]⟩⟩ h
  rw [hopt, hval] at hS
  norm_num at hS
