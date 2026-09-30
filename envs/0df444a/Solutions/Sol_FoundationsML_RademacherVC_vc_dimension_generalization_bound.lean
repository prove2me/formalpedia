-- Prove2me | solution 1 for FoundationsML.RademacherVC.vc_dimension_generalization_bound
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:14:41.9788+00:00
-- url     : https://prove2.me/submissions/16cffb64-89a1-4efc-a8fd-11d234a0b902

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

open MeasureTheory

namespace FoundationsML.RademacherVC

universe u

theorem vcg_hasVCDim_singleton :
    HasVCDim ({fun _ => true} : Set (PUnit.{u+1} → Bool)) 0 := by
  have hG : ∀ m, GrowthFunction ({fun _ => true} : Set (PUnit.{u+1} → Bool)) m = 1 := by
    intro m
    unfold GrowthFunction
    have : ∀ x : Fin m → PUnit.{u+1},
        Nat.card {t : Fin m → Bool // ∃ h ∈ ({fun _ => true} : Set (PUnit.{u+1} → Bool)), t = h ∘ x} = 1 := by
      intro x
      rw [Nat.card_eq_one_iff_exists]
      refine ⟨⟨fun _ => true, ⟨fun _ => true, rfl, rfl⟩⟩, ?_⟩
      rintro ⟨t, h, hh, rfl⟩
      simp at hh; subst hh; rfl
    simp only [this, ciSup_const]
  refine ⟨by rw [hG]; rfl, ?_⟩
  intro m hm
  rw [hG] at hm
  rcases m with _ | m
  · rfl
  · have : 2 ≤ 2 ^ (m+1) := Nat.le_self_pow (by omega) 2
    omega

theorem vcg_counter :
    ¬ (∀ {X : Type u} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (c : X → Bool)
    (m : ℕ) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  intro H
  have h := H (X := PUnit.{u+1}) (Measure.dirac PUnit.unit) {fun _ => true} 0
    vcg_hasVCDim_singleton (fun _ => false) 0 le_rfl (1/2) (by norm_num)
  have hE : GeneralizationError (Measure.dirac PUnit.unit.{u+1}) (fun _ => false) (fun _ => true) = 1 := by
    unfold GeneralizationError
    simp
  have hS : ∀ S : Fin 0 → PUnit.{u+1}, EmpiricalError S (fun _ => false) (fun _ => true) = 0 := by
    intro S; unfold EmpiricalError; simp
  simp [hE, hS] at h
  norm_num at h

end FoundationsML.RademacherVC

open FoundationsML.RademacherVC

theorem solution :
    ¬ (∀ {X : Type} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (c : X → Bool)
    (m : ℕ) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ),
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal) := by
  exact vcg_counter.{0}
