-- Prove2me | solution 1 for FoundationsML.ModelSelection.erm_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:06:48.817702+00:00
-- url     : https://prove2.me/submissions/26808582-465d-4c80-b5ed-e4f112d9f3a0

import Mathlib
import Definitions.Def_FoundationsML_ModelSelection_GeneralizationError
import Definitions.Def_FoundationsML_ModelSelection_EmpiricalError

open MeasureTheory

namespace FoundationsML.ModelSelection

theorem aux_ermb_gen_nonneg {X Y : Type*} [MeasurableSpace X] (D : Measure X)
    (c h : X → Y) : 0 ≤ GeneralizationError D c h := by
  unfold GeneralizationError
  exact ENNReal.toReal_nonneg

theorem aux_ermb_gen_le_one {X Y : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] (c h : X → Y) : GeneralizationError D c h ≤ 1 := by
  unfold GeneralizationError
  have h1 : D {x | h x ≠ c x} ≤ 1 := prob_le_one
  have h2 : D {x | h x ≠ c x} ≠ ⊤ := measure_ne_top _ _
  calc (D {x | h x ≠ c x}).toReal ≤ (1 : ENNReal).toReal :=
        ENNReal.toReal_mono ENNReal.one_ne_top h1
    _ = 1 := by simp

theorem aux_ermb_emp_nonneg {X Y : Type*} {m : ℕ} (S : Fin m → X) (c h : X → Y) :
    0 ≤ EmpiricalError S c h := by
  unfold EmpiricalError
  positivity

open Classical in
theorem aux_ermb_emp_le_one {X Y : Type*} {m : ℕ} (S : Fin m → X) (c h : X → Y) :
    EmpiricalError S c h ≤ 1 := by
  unfold EmpiricalError
  apply div_le_one_of_le₀ _ (Nat.cast_nonneg m)
  have : (Finset.univ.filter (fun i : Fin m => h (S i) ≠ c (S i))).card ≤ m := by
    calc _ ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
      _ = m := by simp
  exact_mod_cast this

theorem aux_ermb_abs_le_one {X Y : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] {m : ℕ} (S : Fin m → X) (c h : X → Y) :
    |GeneralizationError D c h - EmpiricalError S c h| ≤ 1 := by
  have := aux_ermb_gen_nonneg D c h
  have := aux_ermb_gen_le_one D c h
  have := aux_ermb_emp_nonneg S c h
  have := aux_ermb_emp_le_one S c h
  rw [abs_le]; constructor <;> linarith

theorem aux_ermb_le_sup {X Y : Type*} [MeasurableSpace X] (D : Measure X)
    [IsProbabilityMeasure D] {m : ℕ} (S : Fin m → X) (c : X → Y) (H : Set (X → Y))
    (h : X → Y) (hh : h ∈ H) :
    |GeneralizationError D c h - EmpiricalError S c h| ≤
      ⨆ h ∈ H, |GeneralizationError D c h - EmpiricalError S c h| := by
  have hbdd : BddAbove (Set.range fun h : X → Y =>
      ⨆ (_ : h ∈ H), |GeneralizationError D c h - EmpiricalError S c h|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨h', rfl⟩
    exact Real.iSup_le (fun _ => aux_ermb_abs_le_one D S c h') zero_le_one
  refine le_ciSup_of_le hbdd h ?_
  rw [ciSup_pos hh]

end FoundationsML.ModelSelection

open FoundationsML.ModelSelection
open MeasureTheory

theorem solution {X Y : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c : X → Y) (H : Set (X → Y)) (hH : H.Nonempty) (m : ℕ)
    (hERM : (Fin m → X) → (X → Y))
    (hERM_mem : ∀ S, hERM S ∈ H)
    (hERM_min : ∀ S, ∀ h ∈ H, EmpiricalError S c (hERM S) ≤ EmpiricalError S c h)
    (ε : ℝ) :
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (hERM S) -
        sInf (GeneralizationError D c '' H) > ε}).toReal ≤
    (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | (⨆ h ∈ H, |GeneralizationError D c h - EmpiricalError S c h|) > ε / 2}
      ).toReal := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro S hS
  simp only [Set.mem_ofPred_eq] at hS ⊢
  set s := ⨆ h ∈ H, |GeneralizationError D c h - EmpiricalError S c h| with hs
  have key : GeneralizationError D c (hERM S) - 2 * s ≤ sInf (GeneralizationError D c '' H) := by
    apply le_csInf (hH.image _)
    rintro _ ⟨h, hh, rfl⟩
    have h1 := aux_ermb_le_sup D S c H h hh
    have h2 := aux_ermb_le_sup D S c H (hERM S) (hERM_mem S)
    have h3 := hERM_min S h hh
    have h4 := (abs_le.mp h1).1
    have h5 := (abs_le.mp h2).2
    linarith
  linarith
