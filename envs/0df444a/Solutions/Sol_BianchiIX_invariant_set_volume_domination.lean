-- Prove2me | solution 1 for BianchiIX.invariant_set_volume_domination
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:47:24.335134+00:00
-- url     : https://prove2.me/submissions/a62e15ed-ee6f-47fd-ab2c-61791dce0e55

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Theorems.Thm_BianchiIX_ae_gaussMeasure_irrational
import Theorems.Thm_BianchiIX_gaussWord_image_inter_invariant
import Theorems.Thm_BianchiIX_gaussWord_image_measure_ge
import Theorems.Thm_BianchiIX_measurableSet_gaussCylinder
import Theorems.Thm_BianchiIX_measure_le_of_gaussCylinder_bounds
import Theorems.Thm_BianchiIX_volume_restrict_absolutelyContinuous_gaussMeasure
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Dynamics.Ergodic.Ergodic

open Set Filter MeasureTheory
open scoped ENNReal
open BianchiIX

section
open BianchiIX
noncomputable section
open Filter
open scoped Topology

private theorem BianchiIX.gaussInv_pos {a x : ℝ} (ha : 1 ≤ a) (hx : 0 ≤ x) : 0 < gaussInv a x := by
  unfold gaussInv
  exact one_div_pos.mpr (by linarith)

end
end

section
open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.gaussWord_mem_open_unit (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) : gaussWord w x ∈ Ioo (0 : ℝ) 1 := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (1 : ℝ) ≤ a := by exact_mod_cast hw a (by simp)
    have ht := ih (fun b hb => hw b (by simp [hb]))
    refine ⟨gaussInv_pos ha ht.1.le, ?_⟩
    change 1 / ((a : ℝ) + gaussWord w x) < 1
    exact (div_lt_one (by linarith [ht.1])).mpr (by linarith [ht.1])

end
end

theorem solution {E : Set ℝ} (hE : MeasurableSet E)
    (hinv : gaussMap ⁻¹' E = E) :
    ((1 / 2 : ℝ≥0∞) * volume (Ioo (0 : ℝ) 1 ∩ E)) • volume.restrict (Ioo (0 : ℝ) 1) ≤
      volume.restrict (Ioo (0 : ℝ) 1 ∩ E) := by
  let B := Ioo (0 : ℝ) 1 ∩ E
  have hBfinite : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono inter_subset_left)
  let : (volume.restrict B).Regular := Measure.Regular.restrict_of_measure_ne_top hBfinite
  apply measure_le_of_gaussCylinder_bounds
  · apply (Measure.ae_smul_measure_le _)
    exact (ae_restrict_mem measurableSet_Ioo).and
      (volume_restrict_absolutelyContinuous_gaussMeasure.ae_le ae_gaussMeasure_irrational)
  · intro w _ hw
    have hsub : gaussCylinder w ⊆ Ioo (0 : ℝ) 1 := by
      rintro _ ⟨x, hx, rfl⟩
      exact gaussWord_mem_open_unit w hw hx
    have h := gaussWord_image_measure_ge w hw (measurableSet_Ioo.inter hE) inter_subset_left
    rw [gaussWord_image_inter_invariant hinv w hw] at h
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (measurableSet_gaussCylinder w), ← inter_assoc,
      inter_eq_left.mpr hsub]
    simpa only [mul_right_comm] using h
