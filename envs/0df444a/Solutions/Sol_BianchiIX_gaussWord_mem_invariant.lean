-- Prove2me | solution 1 for BianchiIX.gaussWord_mem_invariant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:42:31.446205+00:00
-- url     : https://prove2.me/submissions/41efb4c1-46f3-449e-970c-7a26e51ec83c

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Theorems.Thm_BianchiIX_gaussMap_gaussInv_nat
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

open Set Filter MeasureTheory
open scoped Topology ENNReal
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

theorem solution {E : Set ℝ} (hE : gaussMap ⁻¹' E = E)
    (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    gaussWord w x ∈ E ↔ x ∈ E := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have hw' : ∀ b ∈ w, 1 ≤ b := fun b hb => hw b (by simp [hb])
    have hmem : gaussMap (gaussInv a (gaussWord w x)) ∈ E ↔
        gaussInv a (gaussWord w x) ∈ E := by
      change gaussInv a (gaussWord w x) ∈ gaussMap ⁻¹' E ↔ _
      rw [hE]
    rw [gaussMap_gaussInv_nat (gaussWord_mem_open_unit w hw' hx) (hw a (by simp))] at hmem
    exact hmem.symm.trans (ih hw')
