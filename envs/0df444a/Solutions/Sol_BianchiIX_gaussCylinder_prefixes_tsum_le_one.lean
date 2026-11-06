-- Prove2me | solution 1 for BianchiIX.gaussCylinder_prefixes_tsum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T17:07:24.457918+00:00
-- url     : https://prove2.me/submissions/44eacacc-7fe8-498b-926d-699f78615846

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_Statistics_StoppedMass
import Theorems.Thm_BianchiIX_gaussCylinder_prefixes_disjoint
import Theorems.Thm_BianchiIX_measurableSet_gaussCylinder
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

open BianchiIX
noncomputable section
open Set MeasureTheory
open scoped ENNReal

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

theorem solution {ι : Type*} [Countable ι]
    (a : ι → ℕ → ℕ+) (n : ℕ)
    (hunique : Function.Injective (fun i => digitPrefix (a i) n)) :
    (∑' i, volume (gaussCylinder (digitPrefix (a i) n))) ≤ 1 := by
  rw [← measure_iUnion (gaussCylinder_prefixes_disjoint a n hunique)
    (fun i => measurableSet_gaussCylinder _)]
  calc
    volume (⋃ i, gaussCylinder (digitPrefix (a i) n)) ≤ volume (Ioo (0 : ℝ) 1) := by
      apply measure_mono
      apply iUnion_subset
      intro i x hx
      rcases hx with ⟨t, ht, rfl⟩
      exact gaussWord_mem_open_unit _ (digitPrefix_positive (a i) n) ht
    _ = 1 := by norm_num
