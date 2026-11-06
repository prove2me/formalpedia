-- Prove2me | solution 1 for BianchiIX.gaussCylinder_comparable
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:56:36.08903+00:00
-- url     : https://prove2.me/submissions/85a69f4d-9c6c-40c9-9d26-7cbac3818fa1

import Definitions.Def_BianchiIX_Statistics_GaussCylinders
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
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular

open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

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

private theorem BianchiIX.measurableEmbedding_gaussInv (a : ℝ) : MeasurableEmbedding (gaussInv a) := by
  have h : MeasurableEmbedding (fun x : ℝ => (a + x)⁻¹) :=
    (MeasurableEquiv.inv ℝ).measurableEmbedding.comp
      (MeasurableEquiv.addLeft a).measurableEmbedding
  change MeasurableEmbedding (fun x : ℝ => 1 / (a + x))
  simpa only [one_div] using h

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

private theorem BianchiIX.gaussInv_digit {a : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ⌊1 / gaussInv a x⌋ = (a : ℤ) := by
  simp only [gaussInv, one_div_one_div]
  apply Int.floor_eq_iff.mpr
  push_cast
  constructor <;> linarith [hx.1, hx.2]

theorem solution {v w : List ℕ}
    (hv : ∀ a ∈ v, 1 ≤ a) (hw : ∀ a ∈ w, 1 ≤ a)
    (h : (gaussCylinder v ∩ gaussCylinder w).Nonempty) : v <+: w ∨ w <+: v := by
  induction v generalizing w with
  | nil => exact Or.inl List.nil_prefix
  | cons a v ih =>
    cases w with
    | nil => exact Or.inr List.nil_prefix
    | cons b w =>
      rcases h with ⟨z, ⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
      have hv' : ∀ c ∈ v, 1 ≤ c := fun c hc => hv c (by simp [hc])
      have hw' : ∀ c ∈ w, 1 ≤ c := fun c hc => hw c (by simp [hc])
      have hval : gaussInv a (gaussWord v x) = gaussInv b (gaussWord w y) :=
        hxz.trans hyz.symm
      have hab : a = b := by
        have hd := congrArg (fun z : ℝ => ⌊1 / z⌋) hval
        rw [gaussInv_digit (gaussWord_mem_open_unit v hv' hx),
          gaussInv_digit (gaussWord_mem_open_unit w hw' hy)] at hd
        exact_mod_cast hd
      subst b
      have htail := (measurableEmbedding_gaussInv a).injective hval
      have hi : (gaussCylinder v ∩ gaussCylinder w).Nonempty :=
        ⟨gaussWord v x, ⟨x, hx, rfl⟩, ⟨y, hy, htail.symm⟩⟩
      simpa only [List.cons_prefix_cons, true_and, eq_self] using ih hv' hw' hi
