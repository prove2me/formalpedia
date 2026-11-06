-- Prove2me | solution 1 for BianchiIX.gaussCode_mem_cylinder_iff
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T15:58:41.133356+00:00
-- url     : https://prove2.me/submissions/8782d0b2-0e46-496b-a1a4-5f8aac1017e8

import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_gaussCode_prefix
import Theorems.Thm_BianchiIX_gaussCode_recurrence
import Theorems.Thm_BianchiIX_gaussCylinder_comparable
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

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_tendsto (a : ℕ → ℕ+) : Tendsto (gaussApprox a) atTop (𝓝 (gaussCode a)) :=
  (cauchySeq_tendsto_of_complete (gaussApprox_cauchy a)).choose_spec

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_mem_unit (a : ℕ → ℕ+) : gaussCode a ∈ Icc (0 : ℝ) 1 :=
  isClosed_Icc.mem_of_tendsto (gaussCode_tendsto a) (Eventually.of_forall (gaussApprox_mem_unit a))

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_pos (a : ℕ → ℕ+) : 0 < gaussCode a := by
  rw [gaussCode_recurrence a]
  apply gaussInv_pos _ (gaussCode_mem_unit (shiftDigits a 1)).1
  exact_mod_cast Nat.succ_le_of_lt (a 0).pos

end
end

section
open BianchiIX
noncomputable section
open Filter Set
open scoped Topology

private theorem BianchiIX.gaussCode_lt_one (a : ℕ → ℕ+) : gaussCode a < 1 := by
  rw [gaussCode_recurrence a]
  have ha : (1 : ℝ) ≤ a 0 := by exact_mod_cast Nat.succ_le_of_lt (a 0).pos
  have ht := gaussCode_pos (shiftDigits a 1)
  unfold gaussInv
  exact (div_lt_one (by positivity)).mpr (by linarith)

end
end

private theorem BianchiIX.gaussCode_mem_cylinder (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a ∈ gaussCylinder (digitPrefix a n) :=
  ⟨gaussCode (shiftDigits a n),
    ⟨gaussCode_pos _, gaussCode_lt_one _⟩, (gaussCode_prefix a n).symm⟩

theorem solution (a : ℕ → ℕ+) (w : List ℕ)
    (hw : ∀ k ∈ w, 1 ≤ k) :
    gaussCode a ∈ gaussCylinder w ↔ digitPrefix a w.length = w := by
  constructor
  · intro h
    have hc := gaussCylinder_comparable (digitPrefix_positive a w.length) hw
      ⟨gaussCode a, gaussCode_mem_cylinder a w.length, h⟩
    rcases hc with hc | hc
    · exact hc.eq_of_length (digitPrefix_length a w.length)
    · exact (hc.eq_of_length (digitPrefix_length a w.length).symm).symm
  · intro h
    rw [← h]
    exact gaussCode_mem_cylinder a w.length
