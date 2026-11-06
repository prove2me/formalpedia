-- Prove2me | solution 1 for BianchiIX.measure_le_of_gaussCylinder_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T16:46:09.07181+00:00
-- url     : https://prove2.me/submissions/a22af8a6-ddec-4c97-9add-72463bf18f8d

import Definitions.Def_BianchiIX_Statistics_GaussInverse
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Theorems.Thm_BianchiIX_exists_gaussCode_of_irrational
import Theorems.Thm_BianchiIX_exists_gaussCylinder_subset
import Theorems.Thm_BianchiIX_firstGaussCylinders_disjoint
import Theorems.Thm_BianchiIX_gaussCode_mem_cylinder_iff
import Theorems.Thm_BianchiIX_gaussCode_prefix
import Theorems.Thm_BianchiIX_gaussCode_recurrence
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

section
open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.gaussCode_mem_cylinder (a : ℕ → ℕ+) (n : ℕ) :
    gaussCode a ∈ gaussCylinder (digitPrefix a n) :=
  ⟨gaussCode (shiftDigits a n),
    ⟨gaussCode_pos _, gaussCode_lt_one _⟩, (gaussCode_prefix a n).symm⟩

end
end

section
open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.gaussCylinder_subset_of_prefix {v w : List ℕ}
    (hw : ∀ a ∈ w, 1 ≤ a) (h : v <+: w) : gaussCylinder w ⊆ gaussCylinder v := by
  rcases h with ⟨t, rfl⟩
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨gaussWord t x, gaussWord_mem_open_unit t (fun a ha => hw a (by simp [ha])) hx, ?_⟩
  exact (gaussWord_append v t x).symm

end
end

section
open BianchiIX
noncomputable section
open Filter Set MeasureTheory
open scoped Topology ENNReal NNReal

private theorem BianchiIX.gaussCode_mem_first_cylinder {O : Set ℝ} (hO : IsOpen O)
    (a : ℕ → ℕ+) (ha : gaussCode a ∈ O) :
    ∃ w ∈ firstGaussCylinders O, gaussCode a ∈ gaussCylinder w := by
  classical
  have hex := exists_gaussCylinder_subset hO a ha
  let n := Nat.find hex
  refine ⟨digitPrefix a (n + 1), ⟨digitPrefix_positive a (n + 1), Nat.find_spec hex,
    ?_, ?_⟩, gaussCode_mem_cylinder a (n + 1)⟩
  · intro heq
    have hlen := digitPrefix_length a (n + 1)
    rw [heq] at hlen
    simp at hlen
  intro v hvne hv hvlen hsub
  have hvpos : ∀ k ∈ v, 1 ≤ k :=
    fun k hk => digitPrefix_positive a (n + 1) k (hv.sublist.subset hk)
  have hmem := gaussCylinder_subset_of_prefix (digitPrefix_positive a (n + 1)) hv
    (gaussCode_mem_cylinder a (n + 1))
  have heq := (gaussCode_mem_cylinder_iff a v hvpos).mp hmem
  have hpos : 0 < v.length := List.length_pos_iff.mpr hvne
  have hlt : v.length - 1 < n := by
    simp only [digitPrefix_length] at hvlen
    omega
  apply Nat.find_min hex hlt
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ v.length), heq] using hsub

end
end

theorem solution (μ ν : Measure ℝ) [ν.OuterRegular]
    (hμ : ∀ᵐ x ∂μ, x ∈ Ioo (0 : ℝ) 1 ∧ Irrational x)
    (hbound : ∀ w : List ℕ, w ≠ [] → (∀ k ∈ w, 1 ≤ k) →
      μ (gaussCylinder w) ≤ ν (gaussCylinder w)) : μ ≤ ν := by
  have hopen {O : Set ℝ} (hO : IsOpen O) : μ O ≤ ν O := by
    have hcover : μ O ≤ μ (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) := by
      apply measure_mono_ae
      filter_upwards [hμ] with x hx
      intro hxO
      obtain ⟨a, rfl⟩ := exists_gaussCode_of_irrational hx.1 hx.2
      obtain ⟨w, hw, hxw⟩ := gaussCode_mem_first_cylinder hO a hxO
      exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨hw, hxw⟩⟩
    calc
      μ O ≤ μ (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) := hcover
      _ ≤ ∑' w : firstGaussCylinders O, μ (gaussCylinder w.val) :=
        measure_biUnion_le μ (Set.to_countable _) _
      _ ≤ ∑' w : firstGaussCylinders O, ν (gaussCylinder w.val) :=
        ENNReal.tsum_le_tsum (fun w => hbound w.val w.property.2.2.1 w.property.1)
      _ = ν (⋃ w ∈ firstGaussCylinders O, gaussCylinder w) :=
        (measure_biUnion (Set.to_countable _) (firstGaussCylinders_disjoint O)
          (fun w _ => measurableSet_gaussCylinder w)).symm
      _ ≤ ν O := measure_mono (iUnion₂_subset fun _ hw => hw.2.1)
  apply Measure.le_iff.mpr
  intro A _
  rw [A.measure_eq_iInf_isOpen ν]
  exact le_iInf fun O => le_iInf fun hAO => le_iInf fun hO => (measure_mono hAO).trans (hopen hO)
