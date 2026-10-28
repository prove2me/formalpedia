-- Prove2me | solution 1 for CountingMatroid.Analysis.FinishPhaseWeightsSize.finishPhase_weights_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T13:01:51.91498+00:00
-- url     : https://prove2.me/submissions/9737a6e3-8457-497b-a8b6-4bc506fa1e36

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_RationalHeight
import Definitions.Def_CountingMatroid_Analysis_ScheduleOpeningCost
import Definitions.Def_CountingMatroid_Analysis_ScheduleThermalSetupCost
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
import Definitions.Def_CountingMatroid_Model_Run
import Definitions.Def_CountingMatroid_Model_Subroutines
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines















/-- INTERNAL: Rational inversion swaps numerator and denominator lengths. -/
theorem binaryRatLength_inv_eq (q : ℚ) :
    binaryRatLength q⁻¹ = binaryRatLength q := by
  by_cases hz : q.num = 0
  · have hq : q = 0 := Rat.zero_of_num_zero hz
    simp [hq]
  · unfold binaryRatLength binaryNatLength
    simp [Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
      Int.natAbs_sign, hz, Int.natAbs_natCast]
    omega

/-- INTERNAL: Rational division adds no more binary encoding length than
multiplication by the denominator's reciprocal. -/
theorem binaryRatLength_div_le (q s : ℚ) :
    binaryRatLength (q / s) ≤ binaryRatLength q + binaryRatLength s := by
  rw [div_eq_mul_inv]
  simpa only [binaryRatLength_inv_eq] using binaryRatLength_mul_le q s⁻¹





/-- INTERNAL: A natural cast needs its own binary length plus three framing bits. -/
theorem binaryRatLength_natCast (a : ℕ) :
    binaryRatLength (a : ℚ) = a.log2 + 4 := by
  simp only [binaryRatLength, binaryNatLength, Rat.num_natCast,
    Rat.den_natCast, Int.natAbs_natCast]
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega









end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: Iterate a rational-size budget over a charged scan, with a fixed
additive increment per visited entry. TEXLINE: main.tex:1356-1360 -/
private theorem scan_size_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (D : ℕ)
    (hf : ∀ b i K, P b K → P (f b i).val (K + D))
    (l : List ι) (b : β) (K : ℕ) (hb : P b K) :
    P (Arlib.Computation.Charged.foldl f l b).val (K + l.length * D) := by
  induction l generalizing b K with
  | nil => simpa using hb
  | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      simpa [List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ih (f b i).val (K + D) (hf b i K hb)



end CountingMatroid.Analysis.FinishPhaseWeightsSize

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseWeightsSize
end CountingMatroid.Analysis.FinishPhaseWeightsSize
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FinishPhaseWeightsSize
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: The successful nested multiplier scan adds at most four bounded
count encodings per visit, without requiring uniqueness of writes.
TEXLINE: main.tex:1356-1360 -/
theorem solution {n : ℕ} (s : AnnealingSchedule) (j K : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hc : ∀ kind, observed.counts kind ≤ s.observations)
    (hw : ∀ index, binaryRatLength (weights index) ≤ K)
    (ratio : ℚ) (nextWeights : Multipliers n)
    (h : (finishPhase s j weights observed).val = some (ratio, nextWeights)) :
    ∀ index, binaryRatLength (nextWeights index) ≤
      K + n * n * (4 * (s.observations + 4)) := by
  let D := 4 * (s.observations + 4)
  let P : Option (Multipliers n) → ℕ → Prop :=
    fun acc K => ∀ w, acc = some w → ∀ index, binaryRatLength (w index) ≤ K
  have hcast (a : ℕ) (ha : a ≤ s.observations) :
      binaryRatLength (a : ℚ) ≤ s.observations + 4 := by
    rw [binaryRatLength_natCast]
    have hl := Nat.log_le_self 2 a
    rw [← Nat.log2_eq_log_two] at hl
    omega
  have hpzero : binaryRatLength
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ≤
      2 * (s.observations + 4) := by
    have := binaryRatLength_div_le (observed.counts .transversal : ℚ)
      (s.observations : ℚ)
    have := hcast _ (hc .transversal)
    have := hcast _ (le_refl _)
    omega
  simp only [finishPhase, Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · let step : Fin n → Fin n → Option (Multipliers n) →
        Arlib.Computation.Charged Op Cell (Option (Multipliers n)) :=
        fun i k acc =>
          match acc with
          | none => pure none
          | some current => do
              let diagonal ← indexEqual i k
              if diagonal then pure (some current)
              else
                if h : i ≠ k then
                  let count ← countRead observed.counts (.defect i k)
                  let zero ← natEqual count 0
                  if zero then pure none
                  else if (lessThan (successor j).val s.L).val then
                    let pCount ← ratOfNat count
                    let pDefect ← ratDiv pCount (ratOfNat s.observations).val
                    let old ← multiplierRead current ⟨i, k, h⟩
                    let numerator ← ratMul old
                      ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
                    let value ← ratDiv numerator pDefect
                    let newer ← multiplierWrite current ⟨i, k, h⟩ value
                    pure (some newer)
                  else pure (some current)
                else pure none
    have hs : ∀ i acc k B, P acc B → P (step i k acc).val (B + D) := by
      intro i acc k B hb next hn index
      cases acc with
      | none => simp [step] at hn
      | some current =>
          dsimp [step] at hn
          split at hn
          · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at hn
            subst next
            exact (hb current rfl index).trans (Nat.le_add_right _ _)
          · split at hn
            · simp only [Arlib.Computation.Charged.val_bind] at hn
              split at hn
              · simp at hn
              · split at hn
                · simp only [Arlib.Computation.Charged.val_bind,
                    Arlib.Computation.Charged.val_pure, Option.some.injEq] at hn
                  subst next
                  simp only [multiplierWrite, Arlib.Computation.Charged.val_opMany]
                  split_ifs with hi
                  · have hpdef := binaryRatLength_div_le
                      (observed.counts (.defect i k) : ℚ) (s.observations : ℚ)
                    have hpc := hcast _ (hc (.defect i k))
                    have hpo := hcast _ (le_refl _)
                    have hmul := binaryRatLength_mul_le (current ⟨i, k, ‹i ≠ k›⟩)
                      ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
                    have hdiv := binaryRatLength_div_le
                      (current ⟨i, k, ‹i ≠ k›⟩ *
                        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)))
                      ((observed.counts (.defect i k) : ℚ) / (s.observations : ℚ))
                    have hold := hb current rfl ⟨i, k, ‹i ≠ k›⟩
                    simp only [ratDiv, ratMul, ratOfNat, countRead, multiplierRead,
                      Arlib.Computation.Charged.val_opMany]
                    dsimp [D]
                    omega
                  · exact (hb current rfl index).trans (Nat.le_add_right _ _)
                · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at hn
                  subst next
                  exact (hb current rfl index).trans (Nat.le_add_right _ _)
            · simp at hn
    have hinner : ∀ acc i B, P acc B →
        P (Arlib.Computation.Charged.foldl (fun acc k => step i k acc)
          (List.finRange n) acc).val (B + n * D) := by
      intro acc i B hb
      simpa using scan_size_growth P (fun acc k => step i k acc) D
        (hs i) (List.finRange n) acc B hb
    have hout := scan_size_growth P
      (fun acc i => Arlib.Computation.Charged.foldl (fun acc k => step i k acc)
        (List.finRange n) acc) (n * D) hinner (List.finRange n) (some weights) K
      (by intro w he; cases Option.some.inj he; exact hw)
    simp only [Arlib.Computation.Charged.val_bind] at h
    simp only [ratOfNat, ratDiv, countRead, Arlib.Computation.Charged.val_opMany] at h
    change (match (Arlib.Computation.Charged.foldl
      (fun acc i => Arlib.Computation.Charged.foldl (fun acc k => step i k acc)
        (List.finRange n) acc) (List.finRange n) (some weights)).val with
      | none => pure none
      | some updated => pure (some
        ((observed.numeratorSum / (s.observations : ℚ)) /
          ((observed.counts .transversal : ℚ) / (s.observations : ℚ)), updated)) :
        Arlib.Computation.Charged Op Cell (Option (ℚ × Multipliers n))).val = some (ratio, nextWeights) at h
    split at h
    · simp at h
    · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl⟩
      simpa [P, D, Nat.mul_assoc] using hout _ ‹_ = some _›
