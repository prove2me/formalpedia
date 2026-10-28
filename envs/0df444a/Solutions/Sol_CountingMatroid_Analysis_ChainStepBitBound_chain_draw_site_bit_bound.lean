-- Prove2me | solution 1 for CountingMatroid.Analysis.ChainStepBitBound.chain_draw_site_bit_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:39:53.23722+00:00
-- url     : https://prove2.me/submissions/c9f5351c-2903-4f42-862a-d5a94538b341

import Definitions.Def_CountingMatroidSupport_Computation_Charged
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Charged_Extension2
import Definitions.Def_CountingMatroidSupport_Computation_Cost
import Definitions.Def_CountingMatroidSupport_Computation_Cost_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Dict
import Definitions.Def_CountingMatroidSupport_Computation_Heap
import Definitions.Def_CountingMatroidSupport_Computation_Machine
import Definitions.Def_CountingMatroidSupport_Computation_Machine_Extension1
import Definitions.Def_CountingMatroidSupport_Computation_Num
import Definitions.Def_CountingMatroidSupport_Computation_Queue
import Definitions.Def_CountingMatroidSupport_Computation_Rand
import Definitions.Def_CountingMatroidSupport_Computation_Roster
import Definitions.Def_CountingMatroidSupport_Computation_Slot
import Definitions.Def_CountingMatroidSupport_Computation_Space
import Definitions.Def_CountingMatroidSupport_Computation_Std
import Definitions.Def_CountingMatroid_Analysis_BoundedUniformReplay
import Definitions.Def_CountingMatroid_Analysis_ChainDrawSiteReplay
import Definitions.Def_CountingMatroid_Analysis_ChainStepIntervalReplay
import Definitions.Def_CountingMatroid_Analysis_EstimateMedianResource
import Definitions.Def_CountingMatroid_Analysis_PhaseChainWork
import Definitions.Def_CountingMatroid_Analysis_PhaseResourcePrimitives
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
import Theorems.Thm_CountingMatroid_Analysis_ChainStepBitBound_boundedUniform_cursor_le
import Theorems.Thm_CountingMatroid_Analysis_PhaseChainWork_weightOfKind_work_size
import Theorems.Thm_CountingMatroid_Analysis_ScheduleOtherStepsEnvelope_binaryRatLength_mul_le

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
namespace CountingMatroid.Analysis.LeastHalvingsCost
end CountingMatroid.Analysis.LeastHalvingsCost
namespace CountingMatroid.Analysis
end CountingMatroid.Analysis
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















end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

end

section


set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites





/-- INTERNAL: A capped draw width is bounded by the natural encoding length. -/
private theorem draw_width_le (v : ℕ) : (v - 1).log2 + 1 ≤ v.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le v 1)) 1

/-- INTERNAL: A ratio of two bounded state weights has a bounded draw width.
TEXLINE: main.tex:1382-1400 -/
private theorem ratio_width_le (old new : ℚ) (K : ℕ)
    (ho : binaryRatLength old ≤ 2 * K) (hn : binaryRatLength new ≤ 2 * K) :
    ((new / old).den - 1).log2 + 1 ≤ 4 * K := by
  have hr := binaryRatLength_div_le new old
  have hd := draw_width_le (new / old).den
  unfold binaryRatLength binaryNatLength at hr ho hn
  omega





end CountingMatroid.Analysis.ChainStepBitBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved capped-uniform cursor growth and chain/stopped-site three-draw bounds; avoided an ill-typed simplified charged Boolean condition with a local transparency setting.
-/

end
set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound
end CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Even all future trials of a stopped chain draw fit the same
three-draw budget as a completed chain attempt.
TEXLINE: main.tex:1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (site : Fin 3) (d : ℕ × ℕ)
    (h : chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let W := 4 * K + n + 1
  have hnwidth : (n - 1).log2 + 1 ≤ W := by
    have hl : n.log2 ≤ n := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
    have hd := draw_width_le n
    dsimp [W]; omega
  have hdraw (c : ℕ) : (boundedUniform tape s.drawTrials n c).val.2 ≤ c + s.drawTrials * W :=
    (boundedUniform_cursor_le tape s.drawTrials n c).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left s.drawTrials hnwidth) c)
  have hntrials := Nat.mul_le_mul_left s.drawTrials hnwidth
  have hweight (x : PairedSet n) (kind : StateKind n) :=
    (PhaseChainWork.weightOfKind_work_size r o₁ o₂ q weights x kind K hq hw).2
  unfold chainDrawSite at h
  split at h
  · cases h
  · have hA := hdraw (cursor + 1)
    split at h
    · have he := Option.some.inj h
      rw [← he]
      dsimp [W] at hntrials ⊢
      simp only [Nat.mul_assoc] at hntrials ⊢
      omega
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨aIndex, ha, h⟩ := h
      have hB := hdraw (boundedUniform tape s.drawTrials n (cursor + 1)).val.2
      split at h
      · have he := Option.some.inj h
        rw [← he]
        dsimp [W] at hA hntrials ⊢
        simp only [Nat.mul_assoc] at hA hntrials ⊢
        omega
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨bIndex, hb, a, ha', b, hb', h⟩ := h
        split at h
        · cases h
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨old, ho, new, hn, h⟩ := h
          have hr := ratio_width_le old new K (hweight _ _ old ho) (hweight _ _ new hn)
          have hrt := Nat.mul_le_mul_left s.drawTrials (hr.trans (show 4 * K ≤ 4 * K + n + 1 by omega))
          split at h
          · have he := Option.some.inj h
            rw [← he]
            dsimp [W] at hA hB ⊢
            simp only [Nat.mul_assoc] at hA hB ⊢
            omega
          · cases h
