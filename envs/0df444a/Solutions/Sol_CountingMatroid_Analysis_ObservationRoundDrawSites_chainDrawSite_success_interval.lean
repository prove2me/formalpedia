-- Prove2me | solution 1 for CountingMatroid.Analysis.ObservationRoundDrawSites.chainDrawSite_success_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:39:48.099849+00:00
-- url     : https://prove2.me/submissions/c3730199-7a8f-4325-a9b7-f6056c29e95e

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
import Definitions.Def_CountingMatroid_Model_Operations
import Definitions.Def_CountingMatroid_Model_Prelude
import Definitions.Def_CountingMatroid_Model_Program
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Theorems.Thm_CountingMatroid_Analysis_BoundedUniformReplay_boundedUniform_interval_replay

namespace CountingMatroid.Meta
end CountingMatroid.Meta
namespace Arlib
end Arlib
set_option autoImplicit false

/-!
Pre-draw descriptors for a chain attempt. They record the next capped draw's
cursor and denominator without reading any bits of that draw.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
end CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: A stopped chain draw has a monotone cursor and replays using
only the bits read before that draw, rather than its as-yet-unread trials.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem solution {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (state : PairedSet n) (cursor : ℕ) (site : Fin 3) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => chainDrawSite r o₁ o₂ tape s q weights state cursor site)
      Prod.fst cursor := by
  intro tape d h
  change chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d at h
  unfold chainDrawSite at h
  split at h
  · cases h
  · rename_i hhold
    split at h
    · rename_i hzero
      have hd := Option.some.inj h
      subst d
      refine ⟨by omega, ?_⟩
      intro other hagree
      have hb : other cursor = tape cursor :=
        (hagree cursor le_rfl (by omega)).symm
      simp only [chainDrawSite, hb, hhold, hzero, Bool.false_eq_true, ite_false, ite_true]
    · rename_i hzero
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨aIndex, ha, h⟩ := h
      have hA := BoundedUniformReplay.boundedUniform_interval_replay
        s.drawTrials n (cursor + 1) tape
      dsimp only at hA
      split at h
      · rename_i hone
        have hd := Option.some.inj h
        subst d
        refine ⟨(Nat.le_succ cursor).trans hA.1, ?_⟩
        intro other hagree
        have hb : other cursor = tape cursor :=
          (hagree cursor le_rfl (by dsimp only; omega)).symm
        have heq := hA.2 other (fun i hlo hhi => hagree i (by omega) hhi)
        simp only [chainDrawSite, hb, hhold, hzero, Bool.false_eq_true,
          ite_false, heq, ha, Option.bind_eq_bind, Option.bind_some, hone, ite_true]
        simp
      · rename_i hone
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨bIndex, hbIndex, a, haSel, b, hbSel, h⟩ := h
        have hB := BoundedUniformReplay.boundedUniform_interval_replay
          s.drawTrials n (boundedUniform tape s.drawTrials n (cursor + 1)).val.2 tape
        dsimp only at hB
        split at h
        · cases h
        · rename_i hkind
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨oldWeight, ho, newWeight, hn, h⟩ := h
          split at h
          · rename_i hratio
            have hd := Option.some.inj h
            subst d
            have hstop : cursor + 1 ≤
                (boundedUniform tape s.drawTrials n
                  (boundedUniform tape s.drawTrials n (cursor + 1)).val.2).val.2 :=
              hA.1.trans hB.1
            refine ⟨(Nat.le_succ cursor).trans hstop, ?_⟩
            intro other hagree
            have hb : other cursor = tape cursor :=
              (hagree cursor le_rfl (by dsimp only; omega)).symm
            have heqA := hA.2 other (fun i hlo hhi =>
              hagree i (by omega) (hhi.trans_le hB.1))
            have heqB := hB.2 other (fun i hlo hhi =>
              hagree i ((Nat.le_succ cursor).trans (hA.1.trans hlo)) hhi)
            simp only [chainDrawSite, hb, hhold, hzero, hone,
              Bool.false_eq_true, ite_false, heqA, heqB, ha, hbIndex,
              haSel, hbSel, hkind, ho, hn, hratio,
              Option.bind_eq_bind, Option.bind_some, ite_true]
          · cases h
