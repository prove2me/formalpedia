-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.nat_succ_injective_not_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:18:11.142675+00:00
-- url     : https://prove2.me/submissions/fd0c8cf6-ad98-4573-9996-3061d460f635

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.nat_succ_injective_not_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution :
    Function.Injective Nat.succ ∧ ¬ Function.Surjective Nat.succ :=
  ⟨Nat.succ_injective, by
      intro h; obtain ⟨n, hn⟩ := h 0; exact Nat.succ_ne_zero n hn⟩
