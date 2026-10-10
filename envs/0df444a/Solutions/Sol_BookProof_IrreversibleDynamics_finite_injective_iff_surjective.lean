-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.finite_injective_iff_surjective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:16:52.789515+00:00
-- url     : https://prove2.me/submissions/5dad88e8-cdfa-4382-8e09-79555386ee03

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.finite_injective_iff_surjective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [Finite α] (f : α → α) :
    Function.Injective f ↔ Function.Surjective f := Finite.injective_iff_surjective
