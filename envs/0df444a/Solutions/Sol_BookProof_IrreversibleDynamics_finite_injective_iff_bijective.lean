-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.finite_injective_iff_bijective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:16:53.930055+00:00
-- url     : https://prove2.me/submissions/58820023-620a-4713-81ec-7ab1046cab89

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.finite_injective_iff_bijective
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [Finite α] (f : α → α) :
    Function.Injective f ↔ Function.Bijective f := Finite.injective_iff_bijective
