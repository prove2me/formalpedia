-- Prove2me | solution 1 for EthierKurtz.processPast_contains_present
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:53:05.282258+00:00
-- url     : https://prove2.me/submissions/1b1063fd-4259-4b55-bda0-194423fb4152

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Defs.Basic
import Definitions.Def_auto_M04_6e37b463_processPast

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open EthierKurtz

theorem solution {E Ω : Type*} [MeasurableSpace E] [MeasurableSpace Ω] (X : ℝ≥0 → Ω → E) (s : ℝ≥0) : MeasurableSpace.comap (X s) ‹MeasurableSpace E› ≤ processPast X s := by
  simpa using
    le_iSup (fun q : Set.Iic s => MeasurableSpace.comap (X q.val) ‹MeasurableSpace E›)
      (⟨s, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic s)
