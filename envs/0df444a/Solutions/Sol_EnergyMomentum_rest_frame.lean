-- Prove2me | solution 1 for EnergyMomentum.rest_frame
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:38:59.554532+00:00
-- url     : https://prove2.me/submissions/5e6c9056-02da-46ae-a085-cfe599a1ad7f

import Mathlib
import Definitions.Def_EnergyMomentum_basic
open EnergyMomentum

theorem solution (m c : ℝ) :
    momentum m c 0 = 0 ∧ energy m c 0 = restEnergy m c ∧ restEnergy m c = m * c ^ 2 := by
  refine ⟨by simp [momentum], ?_, rfl⟩
  simp [energy, restEnergy, lorentzFactor]
