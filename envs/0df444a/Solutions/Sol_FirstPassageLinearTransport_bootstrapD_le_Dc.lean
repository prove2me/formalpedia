-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapD_le_Dc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:34:33.109967+00:00
-- url     : https://prove2.me/submissions/bfe69124-940c-4571-8cd6-91cfcbe1f32d

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {chi Dc : ℝ}
    (hchi0 : 0 ≤ chi) (hchi1 : chi ≤ 1) (hDc0 : 0 ≤ Dc) (R : ℕ) :
    bootstrapD chi Dc R ≤ Dc := by
  unfold bootstrapD
  have hp : chi ^ R ≤ 1 := pow_le_one₀ hchi0 hchi1
  nlinarith [mul_le_mul_of_nonneg_left hp hDc0]
end FirstPassageLinearTransport
