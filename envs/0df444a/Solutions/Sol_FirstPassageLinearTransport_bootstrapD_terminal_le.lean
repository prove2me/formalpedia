-- Prove2me | solution 1 for FirstPassageLinearTransport.bootstrapD_terminal_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:19.420424+00:00
-- url     : https://prove2.me/submissions/9f8fad8a-afac-4221-ae1b-a04c678aef50

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_Bootstrap

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {chi Dc : ℝ} {j R : ℕ}
    (hchi0 : 0 ≤ chi) (hchi1 : chi ≤ 1) (hDc0 : 0 ≤ Dc)
    (hjR : j ≤ R) :
    bootstrapD chi Dc R ≤ bootstrapD chi Dc j := by
  unfold bootstrapD
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hchi0 hchi1 hjR) hDc0
end FirstPassageLinearTransport
