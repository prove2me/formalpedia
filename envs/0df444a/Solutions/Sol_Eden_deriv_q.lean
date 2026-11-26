-- Prove2me | solution 1 for Eden.deriv_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:21:04.385075+00:00
-- url     : https://prove2.me/submissions/382a7fe2-e986-4833-9beb-0764fb01884d

import Definitions.Def_Eden_CartesianDerivative
import Mathlib.LinearAlgebra.Trace
import Definitions.Def_Eden_VectorFieldDerivative
import Theorems.Thm_Eden_hasDerivAt_q

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (s : ℝ) : deriv q s = -2 * s + 3 := (hasDerivAt_q s).deriv
end Eden
