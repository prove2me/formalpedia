-- Prove2me | solution 1 for Formalism.L2.G.jW_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:31.967852+00:00
-- url     : https://prove2.me/submissions/20f7d6dd-68cf-4040-976a-15438ca58c13

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ) [NeZero n]
omit [NeZero n]
namespace Formalism.L2.G
theorem _root_.solution (x : WQ p n) (k : ℕ) : (jW p n x).coeff k = algebraMap (F1 p n) (F2 p n) (x.coeff k) :=
  WittVector.map_coeff _ _ _
end Formalism.L2.G
