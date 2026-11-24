-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Node.pol_eval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:08.968428+00:00
-- url     : https://prove2.me/submissions/99f47a9c-d732-4d9a-b90b-1460b1a8f378

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
open Formalism.HermitianLattices.Ext.L3.HU.Node
namespace Formalism.HermitianLattices.Ext.L3.HU.Node
theorem _root_.solution (A B : Matrix n n K) (c : K) : (pol A B).eval c = det (c • A + B) := by
  unfold pol
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.smul_apply]
  ring
end Formalism.HermitianLattices.Ext.L3.HU.Node
