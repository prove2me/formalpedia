-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.Node.pol_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:09.15822+00:00
-- url     : https://prove2.me/submissions/b8ed01cc-bd84-440d-94dd-6feb429f83eb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe

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
theorem _root_.solution (A B : Matrix n n K) : (pol A B).natDegree ≤ Fintype.card n :=
  Polynomial.natDegree_det_X_add_C_le A B
end Formalism.HermitianLattices.Ext.L3.HU.Node
