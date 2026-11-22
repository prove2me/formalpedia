-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.Dv.mul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:06.409511+00:00
-- url     : https://prove2.me/submissions/74c54ad3-0945-4e5c-a83c-790253ae1c99

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AddMulInvMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0
open WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K} {π : K}
namespace Formalism.HermitianLattices.Ext.L3.U0
namespace Dv
theorem _root_.solution {a : K} (ha : Dv S π a) {s : K} (hs : s ∈ S) : Dv S π (s * a) := by
  unfold Dv
  rw [mul_assoc]
  exact S.mul_mem hs ha
end Dv
end Formalism.HermitianLattices.Ext.L3.U0
