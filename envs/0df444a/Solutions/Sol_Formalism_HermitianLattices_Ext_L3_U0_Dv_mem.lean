-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.Dv.mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:15:23.46091+00:00
-- url     : https://prove2.me/submissions/840e5888-68fd-4501-acff-81ca041bd8a2

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
theorem _root_.solution (hπ : IsUnif S π) {a : K} (ha : Dv S π a) : a ∈ S := by
  have : a = a * π⁻¹ * π := by field_simp [hπ.ne]
  rw [this]
  exact S.mul_mem ha hπ.mem
end Dv
end Formalism.HermitianLattices.Ext.L3.U0
