-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.dv_self_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:46.037083+00:00
-- url     : https://prove2.me/submissions/b674e80f-b825-47ca-bd90-9431825e38a4

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
theorem _root_.solution (hπ : IsUnif S π) {s : K} (hs : s ∈ S) : Dv S π (π * s) := by
  unfold Dv
  have : π * s * π⁻¹ = s := by field_simp [hπ.ne]
  rw [this]
  exact hs
end Formalism.HermitianLattices.Ext.L3.U0
