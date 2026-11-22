-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.Dv.eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:06.309823+00:00
-- url     : https://prove2.me/submissions/db8a65cf-5ef1-4f90-a52d-b705e001f9e2

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
theorem _root_.solution (hπ : IsUnif S π) {a : K} (ha : Dv S π a) : ∃ r ∈ S, a = π * r :=
  ⟨a * π⁻¹, ha, by field_simp [hπ.ne]⟩
end Dv
end Formalism.HermitianLattices.Ext.L3.U0
