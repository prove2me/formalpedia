-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.not_inv_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:39.01256+00:00
-- url     : https://prove2.me/submissions/9d37ec31-a77f-4306-90cb-c1e7ac2b626d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_unit_not_dv


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
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}
namespace Formalism.HermitianLattices.Ext.L3.U0
theorem _root_.solution (hπ : IsUnif S π) : π⁻¹ ∉ S := by
  intro hinv
  refine unit_not_dv hπ ⟨hπ.ne, hπ.mem, hinv⟩ ?_
  show π * π⁻¹ ∈ S
  rw [mul_inv_cancel₀ hπ.ne]
  exact S.one_mem
end Formalism.HermitianLattices.Ext.L3.U0
