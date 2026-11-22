-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.mul_inv_mem_of_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:18.206258+00:00
-- url     : https://prove2.me/submissions/eec3f8a3-d63f-4e88-ac90-75661aa69f2d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm

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
theorem _root_.solution (hπ : IsUnif S π) {a b : K} (ha : Dv S π a)
    (hb : IsUnitIn S (b * π⁻¹)) : a * b⁻¹ ∈ S := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb.1 (zero_mul _)
  have e : a * b⁻¹ = (a * π⁻¹) * (b * π⁻¹)⁻¹ := by
    rw [mul_inv, inv_inv]
    field_simp [hπ.ne]
  rw [e]
  exact S.mul_mem ha hb.2.2
end Formalism.HermitianLattices.Ext.L3.U0
