-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.U0.IsSD.exists_not_dv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:16.488486+00:00
-- url     : https://prove2.me/submissions/6a2307f3-be39-4111-b6d8-1df08f91c4eb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormRepresentation
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsPrimitiveNorm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_not_inv_mem

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
namespace IsSD
theorem _root_.solution (hπ : IsUnif S π) (hM : IsSD S h W M) {y : V} (hy : y ∈ M)
    (hprim : ∀ c : K, c • y ∈ M → c ∈ S) : ∃ w ∈ M, ¬ Dv S π (h w y) := by
  by_contra hcon
  push_neg at hcon
  have hmem : π⁻¹ • y ∈ M := hM.dual _ (W.smul_mem _ (hM.le y hy)) (fun m hm => by
    rw [map_smul, smul_eq_mul, mul_comm]
    exact hcon m hm)
  exact not_inv_mem hπ (hprim _ hmem)
end IsSD
end Formalism.HermitianLattices.Ext.L3.U0
