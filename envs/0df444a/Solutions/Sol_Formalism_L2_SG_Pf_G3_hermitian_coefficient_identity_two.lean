-- Prove2me | solution 1 for Formalism.L2.SG.Pf.G3.hermitian_coefficient_identity_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:30.549891+00:00
-- url     : https://prove2.me/submissions/068564d3-b2d9-421e-aab2-02e112268a38

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanSSelf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_HermitianCoefficientIdentityOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}
namespace Formalism.L2.SG.Pf.G3
theorem _root_.solution {A B D α β : K} (hA : A ≠ 0) (hD : D ≠ 0)
    (hDdef : D = star α * α * A + star β * β * B) :
    A * D⁻¹ * (star β * (B * A⁻¹) * β + α * star α) = 1 := by
  have hAA : A * A⁻¹ = 1 := mul_inv_cancel₀ hA
  have e : A * (star β * (B * A⁻¹) * β + α * star α) = D := by
    rw [hDdef]
    linear_combination (star β * β * B) * hAA
  calc A * D⁻¹ * (star β * (B * A⁻¹) * β + α * star α)
      = D⁻¹ * (A * (star β * (B * A⁻¹) * β + α * star α)) := by ring
    _ = 1 := by rw [e, inv_mul_cancel₀ hD]
end Formalism.L2.SG.Pf.G3
