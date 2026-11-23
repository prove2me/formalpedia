-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x3.perp_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:09.936866+00:00
-- url     : https://prove2.me/submissions/ce63ea24-e7d8-4a59-9651-b1e19b4bcfff

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_perp
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_mem_mulLat
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3
variable {K : Type} [CommRing K] {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x3
theorem _root_.solution (b : Kˣ) (L : AddSubgroup K) :
    perp ψ (mulLat (b : K) L) = mulLat ((b⁻¹ : Kˣ) : K) (perp ψ L) := by
  ext a
  rw [mem_mulLat, inv_inv, mem_perp, mem_perp]
  constructor
  · intro h l hl
    have := h ((b : K) * l) ⟨l, hl, rfl⟩
    rwa [show a * ((b : K) * l) = (b : K) * a * l by ring] at this
  · rintro h _ ⟨l, hl, rfl⟩
    have := h l hl
    rwa [show (b : K) * a * l = a * (AddMonoidHom.mulLeft (b : K) l) by
      simp only [AddMonoidHom.coe_mulLeft]; ring] at this
end Formalism.FourierDecayAlt.P.A6x3
