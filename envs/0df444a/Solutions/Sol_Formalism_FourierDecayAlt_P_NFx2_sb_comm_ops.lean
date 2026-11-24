-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sb_comm_ops
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:24.175038+00:00
-- url     : https://prove2.me/submissions/d0301dab-6c35-4810-b570-a84090d0401c

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_comm_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L0 : PreLevel A P.r}
  {QQ : ℂ → Matrix (Fin 2) (Fin 2) A} {κ : (M.Ty P → ℂ) →ₐ[ℂ] A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {X : A} (hz : Commute X L0.ζ) (hzb : Commute X L0.ζb) (hc : ∀ g ∈ L0.crdOps, Commute X g) :
    ∀ g ∈ L0.ops, Commute X g := by
  have hGG : Commute X L0.GG := by
    rw [L0.GG_def]; exact (hz.mul_right hzb).sub_right (Algebra.commutes _ X).symm
  intro g hg
  simp only [PreLevel.ops, PreLevel.fns, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_range] at hg
  rcases hg with (((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | (rfl | rfl | rfl | rfl | rfl | rfl)) | ⟨i, rfl⟩) |
      ⟨i, rfl⟩
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hz
  · exact sb_comm_inv hz L0.ζ_ζi L0.ζi_ζ
  · exact hzb
  · exact sb_comm_inv hzb L0.ζb_ζbi L0.ζbi_ζb
  · exact hGG
  · exact sb_comm_inv hGG L0.GG_GGi L0.GGi_GG
  · exact hc _ (by simp [PreLevel.crdOps])
  · exact hc _ (by simp [PreLevel.crdOps])
end Formalism.FourierDecayAlt.P.NFx2
