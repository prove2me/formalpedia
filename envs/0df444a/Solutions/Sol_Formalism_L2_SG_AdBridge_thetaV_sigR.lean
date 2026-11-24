-- Prove2me | solution 1 for Formalism.L2.SG.AdBridge.thetaV_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:03:29.255853+00:00
-- url     : https://prove2.me/submissions/6c32e8bc-08f1-442b-ade8-1de9c80487b3

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_AdBridge
import Theorems.Thm_Formalism_L2_SG_AdBridge_thetaV_tmul
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.AdBridge
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.MainNotions.S (AutInst uMat)
variable (I : AutInst)
namespace Formalism.L2.SG.AdBridge
theorem _root_.solution (v : InfinitePlace I.F) (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F ⊗[I.F] I.E) :
    thetaV I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig x) =
      starRingEnd ℂ (thetaV I v x) := by
  have hv : v.IsReal := by
    first
    | exact I.cm.totReal.isReal v
    | (haveI := I.cm.totReal; exact NumberField.IsTotallyReal.isReal v)
  have hc : Continuous (InfinitePlace.Completion.extensionEmbedding v) := by
    first
    | exact (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous
    | fun_prop
  have hK : ∀ y : I.F, starRingEnd ℂ (v.embedding y) = v.embedding y := by
    intro y
    first
    | exact RingHom.congr_fun
        (NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) y
    | simpa using RingHom.congr_fun
        (NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hv)) y
  have key : ∀ c : v.Completion, starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding v c) =
      InfinitePlace.Completion.extensionEmbedding v c := by
    intro c
    first
    | (refine InfinitePlace.Completion.induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (refine (InfinitePlace.Completion.denseRange_coe (v := v)).induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (refine (InfinitePlace.Completion.denseRange_coe v).induction_on c (isClosed_eq (Complex.continuous_conj.comp hc) hc) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
    | (obtain ⟨c'⟩ := c; refine UniformSpace.Completion.induction_on c' (isClosed_eq (Complex.continuous_conj.comp (hc.comp (by fun_prop))) (hc.comp (by fun_prop))) ?_; intro y; first | (rw [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp only [InfinitePlace.Completion.extensionEmbedding_coe]; exact hK _) | (simp [InfinitePlace.Completion.extensionEmbedding_coe, hK]; done) | (simp [hK]; done))
  have hreal : ∀ a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F, starRingEnd ℂ (evV I v a) = evV I v a :=
    fun a => key (a.1 v)
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := rfl
    rw [hs, thetaV_tmul, thetaV_tmul, map_mul, hreal]
    congr 1
    exact I.cm.cmUnram.2.1 (I.φ v) y
  | add a b ha hb => simp only [map_add, ha, hb]
end Formalism.L2.SG.AdBridge
