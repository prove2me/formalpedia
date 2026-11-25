-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.ld_big
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:04:03.383919+00:00
-- url     : https://prove2.me/submissions/32ac06f0-8ae8-45cd-ac20-3dc89bbb295a

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_IsoOfIntegral
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Theorems.Thm_CompanionTheory_ThKR_LL_ld_ph
import Theorems.Thm_CompanionTheory_ThKR_LL_ld_dil
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_Intw_smul
import Theorems.Thm_CompanionTheory_ThKR_LL_Iso_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_const
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_mul
import Theorems.Thm_CompanionTheory_ThKR_LL_LD_smul
import Theorems.Thm_CompanionTheory_ThKR_LL_dil_one
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_dil
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_fou
import Theorems.Thm_CompanionTheory_ThKR_LL_iso_ph
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution {Ai B C : ℝ → Eu l →L[ℝ] Eu l} {Ai' B' C' : Eu l →L[ℝ] Eu l} {c : ℝ → ℝ} {c' t₀ : ℝ}
    (hA : HasDerivAt Ai Ai' t₀) (hB : HasDerivAt B B' t₀) (hC : HasDerivAt C C' t₀) (hc : HasDerivAt c c' t₀)
    (h : ∀ᶠ t in 𝓝 t₀, IsUnit (Ai t) ∧ c t ^ 2 = |(Ai t).det|) :
    ∃ Q, LD (fun t => big (Ai t) (B t) (C t) (c t)) Q t₀ ∧ (Ai t₀ = 1 → B t₀ = 0 → C t₀ = 0 → c t₀ = 1 → ∀ f,
      Q f = mq C' f + vf Ai' f + fou l (mq (-B') (fouInv l f)) + (c' : ℂ) • f) := by
  have h1 := (ld_ph (hA.mul hB).neg).mul (LD.const (fouInv l) t₀) (.of_forall fun t => iso_ph _)
  have h2 := (LD.const (fou l) t₀).mul h1 (.of_forall fun t => iso_fou)
  have h3 := ((ld_dil hA h.self_of_nhds.1).smul hc.ofReal_comp).mul h2 (h.mono fun t ht => iso_dil ht.1 ht.2)
  have h4 := (ld_ph (hC.mul hA)).mul h3 (.of_forall fun t => iso_ph _)
  refine ⟨_, h4, fun e1 e2 e3 e4 f => ?_⟩
  have e5 : fou l (fouInv l f) = f := by
    rw [← ContinuousLinearMap.mul_apply, fou_mul_fouInv, ContinuousLinearMap.one_apply]
  simp [e1, e2, e3, e4, ph_zero, dil_one, e5]
  abel
end CompanionTheory.ThKR.LL
