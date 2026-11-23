-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.domConv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:42.625252+00:00
-- url     : https://prove2.me/submissions/0284618b-a561-4d98-8cf3-e4240ee1ce31

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2ConstMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_L1
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_dsMeas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_int_pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_thetaSmooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : DomConv := by
  intro hTR hTL hTB hTZ hC B S σ h4 hM hW hI4 hStar hInt Y hY hIp
  have hσ : 0 ≤ σ := by linarith
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hIg : Integrable (LE.sq B (S.d Y) (S.gX Y)) B.μ := by
    have := hIp 0
    rwa [hds0] at this
  have hmds : ∀ p k, Measurable fun ω => S.ds Y p ω k := fun p k => dsMeas B S hM hI4 Y hY p k
  have hmg : ∀ k, Measurable fun ω => S.gX Y ω k := by
    intro k
    have := hmds 0 k
    rwa [hds0] at this
  have l1 : Tendsto (fun ε => S.Ath ε σ) (𝓝[>] 0) (𝓝 S.A0) := L1 hTR hTL B σ hσ _ hInt
  have l2 : Tendsto (fun ε => S.En ε σ Y) (𝓝[>] 0) (𝓝 (∫ ω, LE.sq B (S.d Y) (S.gX Y) ω ∂B.μ)) :=
    L1 hTR hTL B σ hσ _ hIg
  have l3 : ∀ p, p ≠ 0 → Tendsto (fun ε => S.term ε σ Y p) (𝓝[>] 0) (𝓝 0) := by
    intro p hp
    have := (L2 thetaSmooth hTR hTL hTB hC B σ h4 p hp _ (int_pr B (S.d Y) hd (S.gX Y) (S.ds Y p)
      ((hM.2.2 Y hY).1) hmg (hmds p) hIg (hIp p))).div_const (p.factorial : ℂ)
    simpa [Step.term] using this
  have lsum : Tendsto (fun ε => ∑ p ∈ range (S.r + 2), S.term ε σ Y p) (𝓝[>] 0)
      (𝓝 (∑ p ∈ range (S.r + 2), if p = 0 then ((∫ ω, LE.sq B (S.d Y) (S.gX Y) ω ∂B.μ : ℝ) : ℂ) else 0)) := by
    apply tendsto_finset_sum
    intro p _
    by_cases hp : p = 0
    · subst hp
      simp only [if_true]
      simp_rw [hTZ B S _ σ Y]
      exact (Complex.continuous_ofReal.tendsto _).comp l2
    · rw [if_neg hp]; exact l3 p hp
  have llhs : Tendsto (fun ε => ((|S.P Y| * S.Ath ε σ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((|S.P Y| * S.A0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (l1.const_mul _)
  have heq : (fun ε => ((|S.P Y| * S.Ath ε σ : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      fun ε => ∑ p ∈ range (S.r + 2), S.term ε σ Y p := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hStar ε hε Y hY
  have hfin := tendsto_nhds_unique (llhs.congr' heq) lsum
  rw [Finset.sum_ite_eq' (range (S.r + 2)) 0, if_pos (by simp)] at hfin
  exact_mod_cast hfin.symm
end Formalism.FourierDecayAlt.P.LEx1
