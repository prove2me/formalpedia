-- Prove2me | solution 1 for Formalism.L2.Th1.F.USer.goodModelLattice_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:04.387435+00:00
-- url     : https://prove2.me/submissions/6fdaea22-6489-4c0e-97d4-c0e625bf3354

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorSigma
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_SigmaScale
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_GoodModelLatticeGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism.L2.Th1.CM (wpNum wpDen uSer IsGoodModel)
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open PowerSeries TaylorWp
open Formalism.L2.Th1.F.USer
namespace Formalism.L2.Th1.F.USer
theorem _root_.solution (hh : Homogeneity) (hp : POfLattice) (hm : SeriesMap) (hs : TaylorSigma)
    (hst : TaylorSgStar) (hu : USerLattice) : GoodModelLattice := by
  intro l _ L ι g2 g3 hG
  obtain ⟨-, -, -, -, -, lam, hlam, h2, h3⟩ := hG
  obtain ⟨c, hιc⟩ : ∃ c : ℂ, ι c = lam⁻¹ := ⟨ι.symm lam⁻¹, ι.apply_symm_apply _⟩
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hιc
    exact inv_ne_zero hlam hιc.symm
  refine ⟨c, hc, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hg2, hg3⟩ := hh L c hc
  have e2 : ι (scalePair L c hc).g₂ = g2 := by
    rw [hg2, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h2.symm
  have e3 : ι (scalePair L c hc).g₃ = g3 := by
    rw [hg3, map_mul, map_inv₀, map_pow, hιc, inv_pow, inv_inv]
    exact h3.symm
  obtain ⟨-, -, hMp, hMu, hMs, hMst⟩ := hm ℂ ℂ_[l] (ι : ℂ →+* ℂ_[l]) (scalePair L c hc).g₂
    (scalePair L c hc).g₃ (s2 (scalePair L c hc)) (pSeries (scalePair L c hc))
  have e4 : PowerSeries.map (ι : ℂ →+* ℂ_[l]) (pSeries (scalePair L c hc)) = pOf g2 g3 := by
    rw [hp (scalePair L c hc), hMp]
    exact congrArg₂ pOf e2 e3
  refine ⟨e2.symm, e3.symm, e4, ?_, ?_, ?_⟩
  · rw [hs (scalePair L c hc), hMs, e4]
  · rw [hst (scalePair L c hc), hMst, e4]
    rfl
  · rw [(hu (scalePair L c hc)).2, hMu]
    exact congrArg₂ uSer e2 e3
end Formalism.L2.Th1.F.USer
