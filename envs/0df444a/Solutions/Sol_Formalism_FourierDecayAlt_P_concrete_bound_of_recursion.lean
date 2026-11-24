-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.concrete_bound_of_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:47:52.541503+00:00
-- url     : https://prove2.me/submissions/804c0d5c-1fef-4bea-a955-4bf5c021ad4d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstNormRealNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonSummationDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PoissonJointFirstReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalConditionsAndQuotientSplitting
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConcreteBoundOfRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.TheoremAConcreteOfParts := by
  intro hTA hPT hPJ hPSJ hRI C₁ C₄ hC₁ hC₄
  obtain ⟨C, C', hCC⟩ := hTA C₁ C₄ hC₁ hC₄
  refine ⟨C, C', ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ S jv cE Kr hK0 Th e Θ H _ _ _ Vt c hf hg1 hg2 hΘ hC'Θ hsmall hSz hP hG hI hP1
    hP23 hT hLE _ hPG hKr hA2 hEB hDom hLS hA4 R
  obtain ⟨hGram, hWP, hWave, hPI, hLift, hBlock, hE, hCut⟩ :=
    hRI E Wp Wq S jv H Vt C₄ hg1 hg2 hP hG hI hP1 hP23 hT hLE hPG Kr hK0 Th e
  obtain ⟨V, _, _, _, _, _, ι, _, π, Λ, hD, hZ, emb, dmap, hbij, hFr, hWF⟩ := hPI
  have hPS : (S.mkData Kr hK0 Th e).PoissonStep :=
    @hPSJ hPT hPJ E S.W _ (S.mkData Kr hK0 Th e) V _ _ _ _ _ ι _ π hbij Λ hD hZ emb dmap hFr hWF
  have hr : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 1 := by
    rcases le_or_gt 0 ((C / Θ) ^ S.f) with hx | hx
    · nlinarith
    · have : (S.G.r : ℝ) * (C / Θ) ^ S.f ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hx.le
      linarith
  have hK : 4 ≤ (S.mkData Kr hK0 Th e).K := by
    show 4 ≤ Kst
    unfold Kst
    norm_num
  exact hCC E S.W (S.mkData Kr hK0 Th e) Θ (∏ v, jv v) H Vt c hK hf hΘ hC'Θ hr hSz hGram hKr hWP hA2 hEB hDom
    hWave hPS hLift hBlock hLS hE hCut hA4 R
end Formalism.FourierDecayAlt.P
