-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.bilin_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:46.728924+00:00
-- url     : https://prove2.me/submissions/581783bf-ef17-4e1b-a37e-583263f80d52

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_exists_open_contDiffOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_StandardCharacterExists_key


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Filter Topology
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution (B : F →L[ℝ] G →L[ℝ] H) (hB : ‖B‖ ≤ 1) {q : ℕ} {f : E → F} {g : E → G} {u : E}
    (hf : ContDiffAt ℝ q f u) (hg : ContDiffAt ℝ q g u) {n : ℕ} (hn : n ≤ q) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) u‖ ≤
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f u‖ * ‖iteratedFDeriv ℝ (n - i) g u‖ := by
  obtain ⟨U₁, hU₁, hu₁, hc₁⟩ := exists_open_contDiffOn hf
  obtain ⟨U₂, hU₂, hu₂, hc₂⟩ := exists_open_contDiffOn hg
  have hU : IsOpen (U₁ ∩ U₂) := hU₁.inter hU₂
  have hu : u ∈ U₁ ∩ U₂ := ⟨hu₁, hu₂⟩
  have key := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one (hc₁.mono Set.inter_subset_left)
    (hc₂.mono Set.inter_subset_right) hU.uniqueDiffOn hu (n := n) (by exact_mod_cast hn) hB
  simpa only [iteratedFDerivWithin_of_isOpen _ hU hu] using key
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
