-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.comp_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:59.6071+00:00
-- url     : https://prove2.me/submissions/8fe67d87-c2d1-4ab5-be3b-e6d3fd9bfbcd

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
theorem _root_.solution {q n : ℕ} {g : F → G} {f : E → F} {u : E} (hg : ContDiffAt ℝ q g (f u))
    (hf : ContDiffAt ℝ q f u) (hn : n ≤ q) {C D : ℝ} (hC : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i g (f u)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i f u‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ n (g ∘ f) u‖ ≤ n.factorial * C * D ^ n := by
  obtain ⟨T, hT, hfu, hcT⟩ := exists_open_contDiffOn hg
  obtain ⟨U₁, hU₁, hu₁, hc₁⟩ := exists_open_contDiffOn hf
  have hU : IsOpen (U₁ ∩ f ⁻¹' T) := hc₁.continuousOn.isOpen_inter_preimage hU₁ hT
  have hu : u ∈ U₁ ∩ f ⁻¹' T := ⟨hu₁, hfu⟩
  have key := norm_iteratedFDerivWithin_comp_le (n := n) (x := u) (C := C) (D := D) hcT
    (hc₁.mono Set.inter_subset_left) (by exact_mod_cast hn) hT.uniqueDiffOn hU.uniqueDiffOn
    (fun v hv => hv.2) hu
    (fun i hi => by rw [iteratedFDerivWithin_of_isOpen _ hT hfu]; exact hC i hi)
    (fun i h1 hi => by rw [iteratedFDerivWithin_of_isOpen _ hU hu]; exact hD i h1 hi)
  rwa [iteratedFDerivWithin_of_isOpen _ hU hu] at key
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
