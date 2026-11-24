-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.core
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:51.749156+00:00
-- url     : https://prove2.me/submissions/19c2858a-3094-4d05-9332-384d646198ad

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_card_range_inf_torsion_le_index_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
open Formalism.FourierDecayAlt.G Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
theorem _root_.solution : ∃ a b : ℕ, ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (m q : ℕ) (β D : ℂ) (tt : E → ℂ)
    (xx : E → Fin (m + 1) → ℂ) (yy : E → UT (m + 2) → ℂ) (u : E) (Q W : ℝ),
    2 ^ q * ((m : ℝ) + 2) ^ 2 * q.factorial ≤ Q → DB q tt u Q 1 → (∀ k, DB q (fun v => xx v k) u Q 1) →
    (∀ e, DB q (fun v => yy v e) u Q 1) → ‖D‖ ≤ Q → ‖β‖ ≤ Q → Q ^ (4 * (m + 2)) ≤ W →
    cofXY m (tt u) (xx u, yy u) ≠ 0 → ‖cofXY m (tt u) (xx u, yy u)‖⁻¹ ≤ W →
    ∏ k, xx u k ≠ 0 → ‖∏ k, xx u k‖⁻¹ ≤ W →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Φ : Mat (m + 1 + 1) → V) (K' : ℝ),
      DB q Φ (MXY m D (tt u) (xx u, yy u)) K' 1 →
      DB q (fun v => ampE β m Φ D (tt v) (xx v, yy v)) u (K' * W ^ a) (W ^ b) :=
  ⟨11, 16, fun E _ _ m q β D tt xx yy u Q W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 V _ _ Φ K' h12 =>
    card_range_inf_torsion_le_index_pow E m q β D tt xx yy u Q W h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 V Φ K' h12⟩
end Formalism.FourierDecayAlt.P.EtaleIntegralityFacts
