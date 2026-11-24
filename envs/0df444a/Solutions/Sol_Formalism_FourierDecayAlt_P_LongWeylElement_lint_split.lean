-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LongWeylElement.lint_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:52:59.792817+00:00
-- url     : https://prove2.me/submissions/8cfb0de5-19a4-4a30-9f1c-75e494f66e5e

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianLeviVectorBaseOrthogonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_splitE_mp
import Theorems.Thm_Formalism_FourierDecayAlt_P_LongWeylElement_splitE_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LongWeylElement
namespace Formalism.FourierDecayAlt.P.LongWeylElement
theorem _root_.solution (r' : ℕ) (G : ℂ × (Fin r' → ℂ) → ℝ≥0∞) :
    ∫⁻ c : Fin (1 + r') → ℂ, G (splitC r' c) = ∫⁻ p : ℂ × (Fin r' → ℂ), G p := by
  rw [← splitE_eq r']
  exact (splitE_mp r').lintegral_comp_emb (splitE r').measurableEmbedding G
end Formalism.FourierDecayAlt.P.LongWeylElement
