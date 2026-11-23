-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.sat_sigma_cast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:56.128901+00:00
-- url     : https://prove2.me/submissions/bb9f8d36-e607-41ba-8896-e9172efbe0df

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementS
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SlopeBoundSaturation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPolynomial
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.GradedWeylDivisibility
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {r a b : ℕ} (h : a = b) (I : Fin b → Fin r) :
    (⟨a, fun i => I (Fin.cast h i)⟩ : (j : ℕ) × (Fin j → Fin r)) = ⟨b, I⟩ := by
  subst h; rfl
end Formalism.DworkPowerSeriesWeights
