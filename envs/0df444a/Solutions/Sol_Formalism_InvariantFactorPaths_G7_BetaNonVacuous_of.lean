-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.BetaNonVacuous_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:35:11.534117+00:00
-- url     : https://prove2.me/submissions/1fb2bdc9-a992-4ee1-bd20-1cdc4ee001cf

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hM : ModelExists) (hL : LawExists) (hG : GcIsBeta) (hU : GcUnique) :
    BetaNonVacuous := by
  intro p _ hp2
  obtain ⟨K, i1, h1, h2, h3, σ, hσ, ζ, hζ⟩ := hM p hp2
  obtain ⟨⟨F, hF⟩, -⟩ := hL K p hσ.1 hσ.2.2.1
  refine ⟨K, i1, h1, h2, h3, σ, F, Gser p 1 (σ 1), hσ, ⟨ζ, hζ⟩, hF, ?_, ?_⟩
  · exact hG K p σ hσ F hF 1 (by simp) (by simp)
  · intro h
    have h0 : (0 : MvPowerSeries (Fin 2) K) = Gser p 0 (σ 0) := by simp [Gser]
    rw [h0] at h
    exact one_ne_zero (hU K p σ hσ 1 0 (by simp) (by simp) h)
end Formalism.InvariantFactorPaths.G7
