-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.radical_weight_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:11.738629+00:00
-- url     : https://prove2.me/submissions/3058e575-0e79-4326-86b2-15ae027e7966

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_WtGeProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SubstitutionWeightBound
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_monoWtGe_iff
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_mono
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk29_wtGe_prod__77285e911b46


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
universe u v w
open Formalism Formalism.DworkPowerSeriesWeights
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution : RadMono.{u, v} := by
  intro K _ pi h0 h1 ι r r' wt hr
  have key : ∀ (n : ι →₀ ℕ) (c : K), MonoWtGe pi r wt n c → MonoWtGe pi r' wt n c :=
    fun n c hc => le_trans (monoWtGe_iff.mp hc)
      (Real.rpow_le_rpow_of_exponent_ge h0 h1.le (by linarith [dot_mono n hr]))
  exact ⟨fun f hf n => key n _ (hf n), fun κ f hf n hn => key n _ (hf n hn)⟩
end Formalism.DworkPowerSeriesWeights
