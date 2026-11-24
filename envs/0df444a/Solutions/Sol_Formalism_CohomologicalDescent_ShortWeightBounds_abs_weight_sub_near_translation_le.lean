-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.abs_weight_sub_near_translation_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:36:14.211284+00:00
-- url     : https://prove2.me/submissions/cf3d5f6d-67a5-422e-be39-93b3659c8b2f

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution (P : Par) (hP : P.Hyp) {ι : Type} (W : Wts ι) (hW : W.Ok P) (τ : ι) (a : ℕ)
    (h1 : kc P ≤ a) (h2 : a < P.Nr) : |(W.U P τ a : ℝ) - W.c τ + W.e τ| ≤ P.η := by
  by_cases hb : kc P + W.j τ ≤ a ∧ a < kc P + W.j τ + P.t
  · have e := weight_on_block_eq_bot_add P hP W hW τ a hb.1 hb.2
    have hc := hW.centre τ
    have ht := hP.t_le
    have hd0 : (0 : ℝ) ≤ ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) := Nat.cast_nonneg _
    have hd1 : ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) ≤ (P.t : ℝ) - 1 := by
      have : kc P + W.j τ + P.t - 1 - a + 1 ≤ P.t := by omega
      have h3 : ((kc P + W.j τ + P.t - 1 - a + 1 : ℕ) : ℝ) ≤ (P.t : ℝ) := by exact_mod_cast this
      push_cast at h3
      linarith
    have e' : (W.U P τ a : ℝ) = (W.bot P τ : ℝ) + ((kc P + W.j τ + P.t - 1 - a : ℕ) : ℝ) := by
      rw [e]; push_cast; ring
    rw [e', abs_le]
    constructor <;> linarith
  · refine (hW.low τ a h2 ?_).2
    by_cases h3 : a < kc P + W.j τ
    · exact Or.inl ⟨h1, h3⟩
    · right
      by_contra h4
      exact hb ⟨by omega, by omega⟩
end Formalism.CohomologicalDescent.ShortWeightBounds
