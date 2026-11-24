-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ListSumSplittings.ckOn_mulF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:11:08.951476+00:00
-- url     : https://prove2.me/submissions/4f1b51b4-e4b3-4993-b1c7-6956971e960f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExponentWordRecursion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ListSumSplittings
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10 Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic Formalism.FourierDecayAlt.P.ListSumInequalities
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.ListSumSplittings
theorem _root_.solution {f : Mat k r → ℂ} {H : Mat k r → E} {m : ℕ∞} (hf : CkOn m (GV k r) f)
    (hH : CkOn m (GV k r) H) : CkOn m (GV k r) (fun g => f g • H g) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hc, hff⟩ := hf g₀ hg₀
  obtain ⟨U₂, H', hU₂, hgU₂, hc₂, hff₂⟩ := hH g₀ hg₀
  refine ⟨U ∩ U₂, fun g => f' g • H' g, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hc.mono Set.inter_subset_left).smul (hc₂.mono Set.inter_subset_right), ?_⟩
  intro g hg hgG
  show f g • H g = f' g • H' g
  rw [hff g hg.1 hgG, hff₂ g hg.2 hgG]
end Formalism.FourierDecayAlt.P.ListSumSplittings
