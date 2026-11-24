-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.Pr.ck
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:19:15.227925+00:00
-- url     : https://prove2.me/submissions/51288868-ea2c-4d94-bb4d-9fe111bb7b5f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Pr
theorem _root_.solution (hO : IsOpen O) (hcov : ∀ g ∈ GV k r, g ∈ O ∨ g ∈ UU) {m : ℕ∞} (h : Pr O UU m a Φ) :
    CkOn m (GV k r) (ap a Φ) := by
  intro g₀ hg₀
  rcases hcov g₀ hg₀ with hO' | hU'
  · refine ⟨O, fun _ => 0, hO, hO', contDiffOn_const, fun g hg hgG => ?_⟩
    show a g (Φ g) = 0
    rw [h.hz g hgG hg, map_zero]
  · obtain ⟨U₁, a', hU₁, hg₁, hc₁, he₁⟩ := h.ha g₀ hU'
    obtain ⟨U₂, Φ', hU₂, hg₂, hc₂, he₂⟩ := h.hΦ g₀ hg₀
    have hc₁' : ContDiffOn ℝ (m : WithTop ℕ∞) (fun g => (a' g).restrictScalars ℝ) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E E' ℝ ℝ).contDiff.comp_contDiffOn
        (hc₁.mono Set.inter_subset_left)
    refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩,
      hc₁'.clm_apply (hc₂.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    show a g (Φ g) = a' g (Φ' g)
    rw [he₁ g hg.1 hgG, he₂ g hg.2 hgG]
end Pr
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
