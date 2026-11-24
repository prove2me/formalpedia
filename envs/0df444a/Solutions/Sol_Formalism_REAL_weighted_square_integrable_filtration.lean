-- Prove2me | solution 1 for Formalism.REAL.weighted_square_integrable_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:07:10.127597+00:00
-- url     : https://prove2.me/submissions/efb854c0-48ac-43ff-93a6-f460867ee000

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_integrable_lie_derivative_weighted
import Theorems.Thm_Formalism_REAL_signedCasimir_quotient_mk
import Theorems.Thm_Formalism_REAL_word_action_quotient_mk
import Theorems.Thm_Formalism_REAL_word_mem_filtration
import Theorems.Thm_Formalism_REAL_signedCasimir_preserves_filtration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool}
namespace Formalism.REAL
theorem _root_.solution (hl : HhLip) (hz : IntRdZero) {W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → ℂ)}
    {c : ℂ} {a : ℝ} (ha : 0 ≤ a) (hsm : ∀ w ∈ W, SmoothOnG ε w)
    (hstab : ∀ w ∈ W, ∀ i j : Fin n, ε i = ε j → ∃ w' ∈ W, ∀ g, inUJ ε g → Eab ε i j w g = w' g)
    (hcas : ∀ w ∈ W, ∀ g, inUJ ε g → CasF ε w g = c * w g)
    (hint : ∀ w ∈ W, Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖w (toM g)‖ ^ 2)
      (muG ε)) :
    ∀ k : ℕ, ∀ w : List (Fin n × Fin n), w.length ≤ k → ∀ f ∈ W,
      Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) * ‖Eword ε w f (toM g)‖ ^ 2)
        (muG ε) := by
  intro k
  induction k with
  | zero =>
    intro w hw f hf
    have : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact hint f hf
  | succ k ih =>
    intro w hw f hf
    cases w with
    | nil => exact hint f hf
    | cons p w' =>
      have hw' : w'.length ≤ k := by simp at hw; omega
      have hu := smooth_iterated_lie_derivative (hsm f hf) w'
      have hu2 := ih w' hw' f hf
      have hVG : wordFiltration ε W k ≤ weightedSquareIntegrable ε a := by
        refine Submodule.span_le.2 ?_
        rintro x ⟨w'', m, ⟨f'', hf''W, hf'', rfl⟩, hw'', rfl⟩
        show Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖evalQuotient ε (wordActionQuotient ε w'' (quotientMkAlt ⟨f'', hf''⟩)) g‖ ^ 2) (muG ε)
        rw [word_action_quotient_mk, evalQuotient_mk]
        exact ih w'' hw'' f'' hf''W
      have hx : wordActionQuotient ε w' (quotientMkAlt ⟨f, hsm f hf⟩) ∈ wordFiltration ε W k :=
        word_mem_filtration ⟨f, hf, hsm f hf, rfl⟩ hw'
      have hT := hVG (signedCasimir_preserves_filtration hsm hstab hcas hx)
      have hT' : Integrable (fun g : UJ ε => Real.exp (2 * a * hh (toM g)) *
          ‖evalQuotient ε (signedCasimirQuotient ε (wordActionQuotient ε w' (quotientMkAlt ⟨f, hsm f hf⟩))) g‖ ^ 2) (muG ε) := hT
      rw [word_action_quotient_mk, signedCasimir_quotient_mk, evalQuotient_mk] at hT'
      exact integrable_lie_derivative_weighted hl hz ha hu hu2 hT' p.1 p.2
end Formalism.REAL
