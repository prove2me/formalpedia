-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux10.ALd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:17:10.56578+00:00
-- url     : https://prove2.me/submissions/74220920-452d-4596-b212-678571c497e4

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleyTransformPreservesForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
open MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux10
variable {𝔤 E : Type*} [NormedAddCommGroup 𝔤] [NormedSpace ℝ 𝔤] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]
namespace Formalism.FourierDecayAlt.P.Ux10
theorem _root_.solution {Ω : Set 𝔤} (hΩ : IsOpen Ω) (a : ι → 𝔤 → (𝔤 →L[ℝ] ℝ))
    (ha : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (a i) Ω) :
    ∀ (m : ℕ) (L : List ι → 𝔤 → E),
      (∀ w : List ι, w.length ≤ m → ContinuousOn (L w) Ω) →
      (∀ w : List ι, w.length < m → ∀ Y ∈ Ω, HasFDerivAt (L w) (∑ i, (a i Y).smulRight (L (i :: w) Y)) Y) →
      ContDiffOn ℝ (m : WithTop ℕ∞) (L []) Ω := by
  intro m
  induction m with
  | zero =>
    intro L hc _
    rw [Nat.cast_zero, contDiffOn_zero]
    exact hc [] le_rfl
  | succ m ih =>
    intro L hc hd
    have hL : ∀ j : ι, ContDiffOn ℝ (m : WithTop ℕ∞) (L [j]) Ω := by
      intro j
      have := ih (fun w => L (w ++ [j])) (fun w hw => hc _ (by simp; omega))
        (fun w hw Y hY => by simpa using hd (w ++ [j]) (by simp; omega) Y hY)
      simpa using this
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun Y hY => (hd [] (by simp) Y hY).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have hcd : ContDiffOn ℝ (m : WithTop ℕ∞) (fun Y => ∑ i, (a i Y).smulRight (L [i] Y)) Ω :=
      ContDiffOn.sum fun i _ => ((ha i).of_le (by exact_mod_cast le_top)).smulRight (hL i)
    exact hcd.congr fun Y hY => (hd [] (by simp) Y hY).fderiv
end Formalism.FourierDecayAlt.P.Ux10
