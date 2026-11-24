-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_rsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:22:00.049385+00:00
-- url     : https://prove2.me/submissions/e8701db5-0ab4-4503-bc1f-6aeab8b5bb4b

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListMapSumApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComposeDifferentialOperators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial Set
open scoped ComplexConjugate ContDiff Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
theorem _root_.solution {m : ℕ∞} {b : Mat k r → ℝ} (hb : ContDiff ℝ ∞ b) {Φ : Mat k r → (Wq →L[ℂ] Wp)}
    (hΦ : CkOn m (GV k r) Φ) : CkOn m (GV k r) (fun x => b x • Φ x) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hfe⟩ := hΦ g₀ hg₀
  refine ⟨U, fun x => b x • f' x, hU, hgU, ?_, fun g hg hgv => by simp only [hfe g hg hgv]⟩
  exact ((hb.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn).smul hf'
end Formalism.FourierDecayAlt.P.MinorPolynomials
