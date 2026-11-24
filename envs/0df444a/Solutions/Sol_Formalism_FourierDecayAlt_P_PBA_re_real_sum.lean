-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.re_real_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:12:43.148258+00:00
-- url     : https://prove2.me/submissions/fbb3946c-4a81-47aa-9d21-d09478a1c509

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution {W : Type} (c : ℝ) (Ws : Finset W) (p : W → ℝ) (N : W → ℂ) :
    ((c : ℂ) * ∑ w ∈ Ws, (p w : ℂ) * N w).re = c * ∑ w ∈ Ws, p w * (N w).re := by
  rw [Complex.re_ofReal_mul, Complex.re_sum]
  simp only [Complex.re_ofReal_mul]
end Formalism.FourierDecayAlt.P.PBA
