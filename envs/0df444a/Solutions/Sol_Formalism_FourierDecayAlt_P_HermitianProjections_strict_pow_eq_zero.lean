-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianProjections.strict_pow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:40:57.734367+00:00
-- url     : https://prove2.me/submissions/1ff058b5-09a5-4d05-ab4d-0f394f57a716

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormBasics
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_strict_pow_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianProjections
namespace Formalism.FourierDecayAlt.P.HermitianProjections
theorem _root_.solution {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (hM : ∀ i j : Fin m, j ≤ i → M i j = 0) :
    M ^ m = 0 := by
  ext i j
  rw [Matrix.zero_apply]
  exact strict_pow_apply M hM m i j (by have := j.isLt; omega)
end Formalism.FourierDecayAlt.P.HermitianProjections
