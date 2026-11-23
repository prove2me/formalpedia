-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx6.maj_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:44.123175+00:00
-- url     : https://prove2.me/submissions/5eceb8d1-17f0-4c36-859e-3c557edc116a

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionGivesUniformBoundsForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexConjugate ComplexOrder Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx6
namespace Formalism.FourierDecayAlt.P.Jx6
theorem _root_.solution {E W : Type} [Field E] (D : TB.Data E W) (ρ ρ' : Fin D.f → ℝ) (l : E)
    (h : ∀ v, 0 ≤ ρ v ∧ ρ v ≤ ρ' v) (hav : ∀ v, 0 ≤ D.av v l) : D.maj ρ l ≤ D.maj ρ' l := by
  unfold TB.Data.maj
  apply Finset.prod_le_prod
  · intro v _
    exact le_min zero_le_one (pow_nonneg (div_nonneg (h v).1 (hav v)) _)
  · intro v _
    exact min_le_min le_rfl (pow_le_pow_left₀ (div_nonneg (h v).1 (hav v))
      (div_le_div_of_nonneg_right (h v).2 (hav v)) _)
end Formalism.FourierDecayAlt.P.Jx6
