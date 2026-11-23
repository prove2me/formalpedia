-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx3.sqrt_disc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:49:48.237171+00:00
-- url     : https://prove2.me/submissions/d70dfd15-afe2-482e-afe4-872016e65f26

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Lemmata_FiberEquations_FiberEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualCovolumeChangeOfVariables

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J Module
open scoped ComplexConjugate nonZeroDivisors
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx3
namespace Formalism.FourierDecayAlt.P.Jx3
theorem _root_.solution (hD : S6.DegreeFacts) (E : Type) [Field E] [NumberField E] [IsCMField E] :
    √((|discr E| : ℤ) : ℝ) = S6.rd E ^ S6.deg E := by
  obtain ⟨h1, -, h3⟩ := hD E
  have hd : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  unfold S6.rd
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd, h1, Real.sqrt_eq_rpow]
  congr 1
  have : (S6.deg E : ℝ) ≠ 0 := by exact_mod_cast h3.ne'
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.Jx3
