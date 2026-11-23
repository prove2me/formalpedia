-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx2.sqrt_idl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:17:22.648046+00:00
-- url     : https://prove2.me/submissions/1aa5435c-5036-4f47-b48e-6e65acbd65d0

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx2
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped nonZeroDivisors ComplexConjugate
namespace Formalism.FourierDecayAlt.P.Jx2
theorem _root_.solution (hN : S6.NormIdl) (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (μ : ℤ)
    (hg : 0 < g) : √(FractionalIdeal.absNorm (S6.idl E g (-1) (-μ)) : ℝ) =
      (((g : ℝ) * S6.rd E ^ μ) ^ S6.deg E)⁻¹ := by
  rw [hN E g (-1) (-μ) hg]
  simp only [zpow_neg, zpow_one, mul_pow, inv_pow, mul_inv]
end Formalism.FourierDecayAlt.P.Jx2
