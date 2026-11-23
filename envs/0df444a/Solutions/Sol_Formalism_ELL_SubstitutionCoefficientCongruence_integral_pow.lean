-- Prove2me | solution 1 for Formalism.ELL.SubstitutionCoefficientCongruence.integral_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:23.635682+00:00
-- url     : https://prove2.me/submissions/f938b8b4-f67b-4194-a317-efd9bd28f3ed

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_NDeriv
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_one
import Theorems.Thm_Formalism_ELL_SubstitutionCoefficientCongruence_integral_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.ELL Formalism.ELL.SubstitutionCoefficientCongruence
variable {K : Type*} [NormedField K] [IsUltrametricDist K] {σ : Type*}
namespace Formalism.ELL.SubstitutionCoefficientCongruence
theorem _root_.solution {F : MvPowerSeries σ K} (hF : Formalism.G.IntegralMv F) (n : ℕ) :
    Formalism.G.IntegralMv (F ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact integral_one
  | succ n ih => rw [pow_succ]; exact integral_mul ih hF
end Formalism.ELL.SubstitutionCoefficientCongruence
