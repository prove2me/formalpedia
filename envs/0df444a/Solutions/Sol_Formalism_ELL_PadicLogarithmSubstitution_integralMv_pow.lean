-- Prove2me | solution 1 for Formalism.ELL.PadicLogarithmSubstitution.integralMv_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:37.128076+00:00
-- url     : https://prove2.me/submissions/ab198be3-5cef-43f6-841d-b4f26d9ee3cc

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IntegralPSBserSubOne
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralMv_one
import Theorems.Thm_Formalism_ELL_PadicLogarithmSubstitution_integralMv_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.PadicLogarithmSubstitution
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicLogarithmSubstitution
theorem _root_.solution {σ : Type*} {f : MvPowerSeries σ K} (hf : IntegralMv f) (n : ℕ) :
    IntegralMv (f ^ n) := by
  induction n with
  | zero => simpa using (integralMv_one (K := K) (σ := σ))
  | succ n ih => rw [pow_succ]; exact integralMv_mul ih hf
end Formalism.ELL.PadicLogarithmSubstitution
