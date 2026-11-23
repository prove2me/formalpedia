-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.constantCoeff_mulN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:45.162973+00:00
-- url     : https://prove2.me/submissions/5f6ebc20-6a67-4b21-8d70-102fa1f14d3c

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
import Theorems.Thm_Formalism_ELL_PadicMultiplication_mulN_zero
import Theorems.Thm_Formalism_ELL_PadicMultiplication_mulN_succ
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


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
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {R : Type*} [CommRing R]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup R) (m : ℕ) :
    MvPowerSeries.constantCoeff (mulN F m) = 0 := by
  induction m with
  | zero => simp [mulN_zero]
  | succ m ih =>
    rw [mulN_succ]
    have := constantCoeff_subst_of_zero (R := R) F.toPowerSeries
      (b := (![mulN F m, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R))
      (fun i => by fin_cases i; exacts [ih, PowerSeries.constantCoeff_X])
    rw [F.zero_constantCoeff] at this
    exact this
end Formalism.ELL.PadicMultiplication
