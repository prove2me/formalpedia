-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.integral_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:43.156866+00:00
-- url     : https://prove2.me/submissions/b68551f2-1b40-40d8-9fcc-72eba982d530

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_mul
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_omegaX
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_Dj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution (hN : NPderiv.{u}) (φ : PowerSeries K) (h : InN (triDiff F φ)) (k : ℕ) :
    IntegralMv ((Dj F 0)^[k] (Dj F 0 (Dj F 1 (Dj F 2 (triDiff F φ))))) := by
  have h2 : IntegralMv (Dj F 2 (triDiff F φ)) :=
    integral_mul (integral_omegaX F 2) (hN K (Fin 3) _ h 2)
  have h0 := integral_Dj F 0 (integral_Dj F 1 h2)
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact integral_Dj F 0 ih
end Formalism.ELL.FormalGroupCubeJets
