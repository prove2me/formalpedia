-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.three_variable_law_eq_subst_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:47.083131+00:00
-- url     : https://prove2.me/submissions/dbd79375-e6d9-4550-ab1b-c37da8b91954

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_hsX
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_two_variable_law
import Theorems.Thm_Formalism_G_isCommOfRat


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
theorem _root_.solution : F3 F = (FK F).toPowerSeries.subst ![F2 F 1 2, MvPowerSeries.X 0] := by
  have : (FK F).IsComm := Formalism.G.isCommOfRat K (FK F)
  have e1 := (FK F).assoc' (hsX (K := K) 0) (hsX 1) (hsX 2)
  have h12 : PowerSeries.HasSubst (F2 F 1 2) := PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_two_variable_law F 1 2)
  have c := (FK F).comm' (hsX (K := K) 0) h12
  rw [F3, F2]
  simp only [Y3]
  rw [e1]
  exact c
end Formalism.ELL.FormalGroupCubeJets
