-- Prove2me | solution 1 for Formalism.ELL.jetsCube_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:50.436861+00:00
-- url     : https://prove2.me/submissions/322ac791-522b-4b7a-9506-8e6b29b4c26e

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_chain
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_chain
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_subst_three_variable_law

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
open Formalism Formalism.ELL
namespace Formalism.ELL
theorem _root_.solution (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsCube.{u} := by
  intro K _ _ _ F φ h i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 3 := ⟨i - 3, by omega⟩
  have hI := FormalGroupCubeJets.integral_chain F hN φ h k
  rw [FormalGroupCubeJets.chain] at hI
  have := hI 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, FormalGroupCubeJets.constantCoeff_subst_three_variable_law] at this
  exact this
end Formalism.ELL
