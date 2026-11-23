-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.noConst_Psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:40.099698+00:00
-- url     : https://prove2.me/submissions/c2607b1c-6001-490c-a20b-f15b05104918

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_Psi
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_noConst_zvec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution (t : C → MvPowerSeries Z k) : NoConst (D.Psi t) := by
  intro b A hA
  have h0 : A.degree = 0 := by omega
  rw [coeff_Psi, h0, D.noConst_zvec b A hA]
  simp
end Formalism.BaseCaseIdentities.Data
