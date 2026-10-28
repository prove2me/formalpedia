-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_Cases3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:32:57.253744+00:00
-- url     : https://prove2.me/submissions/f857e523-72ae-4d39-a5a6-fead528c4a77

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Definitions.Def_BS2_b3ba934b_Cert_16_Aux3
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution : ∀ i j : Fin 16, i≤j →
    0<(recipe 3 j).tolerance → (recipe 3 j).tolerance≤2 →
    recipe 3 i=recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).1 ∧
    recipe 3 j=recipe 3 (BS2_b3ba934b_Cert_16_Aux3.representative3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)).2 ∧
    BS2_b3ba934b_Cert_16_Aux3.representativeBound3 (BS2_b3ba934b_Cert_16_Aux3.caseIndex3 i j)≤rawProfile3 (.a i j) := by
  intro i
  fin_cases i <;> decide +kernel
