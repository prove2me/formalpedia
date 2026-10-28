-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawNumerical3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:37:04.825978+00:00
-- url     : https://prove2.me/submissions/03022166-84fe-4989-b9f5-32f7f0a3a43f

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked3
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (coord : Coord 16) (h : valid coord) :
    raw 3 profile3 coord≤rawProfile3 coord := (BS2_b3ba934b_Cert_16_RawOther3).2 BS2_b3ba934b_Cert_16_AChecked3 coord h
