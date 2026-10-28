-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawNumerical2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:55.453374+00:00
-- url     : https://prove2.me/submissions/3b715147-24a8-4a40-b1de-4acc1b18363d

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked2
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (coord : Coord 16) (h : valid coord) :
    raw 2 profile2 coord≤rawProfile2 coord := (BS2_b3ba934b_Cert_16_RawOther2).2 BS2_b3ba934b_Cert_16_AChecked2 coord h
