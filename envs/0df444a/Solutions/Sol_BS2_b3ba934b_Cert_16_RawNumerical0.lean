-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawNumerical0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:33:08.426054+00:00
-- url     : https://prove2.me/submissions/d91b5de5-7176-4de8-a4a9-daccd1b839e7

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked0
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (coord : Coord 16) (h : valid coord) :
    raw 0 profile0 coord≤rawProfile0 coord := (BS2_b3ba934b_Cert_16_RawOther0).2 BS2_b3ba934b_Cert_16_AChecked0 coord h
