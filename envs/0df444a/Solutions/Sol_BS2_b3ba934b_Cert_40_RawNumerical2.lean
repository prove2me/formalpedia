-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawNumerical2
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T06:32:02.666681+00:00
-- url     : https://prove2.me/submissions/645e52ee-0fe8-46d4-969a-8d95f4c3a28a

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked2
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther2
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (coord : Coord 40) (h : valid coord) :
    raw 2 profile2 coord≤rawProfile2 coord := (BS2_b3ba934b_Cert_40_RawOther2).2 BS2_b3ba934b_Cert_40_AChecked2 coord h
