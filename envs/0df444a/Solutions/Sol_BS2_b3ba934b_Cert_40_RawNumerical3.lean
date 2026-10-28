-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawNumerical3
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T07:33:17.690541+00:00
-- url     : https://prove2.me/submissions/0a352d35-b4d0-4cc2-a881-42c874720f5c

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked3
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther3
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (coord : Coord 40) (h : valid coord) :
    raw 3 profile3 coord≤rawProfile3 coord := (BS2_b3ba934b_Cert_40_RawOther3).2 BS2_b3ba934b_Cert_40_AChecked3 coord h
