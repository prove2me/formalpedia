-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawNumerical1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T05:04:30.127845+00:00
-- url     : https://prove2.me/submissions/9e8b7d64-cbb6-4e95-a4b3-1892cd0926f1

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked1
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (coord : Coord 40) (h : valid coord) :
    raw 1 profile1 coord≤rawProfile1 coord := (BS2_b3ba934b_Cert_40_RawOther1).2 BS2_b3ba934b_Cert_40_AChecked1 coord h
