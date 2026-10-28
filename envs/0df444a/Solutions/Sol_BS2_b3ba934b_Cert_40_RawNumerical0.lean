-- Prove2me | solution 1 for BS2_b3ba934b_Cert_40_RawNumerical0
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T01:15:57.346779+00:00
-- url     : https://prove2.me/submissions/8db2a79d-6584-4f20-a91c-bbb9adf759dd

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
import Theorems.Thm_BS2_b3ba934b_Cert_40_AChecked0
import Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem solution (coord : Coord 40) (h : valid coord) :
    raw 0 profile0 coord≤rawProfile0 coord := (BS2_b3ba934b_Cert_40_RawOther0).2 BS2_b3ba934b_Cert_40_AChecked0 coord h
