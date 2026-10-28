-- Prove2me | solution 1 for BS2_b3ba934b_Cert_16_RawNumerical1
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T20:36:55.423766+00:00
-- url     : https://prove2.me/submissions/c6e149f8-7563-4717-8f8f-d00e195522e0

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
import Theorems.Thm_BS2_b3ba934b_Cert_16_AChecked1
import Theorems.Thm_BS2_b3ba934b_Cert_16_RawOther1
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem solution (coord : Coord 16) (h : valid coord) :
    raw 1 profile1 coord≤rawProfile1 coord := (BS2_b3ba934b_Cert_16_RawOther1).2 BS2_b3ba934b_Cert_16_AChecked1 coord h
