-- Prove2me | solution 2 for DetDLP.s8m_ec_pair_wirefamily_to_addresses
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:24:52.974933+00:00
-- url     : https://prove2.me/submissions/000588cb-d02e-4c0c-83e9-d736ab63cddd

import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8m_ec_pair_wirefamily_poly_fields
import Theorems.Thm_DetDLP_s8m_ec_pair_uniform_from_poly_fields

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code

theorem solution (mul : w3_modMulInterface) (h : w3_polyWireFamily w3_ecQueries) :
    ∃ a : S8G.FpMoment.Code.Addresses, a.Uniform := by
  obtain ⟨nv, ne, src, dst, check, hnv, hne, hsrc, hdst, hchk, hvert, hedge⟩ :=
    s8m_ec_pair_wirefamily_poly_fields mul h
  obtain ⟨a, ha⟩ :=
    s8m_ec_pair_uniform_from_poly_fields nv ne src dst check hnv hne hvert hedge hsrc hdst hchk
  exact ⟨a, ha⟩