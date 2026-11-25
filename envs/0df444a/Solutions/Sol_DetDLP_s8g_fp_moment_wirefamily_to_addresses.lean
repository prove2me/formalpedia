-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_wirefamily_to_addresses
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:13:46.197302+00:00
-- url     : https://prove2.me/submissions/b32a205a-0a61-4078-ae58-e1ad67669d3d

import Definitions.Def_DetDLP_W3_ModMul
import Theorems.Thm_DetDLP_s8g_fp_moment_wirefamily_poly_fields
import Theorems.Thm_DetDLP_s8g_fp_moment_uniform_from_poly_fields

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code

theorem solution (mul : w3_modMulInterface) (h : w3_polyWireFamily w3_fpQueries) :
    ∃ a : Addresses, a.Uniform := by
  obtain ⟨nv, ne, src, dst, check, hnv, hne, hsrc, hdst, hchk, hvert, hedge⟩ :=
    s8g_fp_moment_wirefamily_poly_fields mul h
  obtain ⟨a, ha⟩ :=
    s8g_fp_moment_uniform_from_poly_fields nv ne src dst check hnv hne hvert hedge hsrc hdst hchk
  exact ⟨a, ha⟩