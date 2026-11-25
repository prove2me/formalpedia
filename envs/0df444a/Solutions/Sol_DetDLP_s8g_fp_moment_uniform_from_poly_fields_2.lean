-- Prove2me | solution 2 for DetDLP.s8g_fp_moment_uniform_from_poly_fields
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:55:58.972576+00:00
-- url     : https://prove2.me/submissions/63baacb7-5c03-4ddd-88f7-e60e45ffd1d7

import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code

theorem solution
    (nv ne : List Bool → ℕ) (src dst : List Bool → ℕ → ℕ)
    (check : List Bool × ℕ × List Bool → Bool)
    (hnv : Groundwork.PolyT nv) (hne : Groundwork.PolyT ne)
    (hvert : Groundwork.Unary fun w => nv w + ne w)
    (hedge : Groundwork.Unary fun w => ne w + ne w)
    (hsrc : Groundwork.PolyT fun z : List Bool × ℕ => src z.1 z.2)
    (hdst : Groundwork.PolyT fun z : List Bool × ℕ => dst z.1 z.2)
    (hcheck : Groundwork.PolyT check) : ∃ a : Addresses, a.Uniform :=
  ⟨⟨nv, ne, src, dst, check⟩, ⟨hnv, hne, hvert, hedge, hsrc, hdst, hcheck⟩⟩