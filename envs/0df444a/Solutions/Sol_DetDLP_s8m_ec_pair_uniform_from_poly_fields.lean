-- Prove2me | solution 1 for DetDLP.s8m_ec_pair_uniform_from_poly_fields
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:45:51.200163+00:00
-- url     : https://prove2.me/submissions/601865f8-1c25-417d-87d0-6ce5ce14302a

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
    (hcheck : Groundwork.PolyT check) :
    ∃ a : S8G.FpMoment.Code.Addresses, a.Uniform :=
  ⟨⟨nv, ne, src, dst, check⟩, ⟨hnv, hne, hvert, hedge, hsrc, hdst, hcheck⟩⟩