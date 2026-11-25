-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_addresses
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T14:57:06.727804+00:00
-- url     : https://prove2.me/submissions/04236355-8a5d-4684-b1ab-c9ae378cc1e3

import Definitions.Def_DetDLP_S8G_FpMomentPoly

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code Groundwork

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

private theorem unary_zero : Unary (fun (_ : W) => 0) := PolyT.const (List.replicate 0 ())

/-- Trivial uniform address map: empty graph, constant zero endpoints, check always false. -/
theorem solution : ∃ a : Addresses, a.Uniform := by
  refine ⟨{
      nv := fun _ => 0
      ne := fun _ => 0
      src := fun _ _ => 0
      dst := fun _ _ => 0
      check := fun _ => false
    }, ?_⟩
  constructor
  · fun_prop
  · fun_prop
  · simpa using unary_zero
  · simpa using unary_zero
  · fun_prop
  · fun_prop
  · fun_prop