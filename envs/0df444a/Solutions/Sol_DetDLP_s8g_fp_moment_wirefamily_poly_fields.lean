-- Prove2me | solution 1 for DetDLP.s8g_fp_moment_wirefamily_poly_fields
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:56:02.912894+00:00
-- url     : https://prove2.me/submissions/9ff28df1-34b7-408a-bb11-ff794259f78f

import Definitions.Def_DetDLP_S8G_FpMomentPoly
import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul

set_option autoImplicit false

open DetDLP S8G.FpMoment.Code Groundwork

attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' PolyT.const
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f

private theorem unary_zero : Unary (fun (_ : List Bool) => (0 : ℕ)) :=
  PolyT.const (List.replicate 0 ())

/-- Total constant address-field compilers (empty graph); independent of the wire family witness. -/
theorem solution (mul : w3_modMulInterface) (h : w3_polyWireFamily w3_fpQueries) :
    ∃ (nv ne : List Bool → ℕ) (src dst : List Bool → ℕ → ℕ)
      (check : List Bool × ℕ × List Bool → Bool),
      Groundwork.PolyT nv ∧ Groundwork.PolyT ne ∧
        Groundwork.PolyT (fun z : List Bool × ℕ => src z.1 z.2) ∧
        Groundwork.PolyT (fun z : List Bool × ℕ => dst z.1 z.2) ∧
        Groundwork.PolyT check ∧
        Groundwork.Unary (fun w => nv w + ne w) ∧
        Groundwork.Unary (fun w => ne w + ne w) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => false, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · simpa using unary_zero
  · simpa using unary_zero
