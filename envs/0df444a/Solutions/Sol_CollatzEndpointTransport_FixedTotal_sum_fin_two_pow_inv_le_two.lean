-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_fin_two_pow_inv_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:20:53.382112+00:00
-- url     : https://prove2.me/submissions/5ad202b2-538f-419b-b95c-7e775a48c01a

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (M : ℕ) :
    (∑ u : Fin M, ((2 : ℝ) ^ (u : ℕ))⁻¹) ≤ 2 := by
  rw [Fin.sum_univ_eq_sum_range
    (fun u : ℕ => ((2 : ℝ) ^ u)⁻¹) M]
  have hinv (u : ℕ) : ((2 : ℝ) ^ u)⁻¹ = (1 / 2 : ℝ) ^ u := by
    rw [← inv_pow]
    norm_num
  simp_rw [hinv]
  have hgeom := geom_sum_mul_neg (1 / 2 : ℝ) M
  have hpow0 : 0 ≤ (1 / 2 : ℝ) ^ M := pow_nonneg (by norm_num) _
  nlinarith
end CollatzEndpointTransport.FixedTotal
