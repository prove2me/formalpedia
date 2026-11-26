-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_rpow_one_add_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:29:18.122984+00:00
-- url     : https://prove2.me/submissions/8471f870-a4df-4a7d-a8c3-249ec6584209

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {ι : Type*} (U : Finset ι) (a : ι → ℕ)
    {theta : ℝ} (htheta : 0 < theta) :
    ((∑ i ∈ U, a i : ℕ) : ℝ) ^ (1 + theta) ≤
      (U.card : ℝ) ^ theta *
        ∑ i ∈ U, ((a i : ℝ) ^ (1 + theta)) := by
  have hpow :=
    Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg
      (s := U) (f := fun i => (a i : ℝ))
      (p := 1 + theta) (by linarith)
      (by intro i hi; positivity)
  norm_num at hpow ⊢
  convert hpow using 1 <;> ring
end CollatzEndpointTransport.FixedTotal
