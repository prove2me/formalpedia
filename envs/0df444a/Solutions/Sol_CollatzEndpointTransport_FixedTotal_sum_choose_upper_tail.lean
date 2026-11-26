-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_choose_upper_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:11.315351+00:00
-- url     : https://prove2.me/submissions/c035cda5-4051-42b3-b097-3e32f6c04552

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_choose_lower_tail

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H K : ℕ} (hKH : K ≤ H) :
    (∑ k ∈ Finset.Ico (H - K) (H + 1), (H.choose k : ℝ)) =
      CollatzEndpointTransport.Terras.lowerBinomialSum H K := by
  calc
    (∑ k ∈ Finset.Ico (H - K) (H + 1), (H.choose k : ℝ)) =
        ∑ k ∈ Finset.Ico 0 (K + 1), (H.choose (H - k) : ℝ) := by
      symm
      simpa using
        (Finset.sum_Ico_reflect (fun k => (H.choose k : ℝ)) 0
          (show K + 1 ≤ H + 1 by omega))
    _ = ∑ k ∈ Finset.Ico 0 (K + 1), (H.choose k : ℝ) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Nat.choose_symm]
      have hkK : k ≤ K := by
        have := (Finset.mem_Ico.mp hk).2
        omega
      exact hkK.trans hKH
    _ = CollatzEndpointTransport.Terras.lowerBinomialSum H K :=
      sum_choose_lower_tail H K
end CollatzEndpointTransport.FixedTotal
