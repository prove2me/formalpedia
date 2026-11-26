-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.conditionalSeparatorProportion_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:50:30.209782+00:00
-- url     : https://prove2.me/submissions/8614b2c7-6c75-4b34-b657-079de98e25e2

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N) :
    (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) ≤
      centralSeparatorProportion N s := by
  unfold centralSeparatorProportion
  rw [Nat.cast_sub (by omega : 2 ≤ s), Nat.cast_sub (by omega : 2 ≤ N),
    Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_sub (by omega : 1 ≤ N)]
  norm_num
  have hNR : (2 : ℝ) < N := by exact_mod_cast hN
  have hdenSmall : 0 < (N : ℝ) - 2 := by linarith
  have hdenLarge : 0 < (N : ℝ) - 1 := by linarith
  apply (div_le_div_iff₀ hdenSmall hdenLarge).2
  have hsNR : (s : ℝ) ≤ N := by exact_mod_cast hsN.le
  nlinarith
end CollatzEndpointTransport.FixedTotal
