-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseNonterminalSum_eq_sum_spend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:42:55.781154+00:00
-- url     : https://prove2.me/submissions/3276db8c-d07e-4992-8162-5935ba73a95f

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseTermSum_eq_spend


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) (theta : ℝ) :
    fixedReverseNonterminalSum N s theta =
      ∑ D ∈ range (N + 1), fixedReverseSpendSum N s theta D := by
  unfold fixedReverseNonterminalSum fixedReverseSpendSum
  calc
    (∑ r ∈ Ico 1 s, fixedReverseTermSum N s theta r) =
        ∑ r ∈ Ico 1 s,
          ∑ D ∈ range (N + 1),
            ∑ d ∈ terminalPatternSet N s r D,
              (terminalFiber N s r d).card *
                realTerminalPatternTerm theta r d := by
      apply sum_congr rfl
      intro r hr
      exact fixedReverseTermSum_eq_spend N s theta r
    _ = ∑ D ∈ range (N + 1),
          ∑ r ∈ Ico 1 s,
            ∑ d ∈ terminalPatternSet N s r D,
              (terminalFiber N s r d).card *
                realTerminalPatternTerm theta r d := by
      rw [Finset.sum_comm]
end CollatzEndpointTransport.FixedTotal
