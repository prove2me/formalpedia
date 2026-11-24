-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.sum_Ico_tsub_telescope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:00.806645+00:00
-- url     : https://prove2.me/submissions/92a7a44d-b5fd-4e1d-8f4c-40cb3febe2bc

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (g : ℕ → ℕ) (n : ℕ) (hg : ∀ i, g (i + 1) ≤ g i)
    (hn : ∀ i, n ≤ i → g i = 0) :
    ∀ d k, n - k = d → ∑ i ∈ Finset.Ico k n, (g i - g (i + 1)) = g k := by
  intro d
  induction d with
  | zero =>
    intro k hk
    have hnk : n ≤ k := by omega
    rw [Finset.Ico_eq_empty_of_le hnk, Finset.sum_empty, hn k hnk]
  | succ d ih =>
    intro k hk
    have hkn : k < n := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hkn, ih (k + 1) (by omega)]
    exact Nat.sub_add_cancel (hg k)
end Formalism.GradedWeylDivisibility
