-- Prove2me | solution 1 for EdenVerified.s02_index_and_sums
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:56:01.99307+00:00
-- url     : https://prove2.me/submissions/973cf6f9-efa4-4b1b-8b55-6c46fe9098bf

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
import Theorems.Thm_Eden_commonIndexCandidates_isLeast
import Theorems.Thm_Eden_commonIndex_eq_four
import Theorems.Thm_Eden_exponentSum_five_isGreatest
import Theorems.Thm_Eden_exponentSum_four_isGreatest
import Theorems.Thm_Eden_lyapunovExponent_fifth


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified
namespace EdenVerified
theorem _root_.solution (c : ℝ) (hc : 4 < c) :
    IsLeast (commonIndexCandidates c) 4 ∧ commonIndex c = 4 ∧
    (∀ p : PhaseSpace, lyapunovExponent c p 4 = -c) ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 4) '' attractor) 4 ∧
    IsGreatest ((fun p => spectrumPartialSum (lyapunovExponent c p) 5) '' attractor) (4-c) ∧
    4-c < 0 :=
  ⟨commonIndexCandidates_isLeast hc, commonIndex_eq_four hc, lyapunovExponent_fifth hc,
    exponentSum_four_isGreatest hc, exponentSum_five_isGreatest hc, by linarith⟩
end EdenVerified
