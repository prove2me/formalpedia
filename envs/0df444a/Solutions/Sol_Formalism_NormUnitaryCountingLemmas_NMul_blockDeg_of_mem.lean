-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:34:10.704474+00:00
-- url     : https://prove2.me/submissions/1c035b08-00f2-4211-9415-838a0070b6f0

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_weight_blockWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul
namespace Formalism.NormUnitaryCountingLemmas.NMul
theorem _root_.solution {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) {a : Fin N × Fin n →₀ ℕ}
    (ha : a ∈ F.support) (j : Fin N) : blockDeg a j = ν j := by
  rw [mem_weightedHomogeneousSubmodule] at hF
  have := hF (mem_support_iff.1 ha)
  rw [← weight_blockWt, this]
end Formalism.NormUnitaryCountingLemmas.NMul
