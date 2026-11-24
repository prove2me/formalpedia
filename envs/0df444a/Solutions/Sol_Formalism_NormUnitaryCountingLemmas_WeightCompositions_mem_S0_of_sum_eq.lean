-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.WeightCompositions.mem_S0_of_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:43.645262+00:00
-- url     : https://prove2.me/submissions/27dd0d73-7dec-4f23-937e-df4911784015

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShearCoefficients
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_LtSuccOfMemWeightCompositions

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
universe u
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.WeightCompositions
variable {N n : ℕ}
variable {K : Type u} [Field K] (ν : Fin N → ℕ)
namespace Formalism.NormUnitaryCountingLemmas.WeightCompositions
theorem _root_.solution {s : ℕ} {w : Fin n → ℕ} (h : ∑ k, w k = s) : w ∈ S0 n s := by
  simp only [S0, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  refine ⟨fun k => ?_, h⟩
  rw [← h]
  exact Nat.lt_succ_of_le (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
end Formalism.NormUnitaryCountingLemmas.WeightCompositions
