-- Prove2me | solution 1 for ChromaticReconstruction.coeff_thetaAB_self_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:45:58.42217+00:00
-- url     : https://prove2.me/submissions/0a39fe74-c052-4400-b51f-d28b59717ece

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pair_le_two
import Theorems.Thm_ChromaticReconstruction_coeff_thetaAB

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) {a b : ℕ}
    (hab : {a, b} ≤ W) :
    0 < coeff (Multiset.toFinsupp ((a + b - 1) ::ₘ (W - {a, b}))) (thetaAB W a b) := by
  obtain ⟨ha, hb⟩ := pair_le_two hW hab
  rw [coeff_thetaAB, if_pos rfl]
  have h1 : (0 : ℚ) < ((a + b - 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < a + b - 2)
  have h2 : (0 : ℚ) ≤ ∑ r ∈ bigWeights (W - {a, b}),
      if (a + b) ::ₘ lowerAt (W - {a, b}) r = (a + b - 1) ::ₘ (W - {a, b}) then
        (((r - 1) * (W - {a, b}).count r : ℕ) : ℚ) else 0 := by
    apply sum_nonneg
    intro r _
    split_ifs <;> positivity
  linarith
end ChromaticReconstruction
