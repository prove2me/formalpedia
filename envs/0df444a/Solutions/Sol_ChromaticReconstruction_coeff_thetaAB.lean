-- Prove2me | solution 1 for ChromaticReconstruction.coeff_thetaAB
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:33.754428+00:00
-- url     : https://prove2.me/submissions/de1de5a0-f04f-4a5e-b0a2-28b8f810e078

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
import Theorems.Thm_ChromaticReconstruction_pairMS_mk
import Theorems.Thm_ChromaticReconstruction_pairSum_mk
import Theorems.Thm_ChromaticReconstruction_theta_mk
import Theorems.Thm_ChromaticReconstruction_X_mul_fP
import Theorems.Thm_ChromaticReconstruction_coeff_mono
import Theorems.Thm_ChromaticReconstruction_killP1_X_one
attribute [local simp] ChromaticReconstruction.killP1_X_one


attribute [local simp] ChromaticReconstruction.pairMS_mk
attribute [local simp] ChromaticReconstruction.pairSum_mk
attribute [local simp] ChromaticReconstruction.theta_mk

set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (W : Multiset ℕ) (c d : ℕ) (ν : Multiset ℕ) :
    coeff (Multiset.toFinsupp ν) (thetaAB W c d) =
      (if (c + d - 1) ::ₘ (W - {c, d}) = ν then ((c + d - 2 : ℕ) : ℚ) else 0) +
      ∑ r ∈ bigWeights (W - {c, d}), if (c + d) ::ₘ lowerAt (W - {c, d}) r = ν then
        (((r - 1) * (W - {c, d}).count r : ℕ) : ℚ) else 0 := by
  unfold thetaAB
  rw [coeff_add, coeff_C_mul, coeff_mono, X_mul_fP, coeff_sum]
  congr 1
  · split_ifs <;> simp
  · refine sum_congr rfl fun r _ => ?_
    rw [coeff_C_mul, coeff_mono]
    split_ifs <;> simp
end ChromaticReconstruction
