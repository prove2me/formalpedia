-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_wsup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:54.175386+00:00
-- url     : https://prove2.me/submissions/ee9bf7eb-20d6-4811-874a-64b56fcfd8bb

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_pow_exp_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (m : ℕ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (v : ℕ) :
    ((v : ℝ) + 1) ^ m * Real.exp (-(η * v)) ≤ Real.exp 1 * m.factorial / η ^ m := by
  have hηm : 0 < η ^ m := pow_pos hη m
  have ht : (0:ℝ) ≤ (v:ℝ) + 1 := by positivity
  have h1 := dhpr_pow_exp_le m hη.le ht
  have h2 : Real.exp (-(η * v)) ≤ Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1))) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have e : -(η * (v:ℝ)) = 1 + -(η * ((v:ℝ) + 1)) - (1 - η) := by ring
    rw [e]; linarith
  calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * v))
      ≤ ((v : ℝ) + 1) ^ m * (Real.exp 1 * Real.exp (-(η * ((v:ℝ) + 1)))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.exp 1 * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
    _ ≤ Real.exp 1 * ((m.factorial : ℝ) / η ^ m) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        rw [le_div_iff₀ hηm]
        calc ((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1))) * η ^ m
            = η ^ m * (((v : ℝ) + 1) ^ m * Real.exp (-(η * ((v:ℝ) + 1)))) := by ring
          _ ≤ (m.factorial : ℝ) := h1
    _ = Real.exp 1 * m.factorial / η ^ m := by ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
