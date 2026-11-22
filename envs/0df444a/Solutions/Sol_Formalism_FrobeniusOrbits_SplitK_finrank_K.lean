-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.finrank_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:31:07.63009+00:00
-- url     : https://prove2.me/submissions/d9e610b0-0e6c-459f-86bf-4cd5a2af4416

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_b_not_rat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
private theorem isIntegral_b : IsIntegral ℚ b := by
  first
  | exact IsIntegral.of_finite ℚ b
  | exact Algebra.IsIntegral.isIntegral b
private theorem aeval_X_sq_add_C_eq_zero_of_sq_eq_neg (hb : b ^ 2 = -(d : L)) :
    Polynomial.aeval b (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) = 0 := by
  first
  | simp [hb]
  | (rw [map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hb]; simp)
private theorem minpoly_natDegree_eq_two_of_sq_eq_neg (hd : 0 < d) (hb : b ^ 2 = -(d : L)) :
    (minpoly ℚ b).natDegree = 2 := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have hmon : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := by
    first
    | exact Polynomial.monic_X_pow_add_C _ two_ne_zero
    | monicity!
  have hle : (minpoly ℚ b).natDegree ≤ 2 := by
    have h1 := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ b (aeval_X_sq_add_C_eq_zero_of_sq_eq_neg hb)) hmon.ne_zero
    first
    | rwa [Polynomial.natDegree_X_pow_add_C] at h1
    | exact h1.trans (by compute_degree)
  have hne1 : (minpoly ℚ b).natDegree ≠ 1 := by
    intro h1
    first
    | (rw [minpoly.natDegree_eq_one_iff] at h1; obtain ⟨q, hq⟩ := h1; exact b_not_rat hd hb (IntermediateField.mem_bot.mpr ⟨q, hq⟩))
    | (have h2 : Module.finrank ℚ ℚ⟮b⟯ = 1 := by rw [IntermediateField.adjoin.finrank hint, h1]
       exact b_not_rat hd hb (IntermediateField.adjoin_simple_eq_bot_iff.mp (IntermediateField.finrank_eq_one_iff.mp h2)))
  have hpos := minpoly.natDegree_pos hint
  omega
end Formalism.FrobeniusOrbits.SplitK
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (hd : 0 < d) (hb : b ^ 2 = -(d : L)) : Module.finrank ℚ (Kd b) = 2 := by
  show Module.finrank ℚ ℚ⟮b⟯ = 2
  rw [IntermediateField.adjoin.finrank isIntegral_b, minpoly_natDegree_eq_two_of_sq_eq_neg hd hb]
end Formalism.FrobeniusOrbits.SplitK
