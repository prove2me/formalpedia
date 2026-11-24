-- Prove2me | solution 1 for Formalism.HN.sum_ite_val_lt_sub_mul_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:11.309099+00:00
-- url     : https://prove2.me/submissions/64e67982-0d81-47a2-9517-ebd32eddaab9

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_RatioMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNStep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Theorems.Thm_Formalism_HN_sum_ite_val_lt_sub_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution (n m₁ m₂ : ℕ) (h₁₂ : m₁ ≤ m₂) (h₂ : m₂ ≤ n) (x : Fin n → ℝ) (a : ℝ)
    (hx : ∀ j : Fin n, m₁ ≤ (j : ℕ) → (j : ℕ) < m₂ → x j ≤ a) :
    (∑ j : Fin n, if (j : ℕ) < m₂ then x j else 0) - a * m₂ ≤
      (∑ j : Fin n, if (j : ℕ) < m₁ then x j else 0) - a * m₁ := by
  rw [sum_ite_val_lt_sub_mul n m₁ (le_trans h₁₂ h₂) x a, sum_ite_val_lt_sub_mul n m₂ h₂ x a]
  apply Finset.sum_le_sum
  intro j _
  by_cases h1 : (j : ℕ) < m₁
  · simp only [if_pos h1, if_pos (lt_of_lt_of_le h1 h₁₂), le_refl]
  · by_cases h2 : (j : ℕ) < m₂
    · rw [if_neg h1, if_pos h2]
      linarith [hx j (not_lt.mp h1) h2]
    · simp only [if_neg h1, if_neg h2, le_refl]
end Formalism.HN
