-- Prove2me | solution 1 for Formalism.L2.Th1.F.mul_stable_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:26:17.883801+00:00
-- url     : https://prove2.me/submissions/276ba611-092a-4d8c-83d0-d52be8d18bb2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_MulStableIntegral
import Theorems.Thm_Formalism_L2_Th1_F_Ker_matrix_data

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Ker
namespace Formalism.L2.Th1.F
theorem _root_.solution : MulStableIntegral := by
  unfold MulStableIntegral
  intro L α h
  obtain ⟨a, b, c, d, -, -, htr, hn⟩ := matrix_data L α h
  have h1 : α + conj α = ((a + d : ℤ) : ℂ) := by
    rw [Complex.add_conj]
    exact_mod_cast htr
  have h2 : α * conj α = ((a * d - b * c : ℤ) : ℂ) := by
    rw [Complex.mul_conj]
    exact_mod_cast hn
  exact ⟨a + d, a * d - b * c, h1, h2, by linear_combination α * h1 - h2⟩
end Formalism.L2.Th1.F
