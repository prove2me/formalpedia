-- Prove2me | solution 1 for Formalism.DivisionValues.absE_dsum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:14.173473+00:00
-- url     : https://prove2.me/submissions/09e31e8e-88d8-48a1-94dd-1ec1ebc1d884

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_StatementE
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_AbsorbE
import Theorems.Thm_Formalism_DivisionValues_absE_ssum_le

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
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution {J Pl : Type} [Fintype J] [Fintype Pl] (g : J → Pl → ℝ) (c m f : ℝ)
    (hc : 0 ≤ c) (hJ : (Fintype.card J : ℝ) = m) (hP : (Fintype.card Pl : ℝ) ≤ f)
    (hg : ∀ j ρ, g j ρ ≤ c) : ∑ j, ∑ ρ, g j ρ ≤ m * (f * c) := by
  apply absE_ssum_le (fun j => ∑ ρ, g j ρ) (f * c) m hJ
  intro j
  calc ∑ ρ, g j ρ ≤ ∑ _ρ : Pl, c := Finset.sum_le_sum (fun ρ _ => hg j ρ)
    _ = (Fintype.card Pl : ℝ) * c := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ f * c := mul_le_mul_of_nonneg_right hP hc
end Formalism.DivisionValues
