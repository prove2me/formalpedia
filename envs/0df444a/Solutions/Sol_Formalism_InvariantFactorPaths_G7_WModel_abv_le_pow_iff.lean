-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:10:29.253327+00:00
-- url     : https://prove2.me/submissions/c55665a9-4307-4081-a155-2fbd112999da

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_coe_le_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_p
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_one_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_p_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.InvariantFactorPaths.G7.WModel
variable (p : ℕ) [hp : Fact p.Prime]
namespace Formalism.InvariantFactorPaths.G7.WModel
theorem _root_.solution (N : ℕ) (x : KK p) : abv p x ≤ ((p : ℝ)⁻¹) ^ N ↔
    ∃ w : WW p, x = (p : KK p) ^ N * algebraMap (WW p) (KK p) w := by
  have hp0 := p_ne_zero p
  have hpos : (0 : ℝ) < ((p : ℝ)⁻¹) ^ N := by
    have := hp.out.pos
    positivity
  constructor
  · intro h
    have h1 : abv p (x / (p : KK p) ^ N) ≤ 1 := by
      rw [map_div₀, map_pow, abv_p]
      exact div_le_one_of_le₀ h hpos.le
    obtain ⟨w, hw⟩ := (abv_le_one_iff p _).1 h1
    refine ⟨w, ?_⟩
    rw [hw]
    field_simp
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_pow, abv_p]
    exact mul_le_of_le_one_right hpos.le (abv_coe_le_one p w)
end Formalism.InvariantFactorPaths.G7.WModel
