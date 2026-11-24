-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_sig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:15:36.516793+00:00
-- url     : https://prove2.me/submissions/a9cd7696-044a-4443-823e-6f58b6704acd

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_one_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_le_pow_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_sig_coe
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_frob_sub_pow

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
theorem _root_.solution (a : KK p) (ha : abv p a ≤ 1) : abv p (sig p a - a ^ p) ≤ (p : ℝ)⁻¹ := by
  obtain ⟨w, rfl⟩ := (abv_le_one_iff p a).1 ha
  obtain ⟨y, hy⟩ := frob_sub_pow p w
  have := (abv_le_pow_iff p 1 (sig p (algebraMap (WW p) (KK p) w) -
    (algebraMap (WW p) (KK p) w) ^ p)).2 ⟨y, by
      rw [sig_coe, ← map_pow, ← map_sub, hy, map_mul, map_natCast, pow_one]⟩
  simpa using this
end Formalism.InvariantFactorPaths.G7.WModel
