-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_value
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:54.685183+00:00
-- url     : https://prove2.me/submissions/8410ea2b-0402-44ff-a036-7abbcf5e0a3f

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_p
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_unit
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_exists_pow_unit

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
theorem _root_.solution (x : KK p) (hx : x ≠ 0) : ∃ k : ℤ, abv p x = (p : ℝ) ^ k := by
  obtain ⟨n, u, rfl⟩ := exists_pow_unit p x hx
  refine ⟨-n, ?_⟩
  rw [map_mul, abv_unit, mul_one, map_zpow₀, abv_p, inv_zpow']
end Formalism.InvariantFactorPaths.G7.WModel
