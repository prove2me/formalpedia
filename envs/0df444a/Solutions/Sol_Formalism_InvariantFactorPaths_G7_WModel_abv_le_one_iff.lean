-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.WModel.abv_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:20.069865+00:00
-- url     : https://prove2.me/submissions/f1310878-1396-44ca-a80f-03dd3f3aead9

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementW
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_WittTeichmullerRoot
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_WModel_abv_coe_le_one

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
theorem _root_.solution (x : KK p) : abv p x ≤ 1 ↔ ∃ w : WW p, algebraMap (WW p) (KK p) w = x := by
  constructor
  · intro h
    apply IsDiscreteValuationRing.exists_lift_of_le_one
    have h' : (adicAbvDef (IsDiscreteValuationRing.maximalIdeal (WW p)) (one_lt_b p) x : ℝ) ≤ 1 := h
    rw [adicAbvDef] at h'
    exact (WithZeroMulInt.toNNReal_le_one_iff (one_lt_b p)).1 (by exact_mod_cast h')
  · rintro ⟨w, rfl⟩
    exact abv_coe_le_one p w
end Formalism.InvariantFactorPaths.G7.WModel
