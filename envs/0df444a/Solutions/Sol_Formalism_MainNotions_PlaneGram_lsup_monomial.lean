-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.lsup_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:16.672303+00:00
-- url     : https://prove2.me/submissions/d42b566c-40c4-4194-8935-41f3b6b7d683

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ τ : Type} (φ : (σ →₀ ℕ) → MvPolynomial τ K) (α : σ →₀ ℕ) (c : K) :
    lsup φ (monomial α c) = c • φ α := by
  have h : monomial α c = c • (basisMonomials σ K) α := by simp [smul_monomial]
  rw [h, map_smul, lsup, Module.Basis.constr_basis]
end Formalism.MainNotions.PlaneGram
