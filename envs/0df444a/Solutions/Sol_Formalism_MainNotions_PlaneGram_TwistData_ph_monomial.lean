-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:27:22.341832+00:00
-- url     : https://prove2.me/submissions/b70be714-1e63-46d0-9190-7ebfdcca6edb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_X
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_eq_sum

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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (ζ : D.EM) (c : K) :
    D.ph p (monomial ζ c) = monomial (D.phE p ζ) c := by
  classical
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, phE_eq_sum]
  simp only [map_pow, ph_X, monomial_pow, one_pow]
  rw [show D.ph p (C c) = C c from (D.ph p).commutes c]
  rw [Finsupp.sum, ← monomial_sum_one, C_mul_monomial, mul_one]
end Formalism.MainNotions.PlaneGram.TwistData
