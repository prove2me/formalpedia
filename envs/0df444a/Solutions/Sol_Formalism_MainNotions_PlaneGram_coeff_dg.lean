-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.coeff_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:04.552328+00:00
-- url     : https://prove2.me/submissions/d15c8fe0-fa1d-46be-99fc-5565a05329ee

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial

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
theorem _root_.solution {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    (dg f F).coeff α = f α * F.coeff α := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [dg_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · simp
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]
end Formalism.MainNotions.PlaneGram
