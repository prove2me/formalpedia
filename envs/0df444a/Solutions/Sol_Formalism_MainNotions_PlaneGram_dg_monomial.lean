-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:36.00764+00:00
-- url     : https://prove2.me/submissions/046e9914-2162-49af-92eb-e757d8a996e1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_LiftBoundOfHypotheses
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff

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
theorem _root_.solution {σ : Type} (f : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (c : K) :
    dg f (monomial α c) = monomial α (f α * c) := by
  have hb : (basisMonomials σ K) α = monomial α 1 := by simp [coe_basisMonomials]
  have h1 : dg f (monomial α 1) = monomial α (f α) := by rw [← hb, dg, Module.Basis.constr_basis]
  rw [show monomial α c = c • monomial α (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one], map_smul, h1,
    smul_monomial, smul_eq_mul, mul_comm]
end Formalism.MainNotions.PlaneGram
