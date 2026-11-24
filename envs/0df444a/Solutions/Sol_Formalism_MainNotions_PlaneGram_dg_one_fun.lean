-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.dg_one_fun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:07:21.710746+00:00
-- url     : https://prove2.me/submissions/e5ecdd04-3535-49ab-8435-e0d8fb4267ef

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
end Slope
namespace CostOK
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end CostOK
section Binom
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop}
end Binom
section DiagCost
open MvPolynomial
private theorem dg_monomial' (f : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (c : K) :
    dg f (monomial α c) = monomial α (c * f α) := by
  have h1 : (monomial α c : MvPolynomial σ K) = c • monomial α (1 : K) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  have h2 : dg f (monomial α (1 : K)) = monomial α (f α) := by
    rw [show (monomial α (1 : K) : MvPolynomial σ K) = basisMonomials σ K α by
      rw [coe_basisMonomials]]
    unfold dg
    rw [Module.Basis.constr_basis]
  rw [h1, map_smul, h2, smul_monomial, smul_eq_mul]
private theorem coeff_dg_eq_coeff_mul (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (α : σ →₀ ℕ) :
    coeff α (dg f F) = coeff α F * f α := by
  classical
  conv_lhs => rw [F.as_sum]
  rw [map_sum, coeff_sum]
  simp only [dg_monomial']
  rw [Finset.sum_eq_single α]
  · rw [coeff_monomial, if_pos rfl]
  · intro b _ hb
    rw [coeff_monomial, if_neg hb]
  · intro hα
    simp only [mem_support_iff, not_not] at hα
    rw [coeff_monomial, if_pos rfl, hα, zero_mul]
end DiagCost
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open MvPolynomial
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (F : MvPolynomial σ K) : dg (fun _ => (1 : K)) F = F := by
  ext α
  simp only [coeff_dg_eq_coeff_mul, coeff_add, coeff_sub, coeff_smul, smul_eq_mul]
  ring
end Formalism.MainNotions.PlaneGram
