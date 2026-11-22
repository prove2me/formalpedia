-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.adj_matrix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:51:48.372449+00:00
-- url     : https://prove2.me/submissions/fe278204-1081-4fe0-8142-6de3c11f0efe

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
namespace Formalism.DivisionValues
namespace FinitelyNonzeroLinear
section Ext
variable {K Ω : Type} [Field K] [Field Ω] (j : K →+* Ω)
variable {j}
end Ext
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Herm
variable {K : Type} [Field K] [NumberField K] [StarRing K]
private theorem hform_eq_lemma {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H *ᵥ y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
    Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
end Herm
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Cx
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
end Cx
section Diag
variable {K : Type} [Field K] {n : ℕ}
end Diag
end FinitelyNonzeroLinear
namespace FinitelyNonzeroLinear
section Dich
variable {n : ℕ} {Hc : Matrix (Fin n) (Fin n) ℂ}
end Dich
end FinitelyNonzeroLinear
end Formalism.DivisionValues
end
end

set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution {n : ℕ} {H T T' : Matrix (Fin n) (Fin n) K}
    (h : ∀ x y : Fin n → K, hform H (T *ᵥ x) y = hform H x (T' *ᵥ y)) : Tᴴ * H = H * T' := by
  have e : ∀ x y : Fin n → K, star x ⬝ᵥ (Tᴴ * H) *ᵥ y = star x ⬝ᵥ (H * T') *ᵥ y := by
    intro x y
    have := h x y
    rw [hform_eq_lemma, hform_eq_lemma] at this
    simpa only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec] using this
  ext a b
  have := e (Pi.single a 1) (Pi.single b 1)
  simpa [Matrix.mulVec_single_one] using this
end Formalism.DivisionValues.FinitelyNonzeroLinear
