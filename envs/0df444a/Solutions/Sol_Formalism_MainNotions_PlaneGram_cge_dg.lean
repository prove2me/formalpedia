-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.cge_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:14.724177+00:00
-- url     : https://prove2.me/submissions/ee88dd61-8786-4c7e-bbd7-eedd4c224f48

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vge_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
private lemma coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K) (β : σ →₀ ℕ) :
    (dg f F).coeff β = f β * F.coeff β := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial α c =>
    have e : monomial α c = c • (basisMonomials σ K) α := by
      rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    unfold dg
    rw [e, map_smul, Module.Basis.constr_basis, coe_basisMonomials]
    simp only [coeff_smul, coeff_monomial, smul_eq_mul]
    split_ifs with h
    · subst h
      ring
    · simp
  | add F G hF hG => rw [map_add, coeff_add, coeff_add, hF, hG, mul_add]
section DVR
variable {v} {p : ℕ} [CharZero K]
end DVR
section DVR2
variable {v} {p : ℕ} [CharZero K]
end DVR2
section Star
variable {v} {p : ℕ} [CharZero K]
end Star
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} {a b : ℝ} {f : (σ →₀ ℕ) → K} {F : MvPolynomial σ K}
    (hf : ∀ α, vge v a (f α)) (hF : cge v b F) : cge v (a + b) (dg f F) := by
  intro β
  rw [coeff_dg_eq_mul_coeff]
  exact vge_mul v (hf β) (hF β)
end Formalism.MainNotions.PlaneGram
