-- Prove2me | solution 1 for Formalism.L2.Th1.H.form_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:15.782794+00:00
-- url     : https://prove2.me/submissions/9aa67699-eb04-4060-a0fb-4fc16f101297

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace Formalism.L2.Th1.H
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (H : Sesq V) (b : Module.Basis n ℂ V) (l : n → ℂ)
    (L : V →ₗ[ℂ] V) (hb : ∀ i j, H (b i) (b j) = if i = j then 1 else 0) (hL : ∀ i, L (b i) = l i • b i)
    (w : n → ℂ) :
    H (L (b.equivFun.symm w)) (b.equivFun.symm w) = ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2 := by
  rw [Module.Basis.equivFun_symm_apply]
  simp only [map_sum, map_smul, hL, smul_smul, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smul_apply, map_smulₛₗ, hb, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := Complex.mul_conj (w i)
  rw [Complex.normSq_eq_norm_sq] at h
  push_cast at h
  linear_combination (l i) * h
end Formalism.L2.Th1.H
