-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives.a_prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:08.09197+00:00
-- url     : https://prove2.me/submissions/05f383f1-30ef-43e0-80e9-cfaef3f72246

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_contDiffAt_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PhaseFunctionDerivatives_a_norm_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
open Formalism.FourierDecayAlt.G
namespace Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
theorem _root_.solution {n : ℕ} (N : ℕ) (x : Fin n → ℂ) (hx : ∀ k, x k ≠ 0) (b : ℝ)
    (hb : ∀ k, ‖x k‖⁻¹ ≤ b) :
    ‖iteratedFDeriv ℂ N (fun y : Fin n → ℂ => ∏ k, (y k)⁻¹) x‖ ≤
      a_cst n N * ((∏ k, ‖x k‖⁻¹) * b ^ N) := by
  have hS := a_isOpen n
  have hxS : x ∈ {x : Fin n → ℂ | ∀ k, x k ≠ 0} := hx
  rw [← iteratedFDerivWithin_of_isOpen N hS hxS]
  have hcd : ∀ k ∈ (univ : Finset (Fin n)),
      ContDiffOn ℂ N (fun y : Fin n → ℂ => (y k)⁻¹) {x : Fin n → ℂ | ∀ k, x k ≠ 0} :=
    fun k _ y hy => (a_contDiffAt_inv N k y (hy k)).contDiffWithinAt
  refine (norm_iteratedFDerivWithin_prod_le hcd hS.uniqueDiffOn hxS le_rfl).trans ?_
  rw [a_cst, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hcard : ∑ k, Multiset.count k (p : Multiset (Fin n)) = N := by
    rw [Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    exact p.2
  calc ∏ k, ‖iteratedFDerivWithin ℂ (Multiset.count k (p : Multiset (Fin n)))
          (fun y : Fin n → ℂ => (y k)⁻¹) {x : Fin n → ℂ | ∀ k, x k ≠ 0} x‖
      ≤ ∏ k, (((Multiset.count k (p : Multiset (Fin n))).factorial : ℝ) *
          (‖x k‖⁻¹ * b ^ (Multiset.count k (p : Multiset (Fin n))))) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
        rw [iteratedFDerivWithin_of_isOpen _ hS hxS]
        refine (a_norm_inv _ k x (hx k)).trans ?_
        gcongr
        exact hb k
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hcard]
end Formalism.FourierDecayAlt.P.PhaseFunctionDerivatives
