-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.wcomp_memC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:48.384989+00:00
-- url     : https://prove2.me/submissions/8ac597e3-65b5-4106-84a1-369d9e5f880d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_cartan
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_CountingSumsFrames_compP_and
import Theorems.Thm_Formalism_CountingSumsFrames_compP_congr
import Theorems.Thm_Formalism_CountingSumsFrames_compP_true
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply


section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
section Lib
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem exists_mem_coeff_eq_prod_weight_sub_mul (LL : Letters N) (j : ℕ) (c : Fin r)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, glAct p LL j c c x ∈ S) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ S) :
    ∀ F : Finset ℤ, ∃ y ∈ S, ∀ m, coeff m y = (∏ w ∈ F, (((wt LL j c m : ℤ) : ℚ_[p]) - (w : ℚ_[p]))) * coeff m x := by
  intro F
  induction F using Finset.induction_on with
  | empty => exact ⟨x, hx, fun m => by simp⟩
  | insert a F ha ih =>
    obtain ⟨y, hy, hym⟩ := ih
    refine ⟨glAct p LL j c c y - ((a : ℤ) : ℚ_[p]) • y, sub_mem (hS y hy) (Submodule.smul_mem _ _ hy), fun m => ?_⟩
    rw [coeff_sub, coeff_cartan, coeff_smul, smul_eq_mul, hym m, Finset.prod_insert ha]
    ring
private theorem compP_weight_eq_mem_of_glAct_stable (LL : Letters N) (j : ℕ) (c : Fin r)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ x ∈ S, glAct p LL j c c x ∈ S) (k : ℤ) :
    ∀ x ∈ S, compP (fun m => wt LL j c m = k) x ∈ S := by
  classical
  intro x hx
  set F := (x.support.image (wt LL j c)).erase k with hF
  obtain ⟨y, hy, hym⟩ := exists_mem_coeff_eq_prod_weight_sub_mul LL j c S hS x hx F
  have hD : (∏ w ∈ F, ((k : ℚ_[p]) - (w : ℚ_[p]))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    rw [sub_ne_zero]
    intro h
    exact (Finset.ne_of_mem_erase hw) (by exact_mod_cast h.symm)
  have heq : compP (fun m => wt LL j c m = k) x = (∏ w ∈ F, ((k : ℚ_[p]) - (w : ℚ_[p])))⁻¹ • y := by
    ext m
    rw [coeff_compP, coeff_smul, smul_eq_mul, hym m]
    by_cases hm : coeff m x = 0
    · simp [hm]
    · split_ifs with hk
      · rw [hk, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
      · have hmem : wt LL j c m ∈ F := by
          rw [hF, Finset.mem_erase]
          exact ⟨hk, Finset.mem_image_of_mem _ (mem_support_iff.mpr hm)⟩
        rw [Finset.prod_eq_zero (f := fun w : ℤ => ((wt LL j c m : ℤ) : ℚ_[p]) - (w : ℚ_[p])) hmem (sub_self _),
          zero_mul, mul_zero]
  rw [heq]
  exact Submodule.smul_mem _ _ hy
private theorem compP_weights_eq_mem_of_glAct_stable (LL : Letters N) (j : ℕ)
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) (μ : Fin r → ℤ) :
    ∀ F : Finset (Fin r), (∀ c ∈ F, ∀ x ∈ S, glAct p LL j c c x ∈ S) →
      ∀ x ∈ S, compP (fun m => ∀ c ∈ F, wt LL j c m = μ c) x ∈ S := by
  classical
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _ x hx
    rw [compP_congr _ (fun _ => True) (fun m => by simp), compP_true]
    exact hx
  | insert a F ha ih =>
    intro hS x hx
    rw [compP_congr _ (fun m => wt LL j a m = μ a ∧ ∀ c ∈ F, wt LL j c m = μ c)
      (fun m => Finset.forall_mem_insert _ _ _), compP_and]
    exact compP_weight_eq_mem_of_glAct_stable LL j a S (hS a (Finset.mem_insert_self _ _)) (μ a) _
      (ih (fun c hc => hS c (Finset.mem_insert_of_mem hc)) x hx)
end Lib
section YC
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end YC
section Split
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Split
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hS : ∀ c ∈ Cs, ∀ x ∈ S, glAct p LL j c c x ∈ S) (μ : Fin r → ℤ) :
    ∀ x ∈ S, compP (fun m => ∀ c ∈ Cs, wt LL j c m = μ c) x ∈ S := compP_weights_eq_mem_of_glAct_stable LL j S μ Cs hS
end Formalism.InvariantFactorPaths.L4
