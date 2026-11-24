-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nablaLKBasis_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.110641+00:00
-- url     : https://prove2.me/submissions/8f59e24b-f34e-446a-8acb-65a893272946

import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLKBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_span_map_weightBasis_eq_dualWeyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_linInd_base
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_rowAct_inv_left
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_rowAct_inv_right
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (h1 : RowActMul) (_h2 : SSBasis) : NablaLKBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h
      rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (coeff d P) : MvPolynomial (Fin k × Fin n) K) = C (coeff d P) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (coeff d P)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hli := ldlat_linInd_base (K := K) hinj hb.1
  refine ⟨hli.map' (rowAct K g⁻¹).toLinearMap (LinearMap.ker_eq_bot.mpr fun x y hxy => ?_), ?_⟩
  · have e := congrArg (rowAct K g) hxy
    simpa [ldlat_rowAct_inv_left h1 g hg] using e
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) =
        (rowAct K g⁻¹).toLinearMap '' Set.range (fun i => map (algebraMap R K) (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, span_map_weightBasis_eq_dualWeyl hb]
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      exact hinv g⁻¹ P hP
    · intro P hP
      rw [Submodule.mem_map]
      exact ⟨rowAct K g P, hinv g P hP, ldlat_rowAct_inv_right h1 g hg P⟩
end Formalism.GradedWeylDivisibility
