-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.nabla_weight_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:59.933196+00:00
-- url     : https://prove2.me/submissions/6baeee8e-32e6-475a-91c6-3aee50ad8107

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDrowLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowActMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_NablaLLe
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_row_action_mul
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
theorem _root_.solution : NablaLLe := by
  intro R K _ _ _ k n ν g hg F hF
  unfold nablaL at hF
  rw [Submodule.mem_comap, Submodule.mem_map] at hF
  obtain ⟨G, hG, hGF⟩ := hF
  have hGF' : map (algebraMap R K) G = rowAct K g F := hGF

  have hGK : map (algebraMap R K) G ∈ dualWeyl K k n ν := by
    unfold dualWeyl at hG ⊢
    rw [Submodule.mem_inf] at hG ⊢
    obtain ⟨hG1, hG2⟩ := hG
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hG1 ⊢
      intro d hd
      apply hG1
      intro h0
      apply hd
      rw [coeff_map, h0, map_zero]
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hG2 ⊢
      intro l j hlj
      have e := hG2 l j hlj
      have hc : ∀ p : MvPolynomial (Fin k × Fin n) R,
          colAddGen K l j (map (algebraMap R K) p) = map (algebraMap R K) (colAddGen R l j p) := by
        intro p
        induction p using MvPolynomial.induction_on
        · rename_i a
          simp [colAddGen]
        · rename_i p q hp hq
          simp only [map_add, hp, hq]
        · rename_i p v hp
          simp only [map_mul, hp]
          congr 1
          simp only [colAddGen, map_X, aeval_X]
          split_ifs <;> simp
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      rw [hc, ← map_rename, ← map_sub, e, map_zero]

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
  have hid : rowAct K (1 : Matrix (Fin k) (Fin k) K) F = F := by
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have e := congrArg (fun Φ => Φ F) (row_action_mul K k n g⁻¹ g)
  simp only [AlgHom.comp_apply] at e
  rw [Matrix.mul_nonsing_inv g hg, hid] at e
  rw [← e, ← hGF']
  exact hinv _ _ hGK
end Formalism.GradedWeylDivisibility
