-- Prove2me | solution 1 for Formalism.L2.DIV.fk_descent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:14.380907+00:00
-- url     : https://prove2.me/submissions/04412d61-de60-455d-a352-b455f523187f

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_coeff_mem
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v)
    (hv0 : ∀ i, v i ∈ (map (σ := σ) K0.subtype).range) (c : κ → K)
    (hx : ∑ i, c i • v i ∈ (map (σ := σ) K0.subtype).range) (i : κ) : c i ∈ K0 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K0 K)
    (LinearMap.ker_eq_bot.mpr (algebraMap K0 K).injective)
  have hπ' : ∀ a : K0, π (a : K) = a := fun a => congrArg (fun φ : K0 →ₗ[K0] K0 => φ a) hπ
  have hmul : ∀ (a : K0) (z : K), π (z * (a : K)) = π z * a := by
    intro a z
    have : z * (a : K) = a • z := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have key : ∑ i, (c i - (π (c i) : K)) • v i = 0 := by
    ext m
    rw [coeff_sum, coeff_zero]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : coeff m (∑ i, c i • v i) = ∑ i, c i * coeff m (v i) := by
      rw [coeff_sum]
      simp only [coeff_smul, smul_eq_mul]
    have h2 : ((π (coeff m (∑ i, c i • v i)) : K0) : K) = coeff m (∑ i, c i • v i) :=
      congrArg (fun a : K0 => (a : K)) (hπ' ⟨_, fk_coeff_mem K0 hx m⟩)
    rw [← h1, ← h2, h1, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hmul ⟨_, fk_coeff_mem K0 (hv0 i) m⟩ (c i)
    simp only at this
    rw [this]
    rfl
  have := (Fintype.linearIndependent_iff.mp hv) _ key i
  rw [sub_eq_zero] at this
  rw [this]
  exact (π (c i)).2
end Formalism.L2.DIV
