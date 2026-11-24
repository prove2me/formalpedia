-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns.exists_refl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:06.86932+00:00
-- url     : https://prove2.me/submissions/0f1c819b-1ba2-4d2a-98fc-0eb732289e89

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardSumNormFibres
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_FiniteUnitaryColumns_cj_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
open Matrix
variable {k : Type*} [Field k]
namespace Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (σ : k ≃+* k)
    (hσ : ∀ x, σ (σ x) = x) (x y : n → k) (hx : ∑ i, σ (x i) * x i = 1)
    (hy : ∑ i, σ (y i) * y i = 1) (hxy : ∑ i, σ (y i) * x i ≠ 1) :
    ∃ g : Matrix n n k, cj σ g * g = 1 ∧ g *ᵥ x = y := by
  set u : n → k := x - y with hu
  set a : k := ∑ i, σ (u i) * x i with ha
  have ha1 : a = 1 - ∑ i, σ (y i) * x i := by
    simp only [ha, hu, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib, hx]
  have ha0 : a ≠ 0 := by
    rw [ha1]; exact sub_ne_zero.mpr (Ne.symm hxy)
  have hsa0 : σ a ≠ 0 := by simpa using ha0
  have hsa : σ a = 1 - ∑ i, σ (x i) * y i := by
    rw [ha1]; simp [map_sum, hσ, mul_comm]
  have hn : ∑ i, σ (u i) * u i = a + σ a := by
    rw [hsa, ha1]
    simp only [hu, Pi.sub_apply, map_sub, sub_mul, mul_sub, Finset.sum_sub_distrib, hx, hy]
    ring
  set P : Matrix n n k := vecMulVec u (fun i => σ (u i)) with hP
  have hPP : P * P = (a + σ a) • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec, ← hn]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, dotProduct]
    ring
  have hcP : cj σ P = P := by
    ext i j
    simp [cj_apply, hP, vecMulVec_apply, hσ, mul_comm]
  refine ⟨1 - a⁻¹ • P, ?_, ?_⟩
  · have hc : cj σ (1 - a⁻¹ • P) = 1 - (σ a)⁻¹ • P := by
      ext i j
      have := congrFun (congrFun hcP i) j
      have h1 := congrFun (congrFun (cj_one (n := n) σ) i) j
      simp only [cj_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul,
        map_inv₀] at this h1 ⊢
      rw [this, h1]
    rw [hc, sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, smul_mul_smul_comm, hPP]
    have : (σ a)⁻¹ * a⁻¹ * (a + σ a) = a⁻¹ + (σ a)⁻¹ := by
      field_simp
      ring
    rw [smul_smul, this, add_smul]
    abel
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hP, Matrix.vecMulVec_mulVec]
    have : (fun i => σ (u i)) ⬝ᵥ x = a := rfl
    rw [this]
    ext i
    simp [hu, ha0]
end Formalism.HermitianLattices.Ext.L3.FiniteUnitaryColumns
