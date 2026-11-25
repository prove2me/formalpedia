-- Prove2me | solution 1 for Expanders.abs_dotProduct_adjMatrix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:30:55.673032+00:00
-- url     : https://prove2.me/submissions/8397101e-aeee-4b76-80ff-94ad7f02f12e

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Theorems.Thm_Expanders_dotProduct_self_nonneg_real
public import Theorems.Thm_Expanders_adjMatrix_dotProduct_comm

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {μ : ℝ}
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (x y : V → ℝ) (hx : ∑ v, x v = 0) (hy : ∑ v, y v = 0) :
    |dotProduct x (G.adjMatrix ℝ *ᵥ y)| ≤
      μ * (Real.sqrt (dotProduct x x) * Real.sqrt (dotProduct y y)) := by
  set A := G.adjMatrix ℝ
  by_cases hx0 : dotProduct x x = 0
  · rw [dotProduct_self_eq_zero.mp hx0]; simp
  by_cases hy0 : dotProduct y y = 0
  · rw [dotProduct_self_eq_zero.mp hy0]; simp
  have hX : 0 < dotProduct x x := lt_of_le_of_ne (dotProduct_self_nonneg_real x) (Ne.symm hx0)
  have hY : 0 < dotProduct y y := lt_of_le_of_ne (dotProduct_self_nonneg_real y) (Ne.symm hy0)
  set p := Real.sqrt (dotProduct x x) with hp
  set q := Real.sqrt (dotProduct y y) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr hX
  have hq0 : 0 < q := Real.sqrt_pos.mpr hY
  have hp2 : p ^ 2 = dotProduct x x := Real.sq_sqrt hX.le
  have hq2 : q ^ 2 = dotProduct y y := Real.sq_sqrt hY.le
  have hsum : ∀ t : ℝ, ∑ v, (q • x + t • y) v = 0 := by
    intro t
    simp [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy]
  have h1 := hμ _ (hsum p)
  have h2 := hμ _ (hsum (-p))
  have hsym := adjMatrix_dotProduct_comm G y x
  simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul] at h1 h2
  rw [hsym] at h1 h2
  rw [abs_le] at h1 h2
  set b := dotProduct x (A *ᵥ y)
  have hyx : dotProduct y x = dotProduct x y := dotProduct_comm y x
  rw [hyx, ← hp2, ← hq2] at h1 h2
  have hpq : 0 < p * q := mul_pos hp0 hq0
  have key1 : 4 * (p * q) * b ≤ 4 * (p * q) * (μ * (p * q)) := by
    linarith [h1.2, h2.1]
  have key2 : 4 * (p * q) * (-b) ≤ 4 * (p * q) * (μ * (p * q)) := by
    linarith [h1.1, h2.2]
  rw [abs_le]
  constructor
  · have := le_of_mul_le_mul_left key2 (by positivity); linarith
  · exact le_of_mul_le_mul_left key1 (by positivity)
end Expanders
