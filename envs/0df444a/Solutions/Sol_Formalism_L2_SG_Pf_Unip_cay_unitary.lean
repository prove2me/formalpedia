-- Prove2me | solution 1 for Formalism.L2.SG.Pf.Unip.cay_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:24:52.486416+00:00
-- url     : https://prove2.me/submissions/df4a055b-ae59-43e4-b321-2b2eb5408c9c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_UnipTool
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_star_half
import Theorems.Thm_Formalism_L2_SG_Pf_Unip_half_add_half

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.Unip
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [CommRing K] [Invertible (2 : K)]
variable {lv : ι → ℕ} {k : ℕ}
variable [StarRing K]
namespace Formalism.L2.SG.Pf.Unip
theorem _root_.solution {J : Matrix ι ι K} {N : ℕ} {Z : Matrix ι ι K} (hZ : Zᴴ * J = -(J * Z))
    (hN : ((⅟2 : K) • Z) ^ N = 0) : (cay N Z)ᴴ * J * cay N Z = J := by
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = (⅟2 : K) • Z := ⟨_, rfl⟩
  rw [← hYdef] at hN
  have hZY : Z = Y + Y := by
    rw [hYdef]
    exact (half_add_half Z).symm
  have hY : Yᴴ * J = -(J * Y) := by
    rw [hYdef, conjTranspose_smul, star_half, smul_mul_assoc, hZ, mul_smul_comm, smul_neg]
  have hpow : ∀ j : ℕ, Yᴴ ^ j * J = J * (-Y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, hY, pow_succ', ← Matrix.mul_assoc,
        Matrix.mul_neg, Matrix.neg_mul]
  have hS : (geo N Y)ᴴ * J = J * geo N (-Y) := by
    unfold geo
    rw [conjTranspose_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_pow, hpow]
  have h1 : (1 - Y) * geo N Y = 1 := by
    unfold geo
    rw [mul_neg_geom_sum, hN, sub_zero]
  have hN' : (-Y) ^ N = 0 := by rw [neg_pow, hN, mul_zero]
  have h2 : geo N (-Y) * (1 + Y) = 1 := by
    unfold geo
    have := geom_sum_mul_neg (-Y) N
    rw [sub_neg_eq_add, hN', sub_zero] at this
    exact this
  have hS1 : geo N Y = 1 + Y * geo N Y := by
    have := h1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    exact this
  have hC : cay N Z = 1 + Z * geo N Y := by
    rw [hYdef]
    rfl
  have hC2 : cay N Z = (1 + Y) * geo N Y := by
    rw [hC, hZY, Matrix.add_mul, Matrix.add_mul, Matrix.one_mul]
    calc 1 + (Y * geo N Y + Y * geo N Y) = (1 + Y * geo N Y) + Y * geo N Y := by abel
      _ = geo N Y + Y * geo N Y := by rw [← hS1]
  have hA : (1 + Y)ᴴ * J = J * (1 - Y) := by
    rw [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.one_mul, hY, Matrix.mul_sub,
      Matrix.mul_one, sub_eq_add_neg]
  have hcomm : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  rw [hC2, conjTranspose_mul]
  calc (geo N Y)ᴴ * (1 + Y)ᴴ * J * ((1 + Y) * geo N Y)
      = (geo N Y)ᴴ * ((1 + Y)ᴴ * J) * ((1 + Y) * geo N Y) := by simp only [Matrix.mul_assoc]
    _ = ((geo N Y)ᴴ * J) * ((1 - Y) * (1 + Y)) * geo N Y := by
      rw [hA]; simp only [Matrix.mul_assoc]
    _ = J * (geo N (-Y) * (1 + Y)) * ((1 - Y) * geo N Y) := by
      rw [hS, hcomm]; simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, h1, Matrix.mul_one, Matrix.mul_one]
end Formalism.L2.SG.Pf.Unip
