-- Prove2me | solution 1 for ExactSDPDuality.ELSD.prop7_vii
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:02:30.822831+00:00
-- url     : https://prove2.me/submissions/fe74b2d4-7b28-42a0-98b5-8c68b8ba813d

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

theorem aux_p7vii_symm {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) : Uᵀ = U := by
  have h1 := h.isHermitian
  rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h1
  rw [transpose_sub, transpose_mul, transpose_transpose] at h1
  simpa using h1

theorem aux_p7vii_ker {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) (x : Fin n → ℝ) (hx : U *ᵥ x = 0) :
    Wᵀ *ᵥ x = 0 := by
  have h1 := h.dotProduct_mulVec_nonneg x
  have h2 : star x ⬝ᵥ ((U - W * Wᵀ) *ᵥ x) = - ((Wᵀ *ᵥ x) ⬝ᵥ (Wᵀ *ᵥ x)) := by
    rw [star_trivial, sub_mulVec, dotProduct_sub, hx, dotProduct_zero, ← mulVec_mulVec,
      dotProduct_mulVec, ← mulVec_transpose]
    ring
  have h3 : (Wᵀ *ᵥ x) ⬝ᵥ (Wᵀ *ᵥ x) = 0 := by
    have := dotProduct_self_star_nonneg (Wᵀ *ᵥ x)
    rw [star_trivial] at this
    linarith
  exact dotProduct_self_eq_zero.mp h3

theorem aux_p7vii_range {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) (v : Fin n → ℝ) :
    W *ᵥ v ∈ LinearMap.range U.mulVecLin := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  set x : Fin n → ℝ := fun i => φ (Pi.single i 1) with hxdef
  have hrep : ∀ w : Fin n → ℝ, φ w = x ⬝ᵥ w := by
    intro w
    rw [LinearMap.pi_apply_eq_sum_univ φ w, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hxdef, smul_eq_mul]
    rw [mul_comm]
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  have hUx : U *ᵥ x = 0 := by
    have hsymm := aux_p7vii_symm U W h
    have : x ᵥ* U = 0 := by
      ext j
      have := hφ (U *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
      rw [hrep, dotProduct_mulVec] at this
      simpa [dotProduct_single] using this
    rw [← hsymm, mulVec_transpose]
    exact this
  have hWx := aux_p7vii_ker U W h x hUx
  rw [hrep, dotProduct_mulVec, ← mulVec_transpose, hWx, zero_dotProduct]

theorem aux_p7vii_main {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, W = U * H := by
  have hc : ∀ j : Fin n, ∃ y : Fin n → ℝ, U *ᵥ y = W *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := aux_p7vii_range U W h (Pi.single j 1)
    exact ⟨y, hy⟩
  choose y hy using hc
  refine ⟨Matrix.of fun i j => y j i, ?_⟩
  ext i j
  have := congrFun (hy j) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  rw [mul_apply]
  simp only [of_apply]
  exact this.symm

end ExactSDPDuality.ELSD

open ExactSDPDuality.ELSD
open Matrix

theorem solution {n : ℕ} (U W : Matrix (Fin n) (Fin n) ℝ)
    (h : (U - W * Wᵀ).PosSemidef) :
    ∃ H : Matrix (Fin n) (Fin n) ℝ, W = U * H :=
  aux_p7vii_main U W h
