-- Prove2me | solution 1 for CauchyRiemannIndex.czIndex_conj_path
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T10:49:48.366878+00:00
-- url     : https://prove2.me/submissions/8cbbad94-91ea-4270-bdc9-ef17484718db

import Definitions.Def_CauchyRiemannIndex_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_ConleyZehnder_czValue_existsUnique



namespace CauchyRiemannIndex

open Matrix

variable {n : ℕ}

lemma crc_CC : conjMat n * conjMat n = 1 := by
  simp [conjMat, fromBlocks_multiply, ← fromBlocks_one]

lemma crc_CJ : conjMat n * J₀ n = -(J₀ n * conjMat n) := by
  simp [conjMat, J₀, Matrix.J, fromBlocks_multiply, fromBlocks_neg]

lemma crc_CJC : conjMat n * J₀ n * conjMat n = -J₀ n := by
  rw [crc_CJ, Matrix.neg_mul, Matrix.mul_assoc, crc_CC, Matrix.mul_one]

lemma crc_CT : (conjMat n)ᵀ = conjMat n := by
  simp [conjMat, fromBlocks_transpose]

lemma crc_clp (A : Mat n) :
    complexLinearPart (conjMat n * A * conjMat n) =
      conjMat n * complexLinearPart A * conjMat n := by
  set C := conjMat n
  have h : J₀ n * (C * A * C) * J₀ n = C * (J₀ n * A * J₀ n) * C := by
    have e1 : J₀ n * C = -(C * J₀ n) := by rw [crc_CJ, neg_neg]
    calc J₀ n * (C * A * C) * J₀ n = (J₀ n * C) * A * (C * J₀ n) := by noncomm_ring
      _ = (C * J₀ n) * A * (J₀ n * C) := by rw [e1, crc_CJ]; noncomm_ring
      _ = C * (J₀ n * A * J₀ n) * C := by noncomm_ring
  unfold complexLinearPart
  rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

lemma crc_cld (A : Mat n) :
    complexLinearDet (conjMat n * A * conjMat n) = starRingEnd ℂ (complexLinearDet A) := by
  set M := complexLinearPart A
  have h11 : (conjMat n * M * conjMat n).toBlocks₁₁ = M.toBlocks₁₁ := by
    ext i j; simp [conjMat, toBlocks₁₁, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply]
  have h21 : (conjMat n * M * conjMat n).toBlocks₂₁ = -M.toBlocks₂₁ := by
    ext i j; simp [conjMat, toBlocks₂₁, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply]
  unfold complexLinearDet
  rw [crc_clp, h11, h21, RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Complex.conj_ofReal]
  ring

lemma crc_rhoHat (A : Mat n) :
    rhoHat (conjMat n * A * conjMat n) = starRingEnd ℂ (rhoHat A) := by
  unfold rhoHat
  rw [crc_cld, map_div₀, Complex.conj_ofReal, Complex.norm_conj]

lemma crc_symp {A : Mat n} (h : IsSymplectic A) : IsSymplectic (conjMat n * A * conjMat n) := by
  unfold IsSymplectic at *
  rw [SymplecticGroup.mem_iff] at *
  set C := conjMat n
  have hJ : (J₀ n) = Matrix.J (Fin n) ℝ := rfl
  rw [← hJ] at h ⊢
  rw [transpose_mul, transpose_mul, crc_CT]
  calc _ = C * A * (C * J₀ n * C) * Aᵀ * C := by noncomm_ring
    _ = -(C * (A * J₀ n * Aᵀ) * C) := by rw [crc_CJC]; noncomm_ring
    _ = J₀ n := by rw [h, crc_CJC, neg_neg]

lemma crc_det (A : Mat n) : (1 - conjMat n * A * conjMat n).det = (1 - A).det := by
  have : (1 : Mat n) - conjMat n * A * conjMat n = conjMat n * (1 - A) * conjMat n := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, crc_CC]
  rw [this, det_mul, det_mul, mul_comm, ← mul_assoc, ← det_mul, crc_CC, det_one, one_mul]

lemma crc_W (W : Mat n) (hW : W = Wplus n ∨ W = Wminus n) : conjMat n * W * conjMat n = W := by
  rcases hW with rfl | rfl
  · rw [Wplus, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, crc_CC]
  · ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [conjMat, Wminus, mul_apply, Fintype.sum_sum_type, fromBlocks, one_apply, diagonal_apply] <;>
      split_ifs <;> simp_all

lemma crc_isCZValue (ψ φ : C(unitInterval, Mat n))
    (hφ : ∀ t, φ t = conjMat n * ψ t * conjMat n) {k : ℤ} (hk : IsCZValue ψ k) :
    IsCZValue φ (-k) := by
  obtain ⟨χ, ⟨h0, hS, h1⟩, θ₁, θ₂, hθ₁, hθ₂, hsum⟩ := hk
  let χ' : C(unitInterval, Mat n) :=
    ⟨fun t => conjMat n * χ t * conjMat n,
      (continuous_const.matrix_mul χ.continuous).matrix_mul continuous_const⟩
  refine ⟨χ', ⟨?_, fun t => ?_, ?_⟩, fun t => -θ₁ t, fun t => -θ₂ t, ⟨hθ₁.1.neg, fun t => ?_⟩,
    ⟨hθ₂.1.neg, fun t => ?_⟩, ?_⟩
  · show conjMat n * χ 0 * conjMat n = φ 1
    rw [hφ, h0]
  · exact ⟨crc_symp (hS t).1, by show (1 - conjMat n * χ t * conjMat n).det ≠ 0; rw [crc_det]; exact (hS t).2⟩
  · show conjMat n * χ 1 * conjMat n = Wplus n ∨ conjMat n * χ 1 * conjMat n = Wminus n
    rw [crc_W _ h1]; exact h1
  · show rhoHat (φ t) = _
    rw [hφ, crc_rhoHat, show rhoHat (ψ t) = _ from hθ₁.2 t, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  · show rhoHat (conjMat n * χ t * conjMat n) = _
    rw [crc_rhoHat, show rhoHat (χ t) = _ from hθ₂.2 t, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  · push_cast
    linarith

lemma crc_czIndex_eq {ψ : C(unitInterval, Mat n)} (hSP : ψ ∈ ConleyZehnder.SP n) {k : ℤ}
    (hk : IsCZValue ψ k) : czIndex ψ = k := by
  obtain ⟨k', -, huniq⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hex : ∃ k, IsCZValue ψ k := ⟨k, hk⟩
  unfold czIndex
  rw [dif_pos hex]
  exact (huniq _ hex.choose_spec).trans (huniq _ hk).symm

theorem crc_czIndex_conj_path (n : ℕ) (ψ φ : C(unitInterval, Mat n))
    (hs : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0)
    (hφ : ∀ t, φ t = conjMat n * ψ t * conjMat n) :
    czIndex φ = -czIndex ψ := by
  have hSP : ψ ∈ ConleyZehnder.SP n := ⟨hs, h0, h1⟩
  have hSP' : φ ∈ ConleyZehnder.SP n := by
    refine ⟨fun t => ?_, ?_, ?_⟩
    · rw [hφ]; exact crc_symp (hs t)
    · rw [hφ, h0, Matrix.mul_one, crc_CC]
    · rw [hφ, crc_det]; exact h1
  obtain ⟨k, hk, -⟩ := ConleyZehnder.czValue_existsUnique ψ hSP
  have hk' : IsCZValue ψ k := hk
  rw [crc_czIndex_eq hSP hk', crc_czIndex_eq hSP' (crc_isCZValue ψ φ hφ hk')]

end CauchyRiemannIndex

open CauchyRiemannIndex

open MeasureTheory Matrix Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

theorem solution (n : ℕ) (ψ φ : C(unitInterval, Mat n))
    (hs : ∀ t, IsSymplectic (ψ t)) (h0 : ψ 0 = 1) (h1 : (1 - ψ 1).det ≠ 0)
    (hφ : ∀ t, φ t = conjMat n * ψ t * conjMat n) :
    czIndex φ = -czIndex ψ :=
  CauchyRiemannIndex.crc_czIndex_conj_path n ψ φ hs h0 h1 hφ
