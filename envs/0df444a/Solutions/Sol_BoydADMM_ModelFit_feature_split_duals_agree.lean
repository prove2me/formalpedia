-- Prove2me | solution 1 for BoydADMM.ModelFit.feature_split_duals_agree
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:08:27.197877+00:00
-- url     : https://prove2.me/submissions/0d77375b-ce4d-4111-8468-b6b92393a690

import Mathlib
import Definitions.Def_BoydADMM_ModelFit_Basic

open Matrix


namespace BoydADMM.ModelFit

lemma gl_tel_tel {m n k : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (N : Matrix (Fin n) (Fin k) ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    Matrix.toEuclideanLin M (Matrix.toEuclideanLin N x) = Matrix.toEuclideanLin (M * N) x := by
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma gl_inner_tel {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Matrix.toEuclideanLin A x) y = inner ℝ x (Matrix.toEuclideanLin Aᵀ y) := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint A
  rw [conjTranspose_eq_transpose_of_trivial] at h
  rw [h, LinearMap.adjoint_inner_right]

lemma gl_tel_ridge {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (ν : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Matrix.toEuclideanLin (P + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) x =
      Matrix.toEuclideanLin P x + ν • x := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply]
  simp

lemma gl_posDef {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef := by
  have h1 : (Aᵀ * A).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self A
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  exact Matrix.PosDef.posSemidef_add h1 (Matrix.PosDef.one.smul hν)

lemma gl_inv_mul {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (ν : ℝ) (hν : 0 < ν) :
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) = 1 ∧
    (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)) * (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ = 1 := by
  have hd : IsUnit (Aᵀ * A + ν • (1 : Matrix (Fin n) (Fin n) ℝ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (gl_posDef A ν hν).isUnit
  exact ⟨Matrix.nonsing_inv_mul _ hd, Matrix.mul_nonsing_inv _ hd⟩

lemma gl_unique_of_growth {E : Type*} [NormedAddCommGroup E] (f : E → ℝ) (x0 : E) (c : ℝ)
    (hc : 0 < c) (hg : ∀ y, f x0 + c * ‖y - x0‖ ^ 2 ≤ f y) (x : E) :
    IsMinOn f Set.univ x ↔ x = x0 := by
  rw [isMinOn_iff]
  constructor
  · intro hx
    have h1 := hx x0 (Set.mem_univ x0)
    have h2 := hg x
    have h3 : c * ‖x - x0‖ ^ 2 ≤ 0 := by linarith
    have h4 : ‖x - x0‖ ^ 2 = 0 := le_antisymm (by nlinarith [sq_nonneg ‖x - x0‖]) (sq_nonneg _)
    have : ‖x - x0‖ = 0 := by simpa using h4
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl y _
    have := hg y
    nlinarith [sq_nonneg ‖y - x‖]

lemma fs_smul_mean {N m : ℕ} (hN : 0 < N) (y : EuclideanSpace ℝ (Fin m)) :
    (N : ℝ) • ((N : ℝ)⁻¹ • y) = y := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [smul_smul, mul_inv_cancel₀ hN', one_smul]

lemma fs_sum_const {N m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    (∑ _i : Fin N, y) = (N : ℝ) • y := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.cast_smul_eq_nsmul]

lemma fs_decomp {N m : ℕ} (hN : 0 < N) (c z : Fin N → EuclideanSpace ℝ (Fin m)) :
    ∑ i, ‖c i - z i‖ ^ 2 =
      ∑ i, ‖z i - (N : ℝ)⁻¹ • (∑ j, z j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 +
        (N : ℝ) * ‖(N : ℝ)⁻¹ • (∑ j, z j) - (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 := by
  set Mz := (N : ℝ)⁻¹ • (∑ j, z j) with hMz
  set Mc := (N : ℝ)⁻¹ • (∑ j, c j) with hMc
  set e := Mz - Mc
  have hd : ∀ i, c i - z i = -((z i - Mz - c i + Mc) + e) := by intro i; simp only [e]; abel
  have hsum : ∑ i, (z i - Mz - c i + Mc) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, fs_sum_const,
      fs_sum_const, hMz, hMc, fs_smul_mean hN, fs_smul_mean hN]
    abel
  simp_rw [hd, norm_neg, norm_add_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
    inner_zero_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem fs_duals_core {N m : ℕ} {n : Fin N → ℕ} (hN : 0 < N)
    (A : ∀ i, Matrix (Fin m) (Fin (n i)) ℝ) (l : EuclideanSpace ℝ (Fin m) → ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : ∀ i, EuclideanSpace ℝ (Fin (n i))) (u z u' : Fin N → EuclideanSpace ℝ (Fin m))
    (hu' : ∀ i, u' i = u i + Matrix.toEuclideanLin (A i) (x i) - z i) :
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z ↔
      (IsMinOn (fun zb : EuclideanSpace ℝ (Fin m) =>
          l ((N : ℝ) • zb - b) + (N : ℝ) * ρ / 2 *
            ‖zb - (N : ℝ)⁻¹ • (∑ i, Matrix.toEuclideanLin (A i) (x i))
              - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2)
          Set.univ ((N : ℝ)⁻¹ • (∑ i, z i)) ∧
        ∀ i, z i = (N : ℝ)⁻¹ • (∑ j, z j) + Matrix.toEuclideanLin (A i) (x i) + u i
          - (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
          - (N : ℝ)⁻¹ • (∑ j, u j))) ∧
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z →
      ∀ i, u' i = (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
        + (N : ℝ)⁻¹ • (∑ j, u j) - (N : ℝ)⁻¹ • (∑ j, z j)) := by
  set a : Fin N → EuclideanSpace ℝ (Fin m) := fun i => Matrix.toEuclideanLin (A i) (x i) with ha
  set c : Fin N → EuclideanSpace ℝ (Fin m) := fun i => a i + u i with hc
  have hMc : (N : ℝ)⁻¹ • (∑ j, c j) = (N : ℝ)⁻¹ • (∑ j, a j) + (N : ℝ)⁻¹ • (∑ j, u j) := by
    rw [hc]; simp only; rw [Finset.sum_add_distrib, smul_add]
  set F := fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖a i - z' i + u i‖ ^ 2 with hF
  set G := fun zb : EuclideanSpace ℝ (Fin m) =>
          l ((N : ℝ) • zb - b) + (N : ℝ) * ρ / 2 *
            ‖zb - (N : ℝ)⁻¹ • (∑ i, a i) - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2 with hG
  -- the decomposition F z' = G (mean z') + ρ/2 Σ ‖d_i‖²
  have hFG : ∀ z' : Fin N → EuclideanSpace ℝ (Fin m), F z' = G ((N : ℝ)⁻¹ • (∑ j, z' j)) +
      ρ / 2 * ∑ i, ‖z' i - (N : ℝ)⁻¹ • (∑ j, z' j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 := by
    intro z'
    simp only [hF, hG]
    rw [fs_smul_mean hN, ← Finset.mul_sum]
    have e1 : ∀ i, a i - z' i + u i = c i - z' i := by intro i; simp only [hc]; abel
    simp_rw [e1]
    rw [fs_decomp hN c z', hMc, sub_sub _ ((N : ℝ)⁻¹ • ∑ i, a i)]
    ring
  have hd0 : ∀ z' : Fin N → EuclideanSpace ℝ (Fin m),
      (∀ i, z' i - (N : ℝ)⁻¹ • (∑ j, z' j) - c i + (N : ℝ)⁻¹ • (∑ j, c j) = 0) ↔
      (∀ i, z' i = (N : ℝ)⁻¹ • (∑ j, z' j) + a i + u i
          - (N : ℝ)⁻¹ • (∑ j, a j) - (N : ℝ)⁻¹ • (∑ j, u j)) := by
    intro z'
    refine forall_congr' (fun i => ?_)
    rw [hMc]; simp only [hc]
    constructor
    · intro h; rw [← sub_eq_zero, ← h]; abel
    · intro h; rw [h]; abel
  -- construction of a point with prescribed mean and zero deviations
  have hlift : ∀ zb : EuclideanSpace ℝ (Fin m),
      F (fun i => zb + c i - (N : ℝ)⁻¹ • (∑ j, c j)) = G zb := by
    intro zb
    have hm : (N : ℝ)⁻¹ • (∑ j, (zb + c j - (N : ℝ)⁻¹ • (∑ j, c j))) = zb := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, fs_sum_const zb,
        fs_sum_const ((N : ℝ)⁻¹ • (∑ j, c j)), fs_smul_mean hN, add_sub_cancel_right, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hN.ne' : (N : ℝ) ≠ 0), one_smul]
    rw [hFG, hm]
    have : ∀ i, zb + c i - (N : ℝ)⁻¹ • (∑ j, c j) - zb - c i + (N : ℝ)⁻¹ • (∑ j, c j) = 0 := by
      intro i; abel
    simp [this]
  have hnn : ∀ z' : Fin N → EuclideanSpace ℝ (Fin m), 0 ≤ ρ / 2 * ∑ i,
      ‖z' i - (N : ℝ)⁻¹ • (∑ j, z' j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 :=
    fun z' => mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => by positivity))
  have main : IsMinOn F Set.univ z ↔ (IsMinOn G Set.univ ((N : ℝ)⁻¹ • (∑ i, z i)) ∧
      ∀ i, z i - (N : ℝ)⁻¹ • (∑ j, z j) - c i + (N : ℝ)⁻¹ • (∑ j, c j) = 0) := by
    simp only [isMinOn_iff, Set.mem_univ, true_implies]
    constructor
    · intro hz
      have hGz : ∀ zb, G ((N : ℝ)⁻¹ • (∑ i, z i)) ≤ G zb := by
        intro zb
        have := hz (fun i => zb + c i - (N : ℝ)⁻¹ • (∑ j, c j))
        rw [hlift, hFG] at this
        linarith [hnn z]
      refine ⟨hGz, ?_⟩
      have := hz (fun i => (N : ℝ)⁻¹ • (∑ i, z i) + c i - (N : ℝ)⁻¹ • (∑ j, c j))
      rw [hlift, hFG] at this
      have hs : ∑ i, ‖z i - (N : ℝ)⁻¹ • (∑ j, z j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 = 0 := by
        have h1 := hnn z
        have h2 : ρ / 2 * ∑ i, ‖z i - (N : ℝ)⁻¹ • (∑ j, z j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2
            = 0 := by linarith
        rcases mul_eq_zero.mp h2 with h | h
        · linarith
        · exact h
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp hs i
        (Finset.mem_univ _)
      simpa using this
    · rintro ⟨hG', hd⟩ z'
      rw [hFG z, hFG z']
      have : ∑ i, ‖z i - (N : ℝ)⁻¹ • (∑ j, z j) - c i + (N : ℝ)⁻¹ • (∑ j, c j)‖ ^ 2 = 0 := by
        simp [hd]
      rw [this, mul_zero, add_zero]
      linarith [hG' ((N : ℝ)⁻¹ • (∑ j, z' j)), hnn z']
  refine ⟨?_, ?_⟩
  · rw [main, hd0 z]
  · intro hz i
    have h2 := ((hd0 z).mp (main.mp hz).2) i
    rw [hu' i]
    change u i + a i - z i = _
    rw [h2]; abel

end BoydADMM.ModelFit

open BoydADMM.ModelFit


theorem solution {N m : ℕ} {n : Fin N → ℕ} (hN : 0 < N)
    (A : ∀ i, Matrix (Fin m) (Fin (n i)) ℝ) (l : EuclideanSpace ℝ (Fin m) → ℝ)
    (hl : ConvexOn ℝ Set.univ l) (b : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) (hρ : 0 < ρ)
    (x : ∀ i, EuclideanSpace ℝ (Fin (n i))) (u z u' : Fin N → EuclideanSpace ℝ (Fin m))
    (hu' : ∀ i, u' i = u i + Matrix.toEuclideanLin (A i) (x i) - z i) :
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z ↔
      (IsMinOn (fun zb : EuclideanSpace ℝ (Fin m) =>
          l ((N : ℝ) • zb - b) + (N : ℝ) * ρ / 2 *
            ‖zb - (N : ℝ)⁻¹ • (∑ i, Matrix.toEuclideanLin (A i) (x i))
              - (N : ℝ)⁻¹ • (∑ i, u i)‖ ^ 2)
          Set.univ ((N : ℝ)⁻¹ • (∑ i, z i)) ∧
        ∀ i, z i = (N : ℝ)⁻¹ • (∑ j, z j) + Matrix.toEuclideanLin (A i) (x i) + u i
          - (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
          - (N : ℝ)⁻¹ • (∑ j, u j))) ∧
    (IsMinOn (fun z' : Fin N → EuclideanSpace ℝ (Fin m) =>
        l ((∑ i, z' i) - b) + ∑ i, ρ / 2 * ‖Matrix.toEuclideanLin (A i) (x i) - z' i + u i‖ ^ 2)
        Set.univ z →
      ∀ i, u' i = (N : ℝ)⁻¹ • (∑ j, Matrix.toEuclideanLin (A j) (x j))
        + (N : ℝ)⁻¹ • (∑ j, u j) - (N : ℝ)⁻¹ • (∑ j, z j)) := by
  exact fs_duals_core hN A l b ρ hρ x u z u' hu'
