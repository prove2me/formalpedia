-- Prove2me | solution 1 for Formalism.UG.P.fSatake_cell_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:08.287245+00:00
-- url     : https://prove2.me/submissions/e09b03fd-0410-426e-953c-029eb1bd6fa4

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Theorems.Thm_Formalism_UG_P_fSatake_borel_of_diag
import Theorems.Thm_Formalism_UG_P_fSatake_ne_zero_of_borel
import Theorems.Thm_Formalism_UG_P_fSatake_tMat_apply_lt
import Theorems.Thm_Formalism_UG_P_fSatake_borel_tMat
import Theorems.Thm_Formalism_UG_P_fSatake_tMat_exists
import Theorems.Thm_Formalism_UG_P_fSatake_diag_mem_K
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG
noncomputable section
namespace Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
private lemma isBorelU_mul {b c : GU σ n} (hb : IsBorelU b) (hc : IsBorelU c) :
    IsBorelU (b * c) := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  have hC : Matrix.BlockTriangular ⟪c⟫ id := fun i j h => hc i j h
  intro i j hij
  show (⟪b⟫ * ⟪c⟫) i j = 0
  exact (hB.mul hC) hij
private lemma isBorelU_inv {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  have hB : Matrix.BlockTriangular ⟪b⟫ id := fun i j h => hb i j h
  letI : Invertible ⟪b⟫ := Units.invertible _
  have hinv : ⟪b⁻¹⟫ = (⟪b⟫)⁻¹ := by simp [Matrix.coe_units_inv]
  intro i j hij
  change ⟪b⁻¹⟫ i j = 0
  rw [hinv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hB hij
private lemma isBorelU_sigma_diag_mul_opposite_diag {b : GU σ n} (hb : IsBorelU b) (i j : Fin n)
    (hij : (i : ℕ) + j + 1 = n) : σ (⟪b⟫ i i) * ⟪b⟫ j j = 1 := by
  have hB : ∀ p q : Fin n, q < p → ⟪b⟫ p q = 0 := fun p q h => hb p q h
  have hG : cT σ ⟪b⟫ * antiJ L n * ⟪b⟫ = antiJ L n := b.2
  have hG' := congrFun (congrFun hG i) j
  simp only [Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply, antiJ] at hG'
  rw [if_pos hij, Finset.sum_eq_single j] at hG'
  · rw [Finset.sum_eq_single i, if_pos hij, mul_one] at hG'
    · exact hG'
    · intro p _ hp
      rw [if_neg (fun h => hp (Fin.ext (by omega))), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with hlt | hgt
    · have hlt' := Fin.lt_iff_val_lt_val.mp hlt
      rw [Finset.sum_eq_zero, zero_mul]
      intro p _
      by_cases hp : (p : ℕ) + q + 1 = n
      · rw [hB p i (Fin.lt_iff_val_lt_val.mpr (by omega)), map_zero, zero_mul]
      · rw [if_neg hp, mul_zero]
    · rw [hB q j hgt, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
private lemma isBorelU_mul_diag {A B : GU σ n} (hA : IsBorelU A) (hB : IsBorelU B) (i : Fin n) :
    ⟪A * B⟫ i i = ⟪A⟫ i i * ⟪B⟫ i i := by
  show (⟪A⟫ * ⟪B⟫) i i = _
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA i l h, zero_mul]
    · rw [hB l i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
private lemma tMat_diag_mul_opposite_diag {ϖ : L} (hϖ0 : ϖ ≠ 0) {m : ℕ} (hm : 2 * m ≤ n) (a : Fin m → ℤ)
    (i j : Fin n) (hij : (i : ℕ) + j + 1 = n) : tMat ϖ n m a i i * tMat ϖ n m a j j = 1 := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> first
    | omega
    | (simp; done)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [add_neg_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)
    | (rw [← zpow_add₀ hϖ0]; convert zpow_zero ϖ using 2; rw [neg_add_eq_zero]; congr 1;
        simp only [Fin.mk.injEq]; omega)
private lemma sigma_tMat_diag {ϖ : L} (hσ : σ ϖ = ϖ) {m : ℕ} (a : Fin m → ℤ) (i : Fin n) :
    σ (tMat ϖ n m a i i) = tMat ϖ n m a i i := by
  simp only [tMat, Matrix.diagonal_apply_eq]
  split_ifs <;> simp [map_zpow₀, hσ]
private lemma valuation_eq_ofAdd_neg_ordL {x : L} (hx : x ≠ 0) :
    Valued.v x = ↑(Multiplicative.ofAdd (-ordL x)) := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dif_neg hv, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]
private lemma valuation_zpow_uniformizer {ϖ : L} (hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ))) (a : ℤ) :
    Valued.v (ϖ ^ a) = ((Multiplicative.ofAdd (-a) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
  congr 1
  rw [← ofAdd_zsmul]
  simp
private lemma withZero_eq_one_of_mul_self_eq_one {x : WithZero (Multiplicative ℤ)} (h : x * x = 1) : x = 1 := by
  have hx : x ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  obtain ⟨y, rfl⟩ := WithZero.ne_zero_iff_exists.mp hx
  rw [← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj] at h
  rw [← WithZero.coe_one, WithZero.coe_inj]
  have h3 := congrArg Multiplicative.toAdd h
  rw [toAdd_mul, toAdd_one] at h3
  have h2 : Multiplicative.toAdd y = 0 := by omega
  rw [← ofAdd_toAdd y, h2, ofAdd_zero]
end Formalism.UG.P
end
end

set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {ϖ : L} {q m : ℕ} (hU : IsUnramInv ϖ σ q) (hm : 2 * m ≤ n)
    (hm' : n ≤ 2 * m + 1) {b k : GU σ n} (hb : IsBorelU b) (hk : k ∈ KU σ n) :
    ∃ a : Fin m → ℤ, ∃ u : GU σ n, IsUnipU u ∧ ∃ k' ∈ KU σ n,
      ⟪b * k⟫ = tMat ϖ n m a * ⟪u⟫ * ⟪k'⟫ := by
  have hϖ : Valued.v ϖ = ↑(Multiplicative.ofAdd (-1 : ℤ)) := by
    obtain ⟨-, -, -, h, -⟩ := hU
    exact h
  have hσ : σ ϖ = ϖ := by
    obtain ⟨-, -, h, -⟩ := hU
    exact h
  have hσv : ∀ x, Valued.v (σ x) = Valued.v x := by
    obtain ⟨-, h, -⟩ := hU
    exact h
  have hϖ0 : ϖ ≠ 0 := fun h => by
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hbne : ∀ i, ⟪b⟫ i i ≠ 0 := fSatake_ne_zero_of_borel hb
  obtain ⟨a, ha⟩ : ∃ a : Fin m → ℤ, ∀ i : Fin m, ∀ hi : (i : ℕ) < n,
      a i = ordL (⟪b⟫ ⟨i, hi⟩ ⟨i, hi⟩) :=
    ⟨fun i => ordL (⟪b⟫ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩ ⟨i, lt_of_lt_of_le i.isLt (by omega)⟩),
      fun i hi => rfl⟩
  obtain ⟨t, ht⟩ := fSatake_tMat_exists hU hm a
  have htB : IsBorelU t := fSatake_borel_tMat ht
  have hT0 : ∀ i : Fin n, tMat ϖ n m a i i ≠ 0 := fun i h => by
    have hi := i.isLt
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i ⟨n - 1 - i, by omega⟩
      (by show (i : ℕ) + (n - 1 - (i : ℕ)) + 1 = n; omega)
    rw [h, zero_mul] at h2
    exact zero_ne_one h2
  obtain ⟨e, he⟩ : ∃ e : Fin n → L, ∀ i, e i = ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹ :=
    ⟨fun i => ⟪b⟫ i i * (tMat ϖ n m a i i)⁻¹, fun i => rfl⟩
  have he0 : ∀ i, e i ≠ 0 := fun i => by
    rw [he]
    exact mul_ne_zero (hbne i) (inv_ne_zero (hT0 i))
  have hrel : ∀ i j : Fin n, (i : ℕ) + j + 1 = n → σ (e i) * e j = 1 := by
    intro i j hij
    have h1 := isBorelU_sigma_diag_mul_opposite_diag hb i j hij
    have h2 := tMat_diag_mul_opposite_diag hϖ0 hm a i j hij
    rw [he, he, map_mul, map_inv₀, sigma_tMat_diag hσ a i]
    calc σ (⟪b⟫ i i) * (tMat ϖ n m a i i)⁻¹ * (⟪b⟫ j j * (tMat ϖ n m a j j)⁻¹)
        = (σ (⟪b⟫ i i) * ⟪b⟫ j j) * (tMat ϖ n m a i i * tMat ϖ n m a j j)⁻¹ := by ring
      _ = 1 := by rw [h1, h2, inv_one, mul_one]
  have hlow : ∀ i : Fin n, (i : ℕ) < m → Valued.v (e i) = 1 := by
    intro i hi
    have hT : tMat ϖ n m a i i = ϖ ^ (ordL (⟪b⟫ i i)) := by
      have h1 := fSatake_tMat_apply_lt ϖ a ⟨i, hi⟩ i.isLt
      rw [ha ⟨i, hi⟩ i.isLt] at h1
      exact h1
    rw [he, map_mul, map_inv₀, hT, valuation_zpow_uniformizer hϖ, valuation_eq_ofAdd_neg_ordL (hbne i)]
    exact mul_inv_cancel₀ WithZero.coe_ne_zero
  have hve : ∀ i, Valued.v (e i) = 1 := by
    intro i
    by_cases hi : (i : ℕ) < m
    · exact hlow i hi
    · have hin := i.isLt
      obtain ⟨j, hjv⟩ : ∃ j : Fin n, (j : ℕ) = n - 1 - i := ⟨⟨n - 1 - i, by omega⟩, rfl⟩
      have hij : (i : ℕ) + j + 1 = n := by omega
      have h1 := congrArg Valued.v (hrel i j hij)
      rw [map_mul, hσv, map_one] at h1
      by_cases hj : (j : ℕ) < m
      · rw [hlow j hj, mul_one] at h1
        exact h1
      · have hji : j = i := Fin.ext (by omega)
        rw [hji] at h1
        exact withZero_eq_one_of_mul_self_eq_one h1
  have hd1 : Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (he0 i)
  have hd2 : Matrix.diagonal (fun i => (e i)⁻¹) * Matrix.diagonal e = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he0 i)
  have hmemD : (⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩ : GL (Fin n) L) ∈ GU σ n := by
    show cT σ (Matrix.diagonal e) * antiJ L n * Matrix.diagonal e = antiJ L n
    rw [cT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    ext i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [antiJ]
    split_ifs with h
    · rw [mul_one]
      exact hrel i j h
    · simp
  let D0 : GU σ n := ⟨⟨Matrix.diagonal e, Matrix.diagonal (fun i => (e i)⁻¹), hd1, hd2⟩, hmemD⟩
  have hD0 : ⟪D0⟫ = Matrix.diagonal e := rfl
  have hD0i : ⟪D0⁻¹⟫ = Matrix.diagonal (fun i => (e i)⁻¹) := rfl
  have hD0K : D0 ∈ KU σ n := fSatake_diag_mem_K hD0 hD0i hve
  have hD0B : IsBorelU D0 := fSatake_borel_of_diag hD0
  have htinv : ∀ i, ⟪t⁻¹⟫ i i = (tMat ϖ n m a i i)⁻¹ := fun i => by
    have h1 := isBorelU_mul_diag (isBorelU_inv htB) htB i
    rw [inv_mul_cancel, ht] at h1
    have h0 : ⟪(1 : GU σ n)⟫ i i = 1 := by simp
    rw [h0] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  have huB : IsBorelU (t⁻¹ * b * D0⁻¹) :=
    isBorelU_mul (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B)
  have hudiag : ∀ i, ⟪t⁻¹ * b * D0⁻¹⟫ i i = 1 := fun i => by
    rw [isBorelU_mul_diag (isBorelU_mul (isBorelU_inv htB) hb) (isBorelU_inv hD0B),
      isBorelU_mul_diag (isBorelU_inv htB) hb, htinv, hD0i, Matrix.diagonal_apply_eq, he]
    field_simp [hbne i, hT0 i]
  have huU : IsUnipU (t⁻¹ * b * D0⁻¹) := by
    unfold IsUnipU
    exact ⟨huB, hudiag⟩
  refine ⟨a, t⁻¹ * b * D0⁻¹, huU, D0 * k, (KU σ n).mul_mem hD0K hk, ?_⟩
  have hgrp : b * k = t * (t⁻¹ * b * D0⁻¹) * (D0 * k) := by group
  rw [hgrp]
  show ⟪t⟫ * ⟪t⁻¹ * b * D0⁻¹⟫ * ⟪D0 * k⟫ = _
  rw [ht]
end Formalism.UG.P
