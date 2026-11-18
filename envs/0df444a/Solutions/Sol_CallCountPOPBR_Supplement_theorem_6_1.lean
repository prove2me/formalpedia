-- Prove2me | solution 1 for CallCountPOPBR.Supplement.theorem_6_1
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T15:31:37.506205+00:00
-- url     : https://prove2.me/submissions/ee0cfc3d-5a2f-453b-aced-e9f25a6f0f07

import Mathlib

set_option autoImplicit false

namespace CC61Aux

open Matrix

variable (C : ℕ → ℕ) (d : ℕ) (a : ℕ → ℕ → ℕ)

/-- state vector -/
def V (n : ℕ) : Fin (d + 1) → ℚ := fun i => if i.val < d then (C (n - i.val) : ℚ) else 1

/-- transition matrix -/
def M (n : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ := Matrix.of fun i j =>
  if i.val = 0 then (if j.val < d then (a (j.val + 1) n : ℚ) else 1)
  else if i.val < d then (if j.val + 1 = i.val then 1 else 0)
  else (if j.val = d then 1 else 0)

def prodM (n : ℕ) : ℕ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℚ
  | 0 => 1
  | k + 1 => M d a (n + k + 1) * prodM n k

lemma V_zero (n : ℕ) (hd : 1 ≤ d) : V C d n ⟨0, by omega⟩ = C n := by
  simp [V]; omega

lemma step (N₀ : ℕ) (hN₀ : d ≤ N₀) (hd : 1 ≤ d)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (m : ℕ) (hm : N₀ ≤ m) : V C d (m + 1) = M d a (m + 1) *ᵥ V C d m := by
  funext i
  simp only [mulVec, dotProduct, M, Matrix.of_apply]
  by_cases hi0 : i.val = 0
  · simp only [hi0, if_true]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.is_lt, if_true, Fin.val_last, lt_irrefl, if_false]
    have hV : V C d (m + 1) i = C (m + 1) := by simp [V, hi0]; omega
    rw [hV, hrec (m + 1) (by omega)]
    simp only [V, Fin.val_castSucc, Fin.is_lt, if_true, Fin.val_last, lt_irrefl, if_false, mul_one]
    push_cast
    rw [add_comm (1 : ℚ)]
    congr 1
    rw [Fin.sum_univ_eq_sum_range (fun j => (a (j + 1) (m + 1) : ℚ) * (C (m - j) : ℚ)) d]
    have : Finset.Icc 1 d = Finset.Ico 1 (d + 1) := rfl
    rw [this, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [add_comm 1 k]
    congr 3
    omega
  · by_cases hid : i.val < d
    · simp only [hi0, if_false, hid, if_true]
      rw [Finset.sum_eq_single ⟨i.val - 1, by omega⟩]
      · simp only [V, hid, if_true]
        have h1 : i.val - 1 + 1 = i.val := by omega
        have h2 : i.val - 1 < d := by omega
        simp only [h1, h2, if_true, one_mul]
        congr 2
        omega
      · intro b _ hb
        have : ¬ (b.val + 1 = i.val) := by
          intro h; apply hb; ext; simp; omega
        simp [this]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hid' : i.val = d := by omega
      simp only [hi0, if_false, hid, hid']
      rw [Finset.sum_eq_single (Fin.last d)]
      · simp [V, hid]
      · intro b _ hb
        have : ¬ (b.val = d) := by
          intro h; apply hb; ext; simp [h]
        simp [this]
        intro h; omega
      · intro h; exact absurd (Finset.mem_univ _) h

lemma M_per (p N₀ : ℕ) (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n)
    (n : ℕ) (hn : N₀ ≤ n) : M d a (n + p) = M d a n := by
  ext i j
  simp only [M, Matrix.of_apply]
  split_ifs with h1 h2 <;> try rfl
  rw [hper n hn (j.val + 1) (by simp; omega)]

lemma prodM_per (p N₀ : ℕ) (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n)
    (n : ℕ) (hn : N₀ ≤ n) (k : ℕ) : prodM d a (n + p) k = prodM d a n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [prodM, ih]
    rw [show n + p + k + 1 = (n + k + 1) + p by ring, M_per d a p N₀ hper _ (by omega)]

lemma prodM_shift (n k : ℕ) : prodM d a n (k + 1) = prodM d a (n + 1) k * M d a (n + 1) := by
  induction k with
  | zero => simp [prodM]
  | succ k ih =>
    rw [prodM, ih, prodM, mul_assoc]
    congr 2
    ring

lemma V_prod (N₀ : ℕ) (hN₀ : d ≤ N₀) (hd : 1 ≤ d)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (n : ℕ) (hn : N₀ ≤ n) (k : ℕ) : V C d (n + k) = prodM d a n k *ᵥ V C d n := by
  induction k with
  | zero => simp [prodM]
  | succ k ih =>
    rw [← add_assoc, step C d a N₀ hN₀ hd hrec (n + k) (by omega), ih, prodM, mulVec_mulVec]

lemma V_pow (p N₀ : ℕ) (hN₀ : d ≤ N₀) (hd : 1 ≤ d)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n)
    (n : ℕ) (hn : N₀ ≤ n) (k : ℕ) :
    V C d (n + k * p) = (prodM d a n p) ^ k *ᵥ V C d n := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hA : prodM d a (n + k * p) p = prodM d a n p := by
      clear ih
      induction k with
      | zero => simp
      | succ k ih2 =>
        rw [show n + (k + 1) * p = (n + k * p) + p by ring,
          prodM_per d a p N₀ hper _ (by omega), ih2]
    rw [show n + (k + 1) * p = (n + k * p) + p by ring,
      V_prod C d a N₀ hN₀ hd hrec _ (by omega) p, hA, ih, mulVec_mulVec, pow_succ']

lemma charpoly_const (p N₀ : ℕ) (hp : 1 ≤ p)
    (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n)
    (n : ℕ) (hn : N₀ ≤ n) : (prodM d a (n + 1) p).charpoly = (prodM d a n p).charpoly := by
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  rw [prodM_shift d a n r, prodM, show n + 1 + r + 1 = (n + 1) + (r + 1) by ring,
    M_per d a (r + 1) N₀ hper _ (by omega), charpoly_mul_comm]

lemma part1 (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) (a : ℕ → ℕ → ℕ) (N₀ : ℕ)
    (hN₀ : d ≤ N₀)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n) :
    ∃ (q : ℕ → ℚ) (N₁ : ℕ), q (d + 1) = 1 ∧
      ∀ n, N₁ ≤ n → ∑ k ∈ Finset.range (d + 2), q k * (C (n + k * p) : ℚ) = 0 := by
  set χ := (prodM d a N₀ p).charpoly with hχ
  have hdeg : χ.natDegree = d + 1 := by
    rw [hχ, charpoly_natDegree_eq_dim]; simp
  refine ⟨fun k => χ.coeff k, N₀, ?_, ?_⟩
  · have := (charpoly_monic (prodM d a N₀ p)).coeff_natDegree
    rw [← hχ, hdeg] at this; exact this
  · intro n hn
    have hc : (prodM d a n p).charpoly = χ := by
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih => rw [charpoly_const d a p N₀ hp hper n hn, ih]
    have hCH := aeval_self_charpoly (prodM d a n p)
    rw [hc, Polynomial.aeval_eq_sum_range, hdeg] at hCH
    have h2 := congrFun (congrArg (fun A => A *ᵥ V C d n) hCH) ⟨0, by omega⟩
    simp only [sum_mulVec, zero_mulVec, Pi.zero_apply, Finset.sum_apply] at h2
    rw [← h2]
    apply Finset.sum_congr rfl
    intro k _
    rw [smul_mulVec, Pi.smul_apply, ← V_pow C d a p N₀ hN₀ hd hrec hper n hn k,
      V_zero C d _ hd, smul_eq_mul]

end CC61Aux

theorem solution (C : ℕ → ℕ) (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) (a : ℕ → ℕ → ℕ) (N₀ : ℕ)
    (hN₀ : d ≤ N₀)
    (hrec : ∀ n, N₀ ≤ n → C n = 1 + ∑ j ∈ Finset.Icc 1 d, a j n * C (n - j))
    (hper : ∀ n, N₀ ≤ n → ∀ j ∈ Finset.Icc 1 d, a j (n + p) = a j n) :
    (∃ (q : ℕ → ℚ) (N₁ : ℕ), q (d + 1) = 1 ∧
      ∀ n, N₁ ≤ n → ∑ k ∈ Finset.range (d + 2), q k * (C (n + k * p) : ℚ) = 0) ∧
    (∃ P Q : Polynomial ℚ, Q.coeff 0 = 1 ∧
      PowerSeries.mk (fun n => (C n : ℚ)) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ)) := by
  have h1 := CC61Aux.part1 C d p hd hp a N₀ hN₀ hrec hper
  refine ⟨h1, ?_⟩
  obtain ⟨q, N₁, hq1, hq⟩ := h1
  let Q : Polynomial ℚ := ∑ k ∈ Finset.range (d + 2),
    Polynomial.C (q k) * Polynomial.X ^ ((d + 1 - k) * p)
  have hQ0 : Q.coeff 0 = 1 := by
    simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (d + 1)]
    · simp [hq1]
    · intro k hk hk'
      rw [Finset.mem_range] at hk
      have : (d + 1 - k) * p ≠ 0 := by
        apply Nat.mul_ne_zero <;> omega
      simp [Ne.symm this]
    · intro h; exact absurd (by simp) h
  set f := PowerSeries.mk (fun n => (C n : ℚ)) * (Q : PowerSeries ℚ) with hf
  have hcoeff : ∀ m, N₁ + (d + 1) * p ≤ m → PowerSeries.coeff m f = 0 := by
    intro m hm
    have hQc : (Q : PowerSeries ℚ) = ∑ k ∈ Finset.range (d + 2),
        PowerSeries.C (q k) * PowerSeries.X ^ ((d + 1 - k) * p) := by
      simp only [Q, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_mul]
      rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp [Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_C, Polynomial.coe_mul]
    rw [hf, hQc, Finset.mul_sum, map_sum]
    rw [← hq (m - (d + 1) * p) (by omega)]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_left_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow']
    have hle : (d + 1 - k) * p ≤ m := by
      have : (d + 1 - k) * p ≤ (d + 1) * p := Nat.mul_le_mul_right _ (by omega)
      omega
    rw [if_pos hle, PowerSeries.coeff_mk]
    congr 3
    have : (d + 1 - k) * p + k * p = (d + 1) * p := by
      rw [← add_mul]; congr 1; omega
    omega
  refine ⟨PowerSeries.trunc (N₁ + (d + 1) * p) f, Q, hQ0, ?_⟩
  ext m
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  split_ifs with h
  · rfl
  · rw [hcoeff m (by omega)]
