-- Prove2me | solution 1 for FixedPointAA.Main.amplitude_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T19:41:54.224043+00:00
-- url     : https://prove2.me/submissions/ecfecb4f-bf57-4026-888f-4f3a00a85375

import Definitions.Def_FixedPointAA_Main_Setting
import Theorems.Thm_FixedPointAA_Main_amplitude_recurrence
import Theorems.Thm_FixedPointAA_Main_chebT_gammaInv

open FixedPointAA.Main
open scoped Matrix

private def tri (k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), i

private lemma tri_zero : tri 0 = 0 := by rfl

private lemma tri_succ (k : ℕ) : tri (k + 1) = tri k + (k + 1) := by
  dsimp [tri]
  rw [Finset.sum_range_succ]

private lemma tri_odd (l : ℕ) : tri (2 * l + 1) = (2 * l + 1) * (l + 1) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have h1 : 2 * (l + 1) + 1 = (2 * l + 1) + 1 + 1 := by omega
    rw [h1, tri_succ, tri_succ, ih]
    ring

private noncomputable def CCoeff (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) :
    ℕ → ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | k + 1, 0 => K₀ * CCoeff K₀ K₁ η k 0
  | k + 1, j + 1 => K₀ * CCoeff K₀ K₁ η k (j + 1) +
      (η ^ (k + 1)) • (K₁ * CCoeff K₀ K₁ η k j)

private lemma CCoeff_eq_zero_of_lt (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) :
    ∀ k j : ℕ, k < j → CCoeff K₀ K₁ η k j = 0
  | 0, j + 1, _ => rfl
  | k + 1, j + 1, h => by
    dsimp [CCoeff]
    rw [CCoeff_eq_zero_of_lt K₀ K₁ η k (j + 1) (by omega),
        CCoeff_eq_zero_of_lt K₀ K₁ η k j (by omega)]
    simp

private lemma CCoeff_zero (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (k : ℕ) :
    CCoeff K₀ K₁ η k 0 = K₀ ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp [CCoeff]
    rw [ih, pow_succ']

private lemma CCoeff_self (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (k : ℕ) :
    CCoeff K₀ K₁ η k k = (η ^ tri k) • (K₁ ^ k) := by
  induction k with
  | zero => simp [CCoeff, tri_zero]
  | succ k ih =>
    dsimp [CCoeff]
    rw [CCoeff_eq_zero_of_lt K₀ K₁ η k (k + 1) (by omega), Matrix.mul_zero, zero_add,
        ih, Matrix.mul_smul, smul_smul, ← pow_succ', ← pow_add, tri_succ, add_comm (k + 1)]

private noncomputable def kProd (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η t : ℂ) :
    ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | k + 1 => (K₀ + (t * η ^ (k + 1)) • K₁) * kProd K₀ K₁ η t k

private lemma kProd_expand (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η t : ℂ) (k : ℕ) :
    kProd K₀ K₁ η t k = ∑ j ∈ Finset.range (k + 1), (t ^ j) • CCoeff K₀ K₁ η k j := by
  induction k with
  | zero => simp [kProd, CCoeff]
  | succ k ih =>
    have h1 : ∑ j ∈ Finset.range (k + 2), (t ^ j) • CCoeff K₀ K₁ η (k + 1) j =
        (∑ j ∈ Finset.range (k + 1), (t ^ (j + 1)) • (K₀ * CCoeff K₀ K₁ η k (j + 1)) +
          (t ^ 0) • (K₀ * CCoeff K₀ K₁ η k 0)) +
        ∑ j ∈ Finset.range (k + 1),
          (t ^ (j + 1)) • ((η ^ (k + 1)) • (K₁ * CCoeff K₀ K₁ η k j)) := by
      rw [Finset.sum_range_succ']
      dsimp [CCoeff]
      simp only [smul_add, Finset.sum_add_distrib]
      abel
    have h2 : (∑ j ∈ Finset.range (k + 1), (t ^ (j + 1)) • (K₀ * CCoeff K₀ K₁ η k (j + 1)) +
          (t ^ 0) • (K₀ * CCoeff K₀ K₁ η k 0)) =
        ∑ j ∈ Finset.range (k + 1), (t ^ j) • (K₀ * CCoeff K₀ K₁ η k j) := by
      rw [← Finset.sum_range_succ' (fun j => (t ^ j) • (K₀ * CCoeff K₀ K₁ η k j)) (k + 1),
          Finset.sum_range_succ, CCoeff_eq_zero_of_lt K₀ K₁ η k (k + 1) (by omega),
          Matrix.mul_zero, smul_zero, add_zero]
    rw [h1, h2, kProd, ih, Matrix.add_mul, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.mul_smul]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_smul, pow_succ']
      ring_nf

private lemma kProd_shift (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η t : ℂ) (k : ℕ) :
    kProd K₀ K₁ η (η * t) k * (K₀ + (t * η) • K₁) =
      (K₀ + (t * η ^ (k + 1)) • K₁) * kProd K₀ K₁ η t k := by
  induction k with
  | zero => simp [kProd]
  | succ k ih =>
    calc kProd K₀ K₁ η (η * t) (k + 1) * (K₀ + (t * η) • K₁)
      _ = (K₀ + (η * t * η ^ (k + 1)) • K₁) *
            (kProd K₀ K₁ η (η * t) k * (K₀ + (t * η) • K₁)) := by
          simp only [kProd, Matrix.mul_assoc]
      _ = (K₀ + (t * η ^ (k + 2)) • K₁) *
            ((K₀ + (t * η ^ (k + 1)) • K₁) * kProd K₀ K₁ η t k) := by
          rw [ih]
          have : η * t * η ^ (k + 1) = t * η ^ (k + 2) := by rw [pow_succ']; ring
          rw [this]
      _ = (K₀ + (t * η ^ (k + 2)) • K₁) * kProd K₀ K₁ η t (k + 1) := by
          simp only [kProd]

private lemma trace_kProd_shift (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η t : ℂ) (L : ℕ)
    (hL : 1 ≤ L) (hηL : η ^ L = 1) :
    Matrix.trace (kProd K₀ K₁ η (η * t) L) = Matrix.trace (kProd K₀ K₁ η t L) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
  have h1 : kProd K₀ K₁ η t (m + 1) =
      kProd K₀ K₁ η (η * t) m * (K₀ + (t * η) • K₁) := by
    rw [kProd, ← kProd_shift]
  have h2 : kProd K₀ K₁ η (η * t) (m + 1) =
      (K₀ + (t * η) • K₁) * kProd K₀ K₁ η (η * t) m := by
    rw [kProd]
    have : η * t * η ^ (m + 1) = t * η := by
      calc η * t * η ^ (m + 1) = t * η * η ^ (m + 1) := by ring
        _ = t * η := by rw [hηL, mul_one]
    rw [this]
  rw [h1, h2, Matrix.trace_mul_comm]

private lemma trace_kProd_pow (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (L : ℕ)
    (hL : 1 ≤ L) (hηL : η ^ L = 1) (m : ℕ) :
    Matrix.trace (kProd K₀ K₁ η (η ^ m) L) = Matrix.trace (kProd K₀ K₁ η 1 L) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', trace_kProd_shift K₀ K₁ η (η ^ m) L hL hηL, ih]

private lemma geom_sum_eq_zero (z : ℂ) (L : ℕ) (hzL : z ^ L = 1) (hz1 : z ≠ 1) :
    ∑ m ∈ Finset.range L, z ^ m = 0 := by
  have hmul : (z - 1) * ∑ m ∈ Finset.range L, z ^ m = 0 := by
    rw [mul_geom_sum, hzL, sub_self]
  rcases mul_eq_zero.mp hmul with h | h
  · exact absurd (sub_eq_zero.mp h) hz1
  · exact h

private lemma trace_kProd_one (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (l : ℕ)
    (hηL : η ^ (2 * l + 1) = 1)
    (hη_ne : ∀ j : ℕ, 1 ≤ j → j < 2 * l + 1 → η ^ j ≠ 1) :
    Matrix.trace (kProd K₀ K₁ η 1 (2 * l + 1)) =
      Matrix.trace (K₀ ^ (2 * l + 1)) + Matrix.trace (K₁ ^ (2 * l + 1)) := by
  set L := 2 * l + 1
  have hL : 1 ≤ L := by omega
  have hL_ne : (L : ℂ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
  have hsum_lhs : ∑ m ∈ Finset.range L, Matrix.trace (kProd K₀ K₁ η (η ^ m) L) =
      (L : ℂ) * Matrix.trace (kProd K₀ K₁ η 1 L) := by
    trans ∑ _m ∈ Finset.range L, Matrix.trace (kProd K₀ K₁ η 1 L)
    · refine Finset.sum_congr rfl (fun m _ => trace_kProd_pow K₀ K₁ η L hL hηL m)
    · simp [Finset.sum_const]
  have htrace_sum : ∀ (s : Finset ℕ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ),
      Matrix.trace (∑ j ∈ s, f j) = ∑ j ∈ s, Matrix.trace (f j) := by
    intro s f
    simp only [Matrix.trace, Matrix.diag, Matrix.sum_apply]
    exact Finset.sum_comm
  have hsum_rhs : ∑ m ∈ Finset.range L, Matrix.trace (kProd K₀ K₁ η (η ^ m) L) =
      (L : ℂ) * (Matrix.trace (K₀ ^ L) + Matrix.trace (K₁ ^ L)) := by
    calc ∑ m ∈ Finset.range L, Matrix.trace (kProd K₀ K₁ η (η ^ m) L)
      _ = ∑ m ∈ Finset.range L,
            ∑ j ∈ Finset.range (L + 1), ((η ^ j) ^ m) * Matrix.trace (CCoeff K₀ K₁ η L j) := by
          refine Finset.sum_congr rfl (fun m _ => ?_)
          rw [kProd_expand, htrace_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Matrix.trace_smul, smul_eq_mul, ← pow_mul, mul_comm m j, pow_mul]
      _ = ∑ j ∈ Finset.range (L + 1),
            (∑ m ∈ Finset.range L, (η ^ j) ^ m) * Matrix.trace (CCoeff K₀ K₁ η L j) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← Finset.sum_mul]
      _ = (∑ j ∈ Finset.range (2 * l),
            (∑ m ∈ Finset.range L, (η ^ (j + 1)) ^ m) *
              Matrix.trace (CCoeff K₀ K₁ η L (j + 1)) +
            (∑ m ∈ Finset.range L, (η ^ 0) ^ m) * Matrix.trace (CCoeff K₀ K₁ η L 0)) +
          (∑ m ∈ Finset.range L, (η ^ L) ^ m) * Matrix.trace (CCoeff K₀ K₁ η L L) := by
          rw [Finset.sum_range_succ, Finset.sum_range_succ']
      _ = (L : ℂ) * (Matrix.trace (K₀ ^ L) + Matrix.trace (K₁ ^ L)) := by
          have hmid : ∑ j ∈ Finset.range (2 * l),
              (∑ m ∈ Finset.range L, (η ^ (j + 1)) ^ m) *
                Matrix.trace (CCoeff K₀ K₁ η L (j + 1)) = 0 := by
            refine Finset.sum_eq_zero (fun j hj => ?_)
            rw [Finset.mem_range] at hj
            have hzL : (η ^ (j + 1)) ^ L = 1 := by
              rw [← pow_mul, mul_comm, pow_mul, hηL, one_pow]
            have hz1 : η ^ (j + 1) ≠ 1 := hη_ne (j + 1) (by omega) (by omega)
            rw [geom_sum_eq_zero (η ^ (j + 1)) L hzL hz1, zero_mul]
          have htri : η ^ tri L = 1 := by
            dsimp [L]
            rw [tri_odd, pow_mul, hηL, one_pow]
          rw [hmid, zero_add, pow_zero, hηL, CCoeff_zero, CCoeff_self, htri, one_smul]
          simp [Finset.sum_const, mul_add]
  exact mul_left_cancel₀ hL_ne (hsum_lhs.symm.trans hsum_rhs)

private lemma chebT_zero (u : ℝ) : chebT 0 u = 1 := by
  simp [chebT]

private lemma chebT_one (u : ℝ) : chebT 1 u = u := by
  simp [chebT]

private lemma chebT_add_two (k : ℕ) (u : ℝ) :
    chebT (k + 2) u = 2 * u * chebT (k + 1) u - chebT k u := by
  dsimp [chebT]
  rw [Polynomial.Chebyshev.T_add_two]
  simp

private lemma trace_K_pow_pair (γ u : ℝ) (p q : ℂ) (hpq : p * q = (γ : ℂ) ^ 2) (k : ℕ) :
    Matrix.trace ((!![2 * ((γ : ℂ) * (u : ℂ)), -p; q, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ k) =
      2 * (γ : ℂ) ^ k * (chebT k u : ℂ) ∧
    Matrix.trace ((!![2 * ((γ : ℂ) * (u : ℂ)), -p; q, 0] : Matrix (Fin 2) (Fin 2) ℂ) ^ (k + 1)) =
      2 * (γ : ℂ) ^ (k + 1) * (chebT (k + 1) u : ℂ) := by
  set M : Matrix (Fin 2) (Fin 2) ℂ := !![2 * ((γ : ℂ) * (u : ℂ)), -p; q, 0]
  have hM2 : M ^ 2 = (2 * (γ : ℂ) * (u : ℂ)) • M - ((γ : ℂ) ^ 2) • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M, sq, Matrix.mul_apply, Fin.sum_univ_two, ← hpq] <;>
      try ring <;> tauto
  induction k with
  | zero =>
    constructor
    · simp [M, Matrix.trace, chebT_zero]
    · simp only [M, zero_add, pow_one, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, chebT_one]
      ring
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hpow : M ^ (k + 2) =
        (2 * (γ : ℂ) * (u : ℂ)) • (M ^ (k + 1)) - ((γ : ℂ) ^ 2) • (M ^ k) := by
      calc M ^ (k + 2) = M ^ k * M ^ 2 := by rw [pow_add]
        _ = M ^ k * ((2 * (γ : ℂ) * (u : ℂ)) • M - ((γ : ℂ) ^ 2) • 1) := by rw [hM2]
        _ = (2 * (γ : ℂ) * (u : ℂ)) • (M ^ (k + 1)) - ((γ : ℂ) ^ 2) • (M ^ k) := by
          rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← pow_succ]
    have htr : Matrix.trace (M ^ (k + 2)) =
        (2 * (γ : ℂ) * (u : ℂ)) * Matrix.trace (M ^ (k + 1)) -
          ((γ : ℂ) ^ 2) * Matrix.trace (M ^ k) := by
      rw [hpow, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    rw [htr, ih.1, ih.2, chebT_add_two]
    push_cast
    ring

private lemma K_transpose_symm (x p q y z : ℂ) (hyz : y * z = 1) :
    let K₀ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -p; q, 0]
    let K₁ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -q; p, 0]
    pauliZ * (K₀ + y • K₁)ᵀ * pauliZ = y • (K₀ + z • K₁) := by
  intro K₀ K₁
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [K₀, K₁, pauliZ, Fin.zero_eta, Fin.mk_one, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.transpose_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  · linear_combination -(2 * x) * hyz
  · linear_combination q * hyz
  · linear_combination -p * hyz
  · ring

private noncomputable def MOut (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (l : ℕ) :
    ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | j + 1 => (K₀ + (η ^ (l + 1 + j)) • K₁) * MOut K₀ K₁ η l j * (K₀ + (η ^ (l - j)) • K₁)

private lemma kProd_eq_MOut_mul (K₀ K₁ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℂ) (l j : ℕ)
    (hj : j ≤ l) :
    kProd K₀ K₁ η 1 (l + j) = MOut K₀ K₁ η l j * kProd K₀ K₁ η 1 (l - j) := by
  induction j with
  | zero => simp [MOut]
  | succ j ih =>
    have h1 : l + (j + 1) = (l + j) + 1 := by omega
    have h2 : l - j = (l - (j + 1)) + 1 := by omega
    have h3 : (l + j) + 1 = l + 1 + j := by omega
    rw [h1, kProd, one_mul, h3, ih (by omega), h2, kProd, one_mul, ← h2, MOut]
    simp only [Matrix.mul_assoc]

private lemma MOut_symm (x p q η : ℂ) (l : ℕ) (hηL : η ^ (2 * l + 1) = 1) (j : ℕ)
    (hj : j ≤ l) :
    let K₀ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -p; q, 0]
    let K₁ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -q; p, 0]
    pauliZ * (MOut K₀ K₁ η l j)ᵀ * pauliZ = MOut K₀ K₁ η l j := by
  intro K₀ K₁
  induction j with
  | zero =>
    ext a b
    fin_cases a <;> fin_cases b <;> simp [MOut, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  | succ j ih =>
    have hZ2 : pauliZ * pauliZ = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
    have hyz1 : η ^ (l - j) * η ^ (l + 1 + j) = 1 := by
      rw [← pow_add]
      have : (l - j) + (l + 1 + j) = 2 * l + 1 := by omega
      rw [this, hηL]
    have hyz2 : η ^ (l + 1 + j) * η ^ (l - j) = 1 := by
      rw [mul_comm, hyz1]
    have hK1 := K_transpose_symm x p q (η ^ (l - j)) (η ^ (l + 1 + j)) hyz1
    have hK2 := K_transpose_symm x p q (η ^ (l + 1 + j)) (η ^ (l - j)) hyz2
    dsimp only at hK1 hK2
    calc pauliZ * (MOut K₀ K₁ η l (j + 1))ᵀ * pauliZ
      _ = pauliZ * ((K₀ + (η ^ (l - j)) • K₁)ᵀ * (MOut K₀ K₁ η l j)ᵀ *
            (K₀ + (η ^ (l + 1 + j)) • K₁)ᵀ) * pauliZ := by
          simp only [MOut, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (pauliZ * (K₀ + (η ^ (l - j)) • K₁)ᵀ * pauliZ) *
            (pauliZ * (MOut K₀ K₁ η l j)ᵀ * pauliZ) *
            (pauliZ * (K₀ + (η ^ (l + 1 + j)) • K₁)ᵀ * pauliZ) := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc pauliZ pauliZ, hZ2, Matrix.one_mul,
              ← Matrix.mul_assoc pauliZ pauliZ, hZ2, Matrix.one_mul]
      _ = ((η ^ (l - j)) • (K₀ + (η ^ (l + 1 + j)) • K₁)) *
            MOut K₀ K₁ η l j *
            ((η ^ (l + 1 + j)) • (K₀ + (η ^ (l - j)) • K₁)) := by
          rw [hK1, ih (by omega), hK2]
      _ = MOut K₀ K₁ η l (j + 1) := by
          simp only [MOut, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hyz2, one_smul]

private lemma kProd_offdiag_symm (x p q η : ℂ) (l : ℕ) (hηL : η ^ (2 * l + 1) = 1) :
    let K₀ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -p; q, 0]
    let K₁ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -q; p, 0]
    kProd K₀ K₁ η 1 (2 * l) 1 0 = - kProd K₀ K₁ η 1 (2 * l) 0 1 := by
  intro K₀ K₁
  have hM : kProd K₀ K₁ η 1 (2 * l) = MOut K₀ K₁ η l l := by
    have h := kProd_eq_MOut_mul K₀ K₁ η l l (le_refl l)
    have hll : l + l = 2 * l := by omega
    rw [hll, Nat.sub_self, kProd, Matrix.mul_one] at h
    exact h
  have hsym := MOut_symm x p q η l hηL l (le_refl l)
  dsimp only at hsym
  rw [← hM] at hsym
  have hentry := congr_fun (congr_fun hsym 1) 0
  simp only [pauliZ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hentry
  linear_combination -hentry

private lemma kProd_mulVec_rec (x p q η : ℂ) (l : ℕ) (a : ℕ → ℂ)
    (ha0 : a 0 = 1) (ha1 : a 1 = x)
    (harec : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * l →
      (p * η ^ k + q) * a (k + 1) = 2 * x * (η ^ k + 1) * a k - (q * η ^ k + p) * a (k - 1))
    (k : ℕ) (hk : k ≤ 2 * l) :
    let K₀ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -p; q, 0]
    let K₁ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -q; p, 0]
    kProd K₀ K₁ η 1 k *ᵥ ![x, 1] =
      (∏ m ∈ Finset.Ico 1 (k + 1), (p * η ^ m + q)) • ![a (k + 1), a k] := by
  intro K₀ K₁
  induction k with
  | zero =>
    simp [kProd, ha0, ha1]
  | succ k ih =>
    have hstep := harec (k + 1) (by omega) hk
    have hsub : k + 1 - 1 = k := by omega
    rw [hsub] at hstep
    have hvec_step : (K₀ + (η ^ (k + 1)) • K₁) *ᵥ ![a (k + 1), a k] =
        (p * η ^ (k + 1) + q) • ![a (k + 2), a (k + 1)] := by
      ext i
      fin_cases i <;>
        simp only [K₀, K₁, Fin.zero_eta, Fin.mk_one, Matrix.add_apply, Matrix.smul_apply,
          smul_eq_mul, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply]
      · linear_combination -hstep
      · ring
    rw [kProd, one_mul, ← Matrix.mulVec_mulVec, ih (by omega), Matrix.mulVec_smul,
        hvec_step, smul_smul, Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1),
        mul_comm _ (p * η ^ (k + 1) + q)]

private lemma general_chebyshev_eval (γ u : ℝ) (s η : ℂ) (l : ℕ)
    (hs : 1 - s ^ 2 = (γ : ℂ) ^ 2)
    (hηL : η ^ (2 * l + 1) = 1)
    (hη_ne : ∀ j : ℕ, 1 ≤ j → j < 2 * l + 1 → η ^ j ≠ 1)
    (a : ℕ → ℂ) (ha0 : a 0 = 1) (ha1 : a 1 = (γ : ℂ) * (u : ℂ))
    (harec : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * l →
      ((1 + s) * η ^ k + (1 - s)) * a (k + 1) =
        2 * ((γ : ℂ) * (u : ℂ)) * (η ^ k + 1) * a k -
          ((1 - s) * η ^ k + (1 + s)) * a (k - 1)) :
    4 * (∏ m ∈ Finset.Ico 1 (2 * l + 1), ((1 + s) * η ^ m + (1 - s))) * a (2 * l + 1) =
      4 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) u : ℂ) := by
  set x : ℂ := (γ : ℂ) * (u : ℂ)
  set p : ℂ := 1 + s
  set q : ℂ := 1 - s
  set K₀ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -p; q, 0]
  set K₁ : Matrix (Fin 2) (Fin 2) ℂ := !![2 * x, -q; p, 0]
  set P : Matrix (Fin 2) (Fin 2) ℂ := kProd K₀ K₁ η 1 (2 * l)
  have hpq : p * q = (γ : ℂ) ^ 2 := by
    calc p * q = 1 - s ^ 2 := by dsimp [p, q]; ring
      _ = (γ : ℂ) ^ 2 := hs
  have hqp : q * p = (γ : ℂ) ^ 2 := by rw [mul_comm, hpq]
  have hvec := congr_fun (kProd_mulVec_rec x p q η l a ha0 ha1 harec (2 * l) (le_refl _)) 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero] at hvec
  have hvec0 : P 0 0 * x + P 0 1 =
      (∏ m ∈ Finset.Ico 1 (2 * l + 1), (p * η ^ m + q)) * a (2 * l + 1) := by
    simpa [P, K₀, K₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hvec
  have hsym : P 1 0 = - P 0 1 := kProd_offdiag_symm x p q η l hηL
  have htr_lhs : Matrix.trace (kProd K₀ K₁ η 1 (2 * l + 1)) =
      4 * (∏ m ∈ Finset.Ico 1 (2 * l + 1), (p * η ^ m + q)) * a (2 * l + 1) := by
    have hstep : kProd K₀ K₁ η 1 (2 * l + 1) = (K₀ + K₁) * P := by
      rw [kProd, one_mul, hηL, one_smul]
    rw [hstep]
    have htr_expand : Matrix.trace ((K₀ + K₁) * P) =
        4 * x * P 0 0 - 2 * P 1 0 + 2 * P 0 1 := by
      simp only [K₀, K₁, p, q, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
        Matrix.mul_apply, Matrix.add_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring
    rw [htr_expand]
    linear_combination 4 * hvec0 - 2 * hsym
  have htr_rhs : Matrix.trace (kProd K₀ K₁ η 1 (2 * l + 1)) =
      4 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) u : ℂ) := by
    rw [trace_kProd_one K₀ K₁ η l hηL hη_ne]
    have hK0 : Matrix.trace (K₀ ^ (2 * l + 1)) =
        2 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) u : ℂ) :=
      (trace_K_pow_pair γ u p q hpq (2 * l)).2
    have hK1 : Matrix.trace (K₁ ^ (2 * l + 1)) =
        2 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) u : ℂ) :=
      (trace_K_pow_pair γ u q p hqp (2 * l)).2
    rw [hK0, hK1]
    ring
  exact htr_lhs.symm.trans htr_rhs

private lemma exp_arctan_rel (y : ℝ) :
    let w := Complex.exp (-(2 * (Real.arctan y : ℂ) * Complex.I))
    (1 + (y : ℂ) * Complex.I) * w = 1 - (y : ℂ) * Complex.I ∧
      (1 + (y : ℂ) * Complex.I) * (1 + w) = 2 := by
  intro w
  have hw : (1 + (y : ℂ) * Complex.I) * w = 1 - (y : ℂ) * Complex.I := by
    set θ := Real.arctan y
    have hcos_pos : 0 < Real.cos θ := Real.cos_arctan_pos y
    have hcos_ne : (Real.cos θ : ℂ) ≠ 0 := by exact_mod_cast hcos_pos.ne'
    have hsin : Real.sin θ = y * Real.cos θ := by
      have htan := Real.tan_arctan y
      rw [Real.tan_eq_sin_div_cos, div_eq_iff hcos_pos.ne'] at htan
      exact htan
    have he_pos : (Real.cos θ : ℂ) * (1 + (y : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hsin]
      push_cast
      ring
    have he_neg : (Real.cos θ : ℂ) * (1 - (y : ℂ) * Complex.I) =
        Complex.exp (-((θ : ℂ) * Complex.I)) := by
      have : -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
          Real.cos_neg, Real.sin_neg, hsin]
      push_cast
      ring
    apply mul_left_cancel₀ hcos_ne
    calc (Real.cos θ : ℂ) * ((1 + (y : ℂ) * Complex.I) * w)
      _ = ((Real.cos θ : ℂ) * (1 + (y : ℂ) * Complex.I)) * w := by ring
      _ = Complex.exp ((θ : ℂ) * Complex.I) *
            Complex.exp (-(2 * (θ : ℂ) * Complex.I)) := by rw [he_pos]
      _ = Complex.exp (-((θ : ℂ) * Complex.I)) := by
          rw [← Complex.exp_add]
          congr 1
          ring
      _ = (Real.cos θ : ℂ) * (1 - (y : ℂ) * Complex.I) := he_neg.symm
  refine ⟨hw, ?_⟩
  linear_combination hw

private lemma cos_step_ne_zero (l k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * l) :
    Real.cos ((k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)) ≠ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hL : 0 < (2 * (l : ℝ) + 1) := by positivity
  by_cases h : 2 * k ≤ 2 * l
  · have hk_lt : (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) < Real.pi / 2 := by
      rw [div_lt_div_iff₀ hL two_pos]
      have : (k : ℝ) * 2 < 2 * (l : ℝ) + 1 := by exact_mod_cast (by omega : k * 2 < 2 * l + 1)
      nlinarith
    have hk_pos : -(Real.pi / 2) < (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) := by
      have : 0 < (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) := by positivity
      linarith
    exact (Real.cos_pos_of_mem_Ioo ⟨hk_pos, hk_lt⟩).ne'
  · have h2 : 2 * l + 2 ≤ 2 * k := by omega
    have hsub_lt : Real.pi - (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) < Real.pi / 2 := by
      have hgt : Real.pi / 2 < (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) := by
        rw [div_lt_div_iff₀ two_pos hL]
        have : 2 * (l : ℝ) + 1 < (k : ℝ) * 2 := by exact_mod_cast (by omega : 2 * l + 1 < k * 2)
        nlinarith
      linarith
    have hsub_pos : -(Real.pi / 2) < Real.pi - (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) := by
      have hlt : (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1) < Real.pi := by
        rw [div_lt_iff₀ hL]
        have : (k : ℝ) < 2 * (l : ℝ) + 1 := by exact_mod_cast (by omega : k < 2 * l + 1)
        nlinarith
      linarith
    have hcos_sub : 0 < Real.cos (Real.pi - (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)) :=
      Real.cos_pos_of_mem_Ioo ⟨hsub_pos, hsub_lt⟩
    rw [Real.cos_pi_sub] at hcos_sub
    linarith

private lemma eta_tan_rel (l k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2 * l) :
    let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * (l : ℂ) + 1))
    let τ : ℂ := (Real.tan ((k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)) : ℂ)
    (η ^ k + 1) * (τ * Complex.I) = η ^ k - 1 := by
  intro η τ
  set θ : ℝ := (k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)
  have hcos_r : Real.cos θ ≠ 0 := cos_step_ne_zero l k hk1 hk2
  have hsin_r : Real.sin θ = Real.tan θ * Real.cos θ := by
    rw [Real.tan_eq_sin_div_cos θ, div_mul_cancel₀ _ hcos_r]
  have hsin : (Real.sin θ : ℂ) = τ * (Real.cos θ : ℂ) := by
    dsimp [τ, θ] at hsin_r ⊢
    exact_mod_cast hsin_r
  have hηk : η ^ k = Complex.exp ((θ : ℂ) * Complex.I) ^ 2 := by
    dsimp [η, θ]
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hexp : Complex.exp ((θ : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have htrig : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [hsin] at htrig
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  rw [hηk, hexp, hsin]
  linear_combination -(1 + τ * Complex.I) * htrig +
    ((Real.cos θ : ℂ) ^ 2 * τ ^ 2 * (1 + τ * Complex.I)) * hI

private lemma dz_exp_eq (l : ℕ) (δ : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    let t := Real.tan ((k : ℝ) * Real.pi / (2 * (l : ℝ) + 1)) *
      Real.sqrt (1 - gam (2 * l + 1) δ ^ 2)
    Complex.exp (-(((zeta l δ (k + 1) - zeta l δ k : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (-(2 * (Real.arctan t : ℂ) * Complex.I)) := by
  intro t
  have hstep : zeta l δ (k + 1) - zeta l δ k = dz l δ k := by
    dsimp [zeta]
    rw [Finset.sum_Ico_succ_top hk]
    ring
  rw [hstep]
  have hdz : dz l δ k = ((-1 : ℝ) ^ k - 1) * Real.pi + 2 * Real.arctan t := by
    dsimp [dz, arccot, t]
    ring
  rw [hdz]
  have hexp_split :
      -((((((-1 : ℝ) ^ k - 1) * Real.pi + 2 * Real.arctan t : ℝ) : ℂ) * Complex.I)) =
      -(((((-1 : ℝ) ^ k - 1) * Real.pi : ℝ) : ℂ) * Complex.I) +
        (-(2 * (Real.arctan t : ℂ) * Complex.I)) := by
    push_cast
    ring
  rw [hexp_split, Complex.exp_add]
  have hpi : Complex.exp (-(((((-1 : ℝ) ^ k - 1) * Real.pi : ℝ) : ℂ) * Complex.I)) = 1 := by
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have h1 : (-1 : ℝ) ^ (m + m) = 1 := by
        rw [← two_mul, pow_mul, neg_one_sq, one_pow]
      rw [h1]
      simp
    · have h1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
        rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul]
      rw [h1]
      have h2 : -((((-1 - 1 : ℝ) * Real.pi : ℝ) : ℂ) * Complex.I) =
          2 * Real.pi * Complex.I := by
        push_cast
        ring
      rw [h2, Complex.exp_two_pi_mul_I]
  rw [hpi, one_mul]

theorem solution (lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ℕ) :
    amp (blochAngle lam) (zeta l δ) (2 * l + 1) =
      ((chebT (2 * l + 1)
        (Real.cos (blochAngle lam / 2) * gammaInv (2 * l + 1) δ) /
        chebT (2 * l + 1) (gammaInv (2 * l + 1) δ) : ℝ) : ℂ) := by
  set L := 2 * l + 1
  set gInv := gammaInv L δ
  set γ := gam L δ
  set sR := Real.sqrt (1 - γ ^ 2)
  set s : ℂ := (sR : ℂ)
  set η : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * (l : ℂ) + 1))
  have hgInv_ge : 1 ≤ gInv := Real.one_le_cosh _
  have hgInv_pos : 0 < gInv := lt_of_lt_of_le zero_lt_one hgInv_ge
  have hγ_pos : 0 < γ := by dsimp [γ, gam]; positivity
  have hγ_le : γ ≤ 1 := by
    dsimp [γ, gam]
    exact div_le_one_of_le₀ hgInv_ge hgInv_pos.le
  have hγ_mul : γ * gInv = 1 := by
    dsimp [γ, gam]
    exact one_div_mul_cancel hgInv_pos.ne'
  have hs_sq : 1 - s ^ 2 = (γ : ℂ) ^ 2 := by
    have hnonneg : 0 ≤ 1 - γ ^ 2 := by nlinarith
    have hsq : sR ^ 2 = 1 - γ ^ 2 := Real.sq_sqrt hnonneg
    dsimp [s]
    exact_mod_cast (by linarith : 1 - sR ^ 2 = γ ^ 2)
  have hηL : η ^ (2 * l + 1) = 1 := by
    dsimp [η]
    rw [← Complex.exp_nat_mul]
    have hL_ne : (2 * (l : ℂ) + 1) ≠ 0 := by
      exact_mod_cast (by omega : 2 * l + 1 ≠ 0)
    have : ((2 * l + 1 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / (2 * (l : ℂ) + 1)) =
        2 * Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [this, Complex.exp_two_pi_mul_I]
  have hη_ne : ∀ j : ℕ, 1 ≤ j → j < 2 * l + 1 → η ^ j ≠ 1 := by
    intro j hj1 hj2 h_eq
    set θ : ℝ := (j : ℝ) * Real.pi / (2 * (l : ℝ) + 1)
    have hθ_pos : 0 < θ := by
      dsimp [θ]
      have : 0 < (2 * (l : ℝ) + 1) := by positivity
      positivity
    have hθ_lt : θ < Real.pi := by
      dsimp [θ]
      have hL_pos : 0 < (2 * (l : ℝ) + 1) := by positivity
      rw [div_lt_iff₀ hL_pos]
      have : (j : ℝ) < 2 * (l : ℝ) + 1 := by exact_mod_cast hj2
      nlinarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt
    have hcos_ne : Real.cos θ ≠ 0 := cos_step_ne_zero l j hj1 (by omega)
    have htan_ne : (Real.tan θ : ℂ) ≠ 0 := by
      have : Real.tan θ ≠ 0 := by
        rw [Real.tan_eq_sin_div_cos]
        exact div_ne_zero hsin_pos.ne' hcos_ne
      exact_mod_cast this
    have hetan := eta_tan_rel l j hj1 (by omega)
    dsimp only at hetan
    change (η ^ j + 1) * ((Real.tan θ : ℂ) * Complex.I) = η ^ j - 1 at hetan
    rw [h_eq] at hetan
    have hzero : (2 : ℂ) * (Real.tan θ : ℂ) * Complex.I = 0 := by
      linear_combination hetan
    have h2I : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
    apply htan_ne
    apply mul_left_cancel₀ h2I
    linear_combination hzero
  set φ := blochAngle lam
  set a := amp φ (zeta l δ)
  set u := Real.cos (φ / 2) * gInv
  have hrec_full := amplitude_recurrence φ (zeta l δ)
  have ha0 : a 0 = 1 := hrec_full.1
  have ha1 : a 1 = (γ : ℂ) * (u : ℂ) := by
    dsimp [a, u]
    rw [hrec_full.2.1, Complex.ofReal_mul]
    have hγg : (γ : ℂ) * (gInv : ℂ) = 1 := by exact_mod_cast hγ_mul
    linear_combination -(Real.cos (φ / 2) : ℂ) * hγg
  have harec : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * l →
      ((1 + s) * η ^ k + (1 - s)) * a (k + 1) =
        2 * ((γ : ℂ) * (u : ℂ)) * (η ^ k + 1) * a k -
          ((1 - s) * η ^ k + (1 + s)) * a (k - 1) := by
    intro k hk1 hk2
    have hstep := hrec_full.2.2 (k + 1) (by omega)
    have hsub1 : k + 1 - 1 = k := by omega
    have hsub2 : k + 1 - 2 = k - 1 := by omega
    rw [hsub1, hsub2] at hstep
    set τ : ℝ := Real.tan ((k : ℝ) * Real.pi / (2 * (l : ℝ) + 1))
    set tk : ℝ := τ * sR
    set wk : ℂ := Complex.exp (-(((zeta l δ (k + 1) - zeta l δ k : ℝ) : ℂ) * Complex.I))
    have hwk_eq : wk = Complex.exp (-(2 * (Real.arctan tk : ℂ) * Complex.I)) :=
      dz_exp_eq l δ k hk1
    have hrel := exp_arctan_rel tk
    dsimp only at hrel
    rw [← hwk_eq] at hrel
    have hetan := eta_tan_rel l k hk1 hk2
    dsimp only at hetan
    have htk_c : (tk : ℂ) = (τ : ℂ) * s := by dsimp [tk, s]; push_cast; rfl
    have hp_eq : (1 + s) * η ^ k + (1 - s) = (η ^ k + 1) * (1 + (tk : ℂ) * Complex.I) := by
      rw [htk_c]
      linear_combination -s * hetan
    have hq_eq : (1 - s) * η ^ k + (1 + s) = (η ^ k + 1) * (1 - (tk : ℂ) * Complex.I) := by
      rw [htk_c]
      linear_combination s * hetan
    have hx_eq : ((γ : ℂ) * (u : ℂ)) = (Real.cos (φ / 2) : ℂ) := by
      rw [← ha1]
      exact hrec_full.2.1
    rw [hp_eq, hq_eq, hx_eq]
    dsimp [a]
    calc (η ^ k + 1) * (1 + (tk : ℂ) * Complex.I) * amp φ (zeta l δ) (k + 1)
      _ = (η ^ k + 1) * ((1 + (tk : ℂ) * Complex.I) *
            ((Real.cos (φ / 2) : ℂ) * (1 + wk) * amp φ (zeta l δ) k -
              wk * amp φ (zeta l δ) (k - 1))) := by
          rw [← hstep]; ring
      _ = (η ^ k + 1) * ((Real.cos (φ / 2) : ℂ) *
            ((1 + (tk : ℂ) * Complex.I) * (1 + wk)) * amp φ (zeta l δ) k -
            ((1 + (tk : ℂ) * Complex.I) * wk) * amp φ (zeta l δ) (k - 1)) := by ring
      _ = 2 * (Real.cos (φ / 2) : ℂ) * (η ^ k + 1) * amp φ (zeta l δ) k -
            (η ^ k + 1) * (1 - (tk : ℂ) * Complex.I) * amp φ (zeta l δ) (k - 1) := by
          rw [hrel.1, hrel.2]; ring
  have heval_u := general_chebyshev_eval γ u s η l hs_sq hηL hη_ne a ha0 ha1 harec
  have ha1_one : (fun _ : ℕ => (1 : ℂ)) 1 = (γ : ℂ) * (gInv : ℂ) := by
    dsimp
    exact_mod_cast hγ_mul.symm
  have harec_one : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * l →
      ((1 + s) * η ^ k + (1 - s)) * (1 : ℂ) =
        2 * ((γ : ℂ) * (gInv : ℂ)) * (η ^ k + 1) * (1 : ℂ) -
          ((1 - s) * η ^ k + (1 + s)) * (1 : ℂ) := by
    intro k _ _
    rw [← ha1_one]
    ring
  have heval_one := general_chebyshev_eval γ gInv s η l hs_sq hηL hη_ne
    (fun _ => 1) rfl ha1_one harec_one
  rw [mul_one] at heval_one
  rw [heval_one] at heval_u
  have hcheb_gInv : chebT L gInv = 1 / δ :=
    chebT_gammaInv δ hδ0 hδ1 L (by omega)
  have hcheb_ne : (chebT L gInv : ℂ) ≠ 0 := by
    rw [hcheb_gInv]
    exact_mod_cast (one_div_ne_zero hδ0.ne')
  have h4γ_ne : 4 * (γ : ℂ) ^ L ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero L (by exact_mod_cast hγ_pos.ne'))
  have h4γ_cheb_ne : 4 * (γ : ℂ) ^ L * (chebT L gInv : ℂ) ≠ 0 :=
    mul_ne_zero h4γ_ne hcheb_ne
  apply mul_left_cancel₀ h4γ_cheb_ne
  change 4 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) gInv : ℂ) * a (2 * l + 1) =
    4 * (γ : ℂ) ^ (2 * l + 1) * (chebT (2 * l + 1) gInv : ℂ) *
      ((chebT (2 * l + 1) u / chebT (2 * l + 1) gInv : ℝ) : ℂ)
  rw [heval_u]
  push_cast
  have hcancel : (chebT (2 * l + 1) gInv : ℂ) *
      ((chebT (2 * l + 1) u : ℂ) / (chebT (2 * l + 1) gInv : ℂ)) =
      (chebT (2 * l + 1) u : ℂ) := mul_div_cancel₀ _ hcheb_ne
  linear_combination -4 * (γ : ℂ) ^ (2 * l + 1) * hcancel
