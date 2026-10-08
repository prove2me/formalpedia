-- Prove2me | solution 1 for DiophantinePreprocessing.FrankTardos.preprocessing_output_criteria
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:03:04.110697+00:00
-- url     : https://prove2.me/submissions/4c8c8bfa-0d5d-4f8c-9bab-aa8965cdb873

import Mathlib
import Definitions.Def_DiophantinePreprocessing_FrankTardos_CondIII

set_option autoImplicit false

open DiophantinePreprocessing.FrankTardos in
lemma ftd5_abs_le_supNorm {n : ℕ} (v : Fin n → ℤ) (j : Fin n) :
    |v j| ≤ (supNorm v : ℤ) := by
  have h := Finset.le_sup (f := fun j => (v j).natAbs) (Finset.mem_univ j)
  rw [← Int.natCast_natAbs]
  exact_mod_cast h

open DiophantinePreprocessing.FrankTardos in
lemma ftd5_dot_le {n : ℕ} (v b : Fin n → ℤ) :
    |∑ j, v j * b j| ≤ (supNorm v : ℤ) * ∑ j, |b j| := by
  calc |∑ j, v j * b j| ≤ ∑ j, |v j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |v j| * |b j| := by simp [abs_mul]
    _ ≤ ∑ j, (supNorm v : ℤ) * |b j| := by
        gcongr with j
        exact ftd5_abs_le_supNorm v j
    _ = (supNorm v : ℤ) * ∑ j, |b j| := by rw [Finset.mul_sum]

lemma ftd5_tail (a D : ℕ → ℝ) (c : ℕ → ℤ) (K : ℕ)
    (hpos : ∀ m, 1 ≤ m → m < K → 0 < a m)
    (hc : ∀ i, 1 ≤ i → i < K → |(c i : ℝ)| ≤ D i)
    (hstep : ∀ m, 1 ≤ m → m + 1 < K → a (m + 1) * (D (m + 1) + 1) ≤ a m) :
    ∀ m, 1 ≤ m → m < K → |∑ i ∈ Finset.Ico (m + 1) K, a i * c i| < a m := by
  suffices H : ∀ d m, K = m + 1 + d → 1 ≤ m → |∑ i ∈ Finset.Ico (m + 1) K, a i * c i| < a m by
    intro m hm hmK
    exact H (K - m - 1) m (by omega) hm
  intro d
  induction d with
  | zero =>
    intro m hK hm
    subst hK
    simpa using hpos m hm (by omega)
  | succ d ih =>
    intro m hK hm
    have h1 := ih (m + 1) (by omega) (by omega)
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : m + 1 < K)]
    have hcm := hc (m + 1) (by omega) (by omega)
    have hst := hstep m hm (by omega)
    have hp := hpos (m + 1) (by omega) (by omega)
    calc |a (m + 1) * c (m + 1) + ∑ i ∈ Finset.Ico (m + 1 + 1) K, a i * c i|
        ≤ |a (m + 1) * c (m + 1)| + |∑ i ∈ Finset.Ico (m + 1 + 1) K, a i * c i| :=
          abs_add_le _ _
      _ < a (m + 1) * D (m + 1) + a (m + 1) := by
          rw [abs_mul, abs_of_pos hp]
          exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hcm hp.le) h1
      _ = a (m + 1) * (D (m + 1) + 1) := by ring
      _ ≤ a m := hst

lemma ftd5_sign_aux (w T : ℝ) (z : ℤ) (hz : z ≠ 0) (hw : 0 < w) (hT : |T| < w) :
    SignType.sign (w * z + T) = SignType.sign (z : ℝ) := by
  have hT' := abs_lt.mp hT
  rcases lt_or_gt_of_ne hz with h | h
  · have h1 : (z : ℝ) ≤ -1 := by exact_mod_cast (show z ≤ -1 by omega)
    have h2 : w * z + T < 0 := by nlinarith
    rw [sign_neg h2, sign_neg (by linarith)]
  · have h1 : (1 : ℝ) ≤ z := by exact_mod_cast (show 1 ≤ z by omega)
    have h2 : 0 < w * z + T := by nlinarith
    rw [sign_pos h2, sign_pos (by linarith)]

lemma ftd5_sign (a a' : ℕ → ℝ) (c : ℕ → ℤ) (K : ℕ)
    (hpos : ∀ m, 1 ≤ m → m < K → 0 < a m)
    (hpos' : ∀ m, 1 ≤ m → m < K → 0 < a' m)
    (ht : ∀ m, 1 ≤ m → m < K → |∑ i ∈ Finset.Ico (m + 1) K, a i * c i| < a m)
    (ht' : ∀ m, 1 ≤ m → m < K → |∑ i ∈ Finset.Ico (m + 1) K, a' i * c i| < a' m) :
    ∀ j, 1 ≤ j → SignType.sign (∑ i ∈ Finset.Ico j K, a i * c i) =
      SignType.sign (∑ i ∈ Finset.Ico j K, a' i * c i) := by
  suffices H : ∀ d j, K = j + d → 1 ≤ j → SignType.sign (∑ i ∈ Finset.Ico j K, a i * c i) =
      SignType.sign (∑ i ∈ Finset.Ico j K, a' i * c i) by
    intro j hj
    by_cases hjK : j ≤ K
    · exact H (K - j) j (by omega) hj
    · simp [Finset.Ico_eq_empty_of_le (by omega : K ≤ j)]
  intro d
  induction d with
  | zero =>
    intro j hK hj
    subst hK
    simp
  | succ d ih =>
    intro j hK hj
    have hjK : j < K := by omega
    rw [Finset.sum_eq_sum_Ico_succ_bot hjK, Finset.sum_eq_sum_Ico_succ_bot hjK]
    by_cases hc : c j = 0
    · simp only [hc, Int.cast_zero, mul_zero, zero_add]
      exact ih (j + 1) (by omega) (by omega)
    · rw [ftd5_sign_aux _ _ _ hc (hpos j hj hjK) (ht j hj hjK),
        ftd5_sign_aux _ _ _ hc (hpos' j hj hjK) (ht' j hj hjK)]

open DiophantinePreprocessing.FrankTardos in
lemma ftd5_supNorm_pos {n : ℕ} (v : Fin n → ℤ) (hv : v ≠ 0) : 1 ≤ supNorm v := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    exact hv (funext fun j => by
      by_contra hj
      exact h ⟨j, hj⟩)
  have h1 := ftd5_abs_le_supNorm v j
  have h2 : 0 < |v j| := abs_pos.mpr hj
  have : (0 : ℤ) < supNorm v := lt_of_lt_of_le h2 h1
  exact_mod_cast this

open DiophantinePreprocessing.FrankTardos in
theorem solution (n N k : ℕ) (hN : 1 ≤ N) (w : Fin n → ℚ)
    (v : ℕ → Fin n → ℤ) (lam : ℕ → ℝ) (hk : k ≤ n)
    (hlam : ∀ i ∈ Finset.Icc 1 k, 0 < lam i)
    (hw : ∀ j, (w j : ℝ) = ∑ i ∈ Finset.Icc 1 k, lam i * (v i j : ℝ))
    (hii' : ∀ i ∈ Finset.Icc 1 k, supNorm (v i) ≤ 2 ^ (n ^ 2 + n) * N ^ n)
    (hIII : CondIII N k lam v) :
    let M : ℤ := 2 ^ (n ^ 2 + n) * (N : ℤ) ^ (n + 1)
    let wt : Fin n → ℤ := fun j => ∑ i ∈ Finset.Icc 1 k, M ^ (k - i) * v i j
    (∀ j, |wt j| ≤ 2 ^ (4 * n ^ 3) * (N : ℤ) ^ (n * (n + 2))) ∧
    ∀ b : Fin n → ℤ, ∑ j, |b j| ≤ (N : ℤ) - 1 →
      SignType.sign (∑ j, (w j : ℝ) * (b j : ℝ)) =
        SignType.sign ((∑ j, wt j * b j : ℤ) : ℝ) := by
  dsimp only
  set B : ℤ := 2 ^ (n ^ 2 + n) * (N : ℤ) ^ n with hBdef
  set M : ℤ := 2 ^ (n ^ 2 + n) * (N : ℤ) ^ (n + 1) with hMdef
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hB1 : (1 : ℤ) ≤ B := by
    rw [hBdef]
    have h1 : (1 : ℤ) ≤ 2 ^ (n ^ 2 + n) := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℤ) ≤ (N : ℤ) ^ n := one_le_pow₀ hN1
    nlinarith
  have hMB : M = B * N := by rw [hMdef, hBdef]; ring
  have hM1 : (1 : ℤ) ≤ M := by rw [hMB]; nlinarith
  have hsupB : ∀ i ∈ Finset.Icc 1 k, (supNorm (v i) : ℤ) ≤ B := by
    intro i hi
    rw [hBdef]
    exact_mod_cast hii' i hi
  have hI : Finset.Icc 1 k = Finset.Ico 1 (k + 1) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  constructor
  · intro j
    have hterm : ∀ i ∈ Finset.Icc 1 k, |M ^ (k - i) * v i j| ≤ M ^ n := by
      intro i hi
      have hi' := Finset.mem_Icc.mp hi
      have hv : |v i j| ≤ M := by
        calc |v i j| ≤ (supNorm (v i) : ℤ) := ftd5_abs_le_supNorm _ _
          _ ≤ B := hsupB i hi
          _ ≤ B * N := by nlinarith
          _ = M := hMB.symm
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < M ^ (k - i))]
      calc M ^ (k - i) * |v i j| ≤ M ^ (k - i) * M :=
            mul_le_mul_of_nonneg_left hv (by positivity)
        _ = M ^ (k - i + 1) := by rw [pow_succ]
        _ ≤ M ^ n := pow_le_pow_right₀ hM1 (by omega)
    have h1 : |∑ i ∈ Finset.Icc 1 k, M ^ (k - i) * v i j| ≤ (n : ℤ) * M ^ n := by
      calc |∑ i ∈ Finset.Icc 1 k, M ^ (k - i) * v i j|
          ≤ ∑ i ∈ Finset.Icc 1 k, |M ^ (k - i) * v i j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.Icc 1 k, M ^ n := Finset.sum_le_sum hterm
        _ = (k : ℤ) * M ^ n := by simp
        _ ≤ (n : ℤ) * M ^ n := by
            have : (k : ℤ) ≤ n := by exact_mod_cast hk
            have : (0 : ℤ) ≤ M ^ n := by positivity
            nlinarith
    refine le_trans h1 ?_
    have hn2 : (n : ℤ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
    have hMn : M ^ n = 2 ^ ((n ^ 2 + n) * n) * (N : ℤ) ^ ((n + 1) * n) := by
      rw [hMdef, mul_pow, ← pow_mul, ← pow_mul]
    rw [hMn]
    have he1 : n + (n ^ 2 + n) * n ≤ 4 * n ^ 3 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp
      · have : n ≤ n ^ 3 := by
          calc n = n ^ 1 := (pow_one n).symm
            _ ≤ n ^ 3 := Nat.pow_le_pow_right h (by norm_num)
        have : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right h (by norm_num)
        nlinarith
    have he2 : (n + 1) * n ≤ n * (n + 2) := by nlinarith
    have hp1 : (2 : ℤ) ^ n * 2 ^ ((n ^ 2 + n) * n) ≤ 2 ^ (4 * n ^ 3) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) he1
    have hp2 : (N : ℤ) ^ ((n + 1) * n) ≤ (N : ℤ) ^ (n * (n + 2)) :=
      pow_le_pow_right₀ hN1 he2
    have hq1 : (0 : ℤ) ≤ 2 ^ ((n ^ 2 + n) * n) := by positivity
    have hq2 : (0 : ℤ) ≤ (N : ℤ) ^ ((n + 1) * n) := by positivity
    calc (n : ℤ) * (2 ^ ((n ^ 2 + n) * n) * (N : ℤ) ^ ((n + 1) * n))
        ≤ 2 ^ n * (2 ^ ((n ^ 2 + n) * n) * (N : ℤ) ^ ((n + 1) * n)) :=
          mul_le_mul_of_nonneg_right hn2 (by positivity)
      _ = (2 ^ n * 2 ^ ((n ^ 2 + n) * n)) * (N : ℤ) ^ ((n + 1) * n) := by ring
      _ ≤ 2 ^ (4 * n ^ 3) * (N : ℤ) ^ (n * (n + 2)) :=
          mul_le_mul hp1 hp2 hq2 (by positivity)
  · intro b hb
    set c : ℕ → ℤ := fun i => ∑ j, v i j * b j with hcdef
    have hL : ∑ j, (w j : ℝ) * (b j : ℝ) =
        ∑ i ∈ Finset.Ico 1 (k + 1), lam i * (c i : ℝ) := by
      rw [← hI]
      simp only [hw, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hcdef]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hR : ((∑ j, (∑ i ∈ Finset.Icc 1 k, M ^ (k - i) * v i j) * b j : ℤ) : ℝ) =
        ∑ i ∈ Finset.Ico 1 (k + 1), ((M : ℝ)) ^ (k - i) * (c i : ℝ) := by
      rw [← hI]
      push_cast
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hcdef]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hL, hR]
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hcb : ∀ i, 1 ≤ i → i < k + 1 →
        |(c i : ℝ)| ≤ (supNorm (v i) : ℝ) * ((N : ℝ) - 1) := by
      intro i _ _
      have h1 := ftd5_dot_le (v i) b
      have h2 : |c i| ≤ (supNorm (v i) : ℤ) * ((N : ℤ) - 1) := by
        refine le_trans h1 ?_
        exact mul_le_mul_of_nonneg_left hb (by positivity)
      have h3 : ((|c i| : ℤ) : ℝ) ≤ (((supNorm (v i) : ℤ) * ((N : ℤ) - 1) : ℤ) : ℝ) := by
        exact_mod_cast h2
      push_cast at h3
      exact h3
    have hMpos : (0 : ℝ) < (M : ℝ) := by
      have : (0 : ℤ) < M := by omega
      exact_mod_cast this
    have hposL : ∀ m, 1 ≤ m → m < k + 1 → 0 < lam m := fun m h1 h2 =>
      hlam m (Finset.mem_Icc.mpr ⟨h1, by omega⟩)
    have hposR : ∀ m, 1 ≤ m → m < k + 1 → 0 < (M : ℝ) ^ (k - m) := fun m _ _ =>
      pow_pos hMpos _
    have htL := ftd5_tail lam (fun i => (supNorm (v i) : ℝ) * ((N : ℝ) - 1)) c (k + 1)
      hposL hcb (by
        intro m hm hmk
        have h := hIII (m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        obtain ⟨hv0, hle⟩ := h
        have hs : (1 : ℝ) ≤ (supNorm (v (m + 1)) : ℝ) := by
          exact_mod_cast ftd5_supNorm_pos _ hv0
        have hp := hposL (m + 1) (by omega) (by omega)
        simp only [Nat.add_sub_cancel] at hle
        calc lam (m + 1) * ((supNorm (v (m + 1)) : ℝ) * ((N : ℝ) - 1) + 1)
            ≤ lam (m + 1) * ((N : ℝ) * (supNorm (v (m + 1)) : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ hp.le
              nlinarith
          _ ≤ lam m := hle)
    have htR := ftd5_tail (fun i => (M : ℝ) ^ (k - i))
      (fun i => (supNorm (v i) : ℝ) * ((N : ℝ) - 1)) c (k + 1)
      hposR hcb (by
        intro m hm hmk
        have hsB : (supNorm (v (m + 1)) : ℝ) ≤ (B : ℝ) := by
          exact_mod_cast hsupB (m + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        have hB1r : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB1
        have hMBr : (M : ℝ) = (B : ℝ) * (N : ℝ) := by
          rw [hMB]; push_cast; ring
        have hD : (supNorm (v (m + 1)) : ℝ) * ((N : ℝ) - 1) + 1 ≤ (M : ℝ) := by
          rw [hMBr]; nlinarith
        have hkm : k - m = k - (m + 1) + 1 := by omega
        show (M : ℝ) ^ (k - (m + 1)) * ((supNorm (v (m + 1)) : ℝ) * ((N : ℝ) - 1) + 1) ≤
          (M : ℝ) ^ (k - m)
        rw [hkm, pow_succ]
        exact mul_le_mul_of_nonneg_left hD (by positivity))
    exact ftd5_sign lam (fun i => (M : ℝ) ^ (k - i)) c (k + 1) hposL hposR htL htR 1 le_rfl
