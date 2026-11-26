-- Prove2me | solution 1 for Erdos287.maximum_bands_from_dyadic_prime_pairs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:55:17.952819+00:00
-- url     : https://prove2.me/submissions/47e937ae-0247-4734-95d3-d782b83de3c0

import Mathlib
import Theorems.Thm_Erdos287_compatible_slopes_realize_distance_band
import Theorems.Thm_Erdos287_prime_power_pair_excludes_band

open Finset

set_option autoImplicit false

/-- Two primes in each large dyadic parameter window give bands of covered maxima. -/
theorem solution (N : ℕ) (hN : 2 ≤ N)
    (hpair_supply : ∀ a : ℕ → ℕ, (∀ i < N, 0 < a i) →
      (∀ i j, i < j → j < N → a i < a j) →
      ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T → ∃ t : ℕ, T ≤ t ∧ t ≤ 2 * T ∧
        ∃ i j, i < j ∧ j < N ∧ Nat.Prime (a i * t + 1) ∧ Nat.Prime (a j * t + 1)) :
    ∃ T₁ : ℕ, ∀ T : ℕ, T₁ ≤ T →
      ∃ x : ℕ, T ≤ x ∧ 2 * x ≤ (12 * N + 2) * T ∧
        ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
          (∀ i, i < k → 1 < f i) →
          (∀ i j, i < j → j < k → f i < f j) →
          (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) →
          x + 1 ≤ f (k - 1) → f (k - 1) ≤ 2 * x →
          ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have he' : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
  obtain ⟨a, L, U, hL, hLU, hU, ha, hpair⟩ :=
    Erdos287.compatible_slopes_realize_distance_band N id (fun _ _ h => h)
      1 1 (by norm_num) le_rfl (by
        rw [mul_one]
        linarith)
  have hUp := hL.trans_le hLU
  have hU₃ : U < 3 * L := hU.trans (mul_lt_mul_of_pos_right he' hL)
  let cPair (i j : ℕ) := (a i / (a j - a i)) * a j
  let r (i : ℕ) := (1 : ℝ) / a i
  have hinv (i j : ℕ) (hij : i < j) (hj : j < N) :
      (0 : ℝ) < cPair i j ∧ 1 / (cPair i j : ℝ) = r i - r j := by
    obtain ⟨hlt, hdiv, _⟩ := hpair i j hij hj
    have hi := hij.trans hj
    have hai : (0 : ℝ) < a i := by exact_mod_cast ha i hi
    have haj : (0 : ℝ) < a j := by exact_mod_cast ha j hj
    have hdp : (0 : ℝ) < (a j - a i : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hd : ((a j - a i : ℕ) : ℝ) = (a j : ℝ) - a i := Nat.cast_sub hlt.le
    have hcoef : ((a i / (a j - a i) : ℕ) : ℝ) * ((a j - a i : ℕ) : ℝ) =
        (a i : ℝ) := by exact_mod_cast Nat.div_mul_cancel hdiv
    have hprod : (cPair i j : ℝ) = (a i : ℝ) * a j / ((a j : ℝ) - a i) := by
      apply (eq_div_iff (hd ▸ hdp.ne')).mpr
      push_cast [cPair]
      rw [← hd]
      linear_combination (a j : ℝ) * hcoef
    refine ⟨by rw [hprod, ← hd]; exact div_pos (mul_pos hai haj) hdp, ?_⟩
    rw [hprod]
    dsimp [r]
    have hne : (a j : ℝ) - a i ≠ 0 := hd ▸ hdp.ne'
    field_simp [hai.ne', haj.ne', hne]
  have hadj (i : ℕ) (hi : i + 1 < N) :
      1 / U ≤ r i - r (i + 1) ∧ r i - r (i + 1) ≤ 1 / L := by
    have hdist : ((id (i + 1) : ℕ) : ℝ) - id i = 1 := by simp
    obtain ⟨hlo, hhi⟩ := (hpair i (i + 1) (by omega) hi).2.2
      (by rw [hdist]) (by rw [hdist])
    have hlo' : L ≤ (cPair i (i + 1) : ℝ) := by simpa [cPair] using hlo
    have hhi' : (cPair i (i + 1) : ℝ) ≤ U := by simpa [cPair] using hhi
    obtain ⟨hp, heq⟩ := hinv i (i + 1) (by omega) hi
    rw [← heq]
    exact ⟨one_div_le_one_div_of_le hp hhi', one_div_le_one_div_of_le hL hlo'⟩
  have htel (i d : ℕ) (hid : i + d < N) :
      (d : ℝ) / U ≤ r i - r (i + d) ∧ r i - r (i + d) ≤ (d : ℝ) / L := by
    induction d with
    | zero => simp
    | succ d ih =>
      obtain ⟨hl, hu⟩ := ih (by omega)
      obtain ⟨hl', hu'⟩ := hadj (i + d) (by omega)
      simp only [Nat.cast_succ, Nat.add_succ, add_div]
      constructor <;> linarith
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcPair (i j : ℕ) (hij : i < j) (hj : j < N) :
      L / N ≤ (cPair i j : ℝ) ∧ (cPair i j : ℝ) ≤ U := by
    have hijd : i + (j - i) = j := Nat.add_sub_cancel' hij.le
    have hh := htel i (j - i) (by omega)
    obtain ⟨hpos, heq⟩ := hinv i j hij hj
    rw [hijd, ← heq] at hh
    have h₁ : (1 : ℝ) ≤ ((j - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hij
    have h₂ : ((j - i : ℕ) : ℝ) ≤ N := by
      exact_mod_cast (show j - i ≤ N by omega)
    have hinv₁ := (div_le_div_of_nonneg_right h₁ hUp.le).trans hh.1
    have hinv₂ := hh.2.trans (div_le_div_of_nonneg_right h₂ hL.le)
    have hinv₃ : 1 / (L / (N : ℝ)) = (N : ℝ) / L := by
      field_simp
    refine ⟨(one_div_le_one_div hpos (div_pos hL hNp)).mp ?_,
      (one_div_le_one_div hUp hpos).mp hinv₁⟩
    rwa [hinv₃]
  obtain ⟨T₀, hsupply⟩ := hpair_supply a ha (fun i j hij hj => (hpair i j hij hj).1)
  let A := ∑ i ∈ range N, a i
  have hA (i : ℕ) (hi : i < N) : a i ≤ A :=
    single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.mpr hi)
  have hApos : 0 < A := (ha 0 (by omega)).trans_le (hA 0 (by omega))
  let B := 2 * A * (A + 1)
  let S := ∑ j ∈ Icc 1 B, Nat.lcmUpto B / j
  let T₀' := max T₀ (max (B + 1) (S + 1))
  let K := (N : ℝ) / L
  have hK := div_pos hNp hL
  have hBpos : 0 < B := by dsimp [B]; positivity
  obtain ⟨T₁, hT₁⟩ := exists_nat_gt (max ((T₀' : ℝ) / K) (6 * L + A))
  refine ⟨T₁, ?_⟩
  intro T hT
  have hbig : max ((T₀' : ℝ) / K) (6 * L + A) < (T : ℝ) :=
    hT₁.trans_le (by exact_mod_cast hT)
  let V := ⌈K * (T : ℝ)⌉₊
  have hV₁ : K * (T : ℝ) ≤ V := Nat.le_ceil _
  have hV₂ : (V : ℝ) < K * (T : ℝ) + 1 :=
    Nat.ceil_lt_add_one (mul_nonneg hK.le (Nat.cast_nonneg _))
  have hT₀' : T₀' ≤ V := by
    have h := (div_lt_iff₀ hK).mp ((le_max_left _ _).trans_lt hbig)
    rw [mul_comm] at h
    exact_mod_cast (h.trans_le hV₁).le
  have hT₀ : T₀ ≤ V := (le_max_left _ _).trans hT₀'
  have hBT : B < V := ((le_max_left (B + 1) (S + 1)).trans
    ((le_max_right _ _).trans hT₀'))
  have hST : S < V := ((le_max_right (B + 1) (S + 1)).trans
    ((le_max_right _ _).trans hT₀'))
  obtain ⟨t, ht, ht₂, i, j, hij, hj, hp, hq⟩ := hsupply V hT₀
  let p := a i * t + 1
  let q := a j * t + 1
  let d := a j - a i
  let c := a i / d
  let x := c * q
  have hi : i < N := hij.trans hj
  have ⟨hal, hdiv, _⟩ := hpair i j hij hj
  have hcoef : c * d = a i := Nat.div_mul_cancel hdiv
  have hnext : (c + 1) * d = a j := by
    rw [add_mul, one_mul, hcoef]
    dsimp [d]
    omega
  have hx1 : (c + 1) * p = x + 1 := by
    calc
      (c + 1) * p = (c + 1) * (c * d * t + 1) := by rw [hcoef]
      _ = c * ((c + 1) * d * t + 1) + 1 := by ring
      _ = x + 1 := by rw [hnext]
  have hc : 0 < c := Nat.pos_of_mul_pos_right (hcoef ▸ ha i hi)
  have hcA : c ≤ A := (Nat.div_le_self _ _).trans (hA i hi)
  have htp : t ≤ p := by
    have h := Nat.mul_le_mul_right t (show 1 ≤ a i from ha i hi)
    simpa [p] using h.trans (Nat.le_succ _)
  have htq : t ≤ q := by
    have h := Nat.mul_le_mul_right t (show 1 ≤ a j from ha j hj)
    simpa [q] using h.trans (Nat.le_succ _)
  have htx : t ≤ x := by
    have h := Nat.mul_le_mul_right q (show 1 ≤ c from hc)
    exact htq.trans (by simpa only [one_mul] using h)
  have htpos : 0 < t := hBpos.trans (hBT.trans_le ht)
  have hqx : q ≤ (A + 1) * t := by
    have h := Nat.mul_le_mul_right t (hA j hj)
    rw [add_mul, one_mul]
    dsimp [q]
    omega
  have hxt : 2 * x ≤ B * t := by
    calc
      2 * x ≤ 2 * (A * ((A + 1) * t)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul hcA hqx)
      _ = B * t := by dsimp [B]; ring
  have hxR : (x : ℝ) = (cPair i j : ℝ) * t + c := by
    simp [x, q, cPair, c, d, mul_add, mul_assoc]
  obtain ⟨hcLo, hcHi⟩ := hcPair i j hij hj
  have htR₁ : K * (T : ℝ) ≤ t := hV₁.trans (by exact_mod_cast ht)
  have htR₂ : (t : ℝ) ≤ 2 * (K * (T : ℝ) + 1) := by
    have h : (t : ℝ) ≤ 2 * V := by exact_mod_cast ht₂
    linarith
  have hKmul : L * K = (N : ℝ) := by dsimp [K]; field_simp
  have hxLo : (T : ℝ) ≤ x := by
    calc
      (T : ℝ) = (L / (N : ℝ)) * (K * (T : ℝ)) := by
        dsimp [K]
        field_simp
      _ ≤ (L / (N : ℝ)) * t := mul_le_mul_of_nonneg_left htR₁ (div_pos hL hNp).le
      _ ≤ (cPair i j : ℝ) * t := mul_le_mul_of_nonneg_right hcLo (Nat.cast_nonneg _)
      _ ≤ x := by rw [hxR]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
  have hxHi : (x : ℝ) ≤ (6 * (N : ℝ) + 1) * T := by
    calc
      (x : ℝ) ≤ (3 * L) * (t : ℝ) + A := by
        rw [hxR]
        exact add_le_add (mul_le_mul_of_nonneg_right (hcHi.trans hU₃.le) (Nat.cast_nonneg _))
          (by exact_mod_cast hcA)
      _ ≤ (3 * L) * (2 * (K * (T : ℝ) + 1)) + A :=
        add_le_add (mul_le_mul_of_nonneg_left htR₂
          (show 0 ≤ (3 : ℝ) * L from mul_nonneg (by norm_num) hL.le)) le_rfl
      _ = 6 * (N : ℝ) * T + (6 * L + A) := by
        linear_combination 6 * (T : ℝ) * hKmul
      _ ≤ (6 * (N : ℝ) + 1) * T := by linarith [(le_max_right _ _).trans_lt hbig]
  refine ⟨x, by exact_mod_cast hxLo, ?_, ?_⟩
  · have h : (2 : ℝ) * x ≤ (12 * (N : ℝ) + 2) * T := by linarith
    exact_mod_cast h
  intro k f hk hf hmono hsum hM₁ hM₂
  have hx : 0 < x := htpos.trans_le htx
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hMR : (f (k - 1) : ℝ) ≤ 2 * x := by exact_mod_cast hM₂
  have hMhi := hMR.trans_lt (mul_lt_mul_of_pos_right he hxR)
  have hM := hM₂.trans hxt
  have hmax (r : ℕ) (htr : t ≤ r) : f (k - 1) < (B + 1) * r :=
    (hM.trans (Nat.mul_le_mul_left B htr)).trans_lt
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self B) (htpos.trans_le htr))
  have hdivq : q ∣ x := dvd_mul_left q c
  have hdivp : p ∣ x + 1 := by rw [← hx1]; exact dvd_mul_left p (c + 1)
  exact Erdos287.prime_power_pair_excludes_band k hk f hf hmono hsum x hx hM₁ hMhi
    q p 1 1 B B hq hp le_rfl le_rfl
    (by simpa using hdivq) (by simpa using hdivp)
    (hBT.trans_le (ht.trans htq)) (hBT.trans_le (ht.trans htp))
    (by simpa using hmax q htq) (by simpa using hmax p htp)
    (hST.trans_le (ht.trans htq)) (hST.trans_le (ht.trans htp))

