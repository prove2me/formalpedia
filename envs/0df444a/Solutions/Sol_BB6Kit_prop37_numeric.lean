-- Prove2me | solution 1 for BB6Kit.prop37_numeric
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T07:25:00.408313+00:00
-- url     : https://prove2.me/submissions/a678d851-5f4a-4c23-a6bd-12ab43d0fec3

import Mathlib
import Definitions.Def_BB6Delta
import Definitions.Def_BB6Kit
import Definitions.Def_BB6Psi
import Definitions.Def_BB6Theta
import Theorems.Thm_BB6Kit_lemma34
import Theorems.Thm_BB6Kit_bound314
import Theorems.Thm_BB6Kit_rows_counts

open Finset

set_option maxHeartbeats 4000000 in
theorem solution (K L R S T N b1 b2 b3 α1 α2 α3 : ℕ) (ρ : ℝ)
    (hK : 3 ≤ K) (hL : 5 ≤ L) (hN : N = K * (K + 1) * L / 2) (hRST : N ≤ R * S * T)
    (hα1 : 1 < α1) (hα2 : 1 < α2) (hα3 : 1 < α3) (hind : BB6Kit.MultIndep α1 α2 α3)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1)
    (hΛ : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ≠ 0) (hρ : 2 ≤ ρ)
    (kml rst : Fin N → ℕ × ℕ × ℕ) (hrows : BB6Kit.RowsOK K L N kml) (hcols : BB6Kit.ColsOK R S T N rst)
    (hsmall : BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) < ρ ^ (-((K : ℝ) * L))) :
    ∀ I : Finset (Fin N),
      BB6Kit.lamPrime L T b3 ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) ^ (N - I.card) *
        (((N.factorial : ℝ) * (∏ i, (((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) ^ (kml i).1 * ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) ^ (kml i).2.1 / (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) * (ρ * (((R : ℝ) - 1) / 2 + ((b1 / Nat.gcd b1 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b1 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).1) * (ρ * (((S : ℝ) - 1) / 2 + ((b2 / Nat.gcd b2 b3 : ℕ) : ℝ) / ((b3 / Nat.gcd b2 b3 : ℕ) : ℝ) * (((T : ℝ) - 1) / 2))) ^ (∑ i, (kml i).2.1) *
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) +
          BB6Kit.GK N L R S T T * (Real.log (α3 : ℝ) + |((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ))| / (b3 : ℝ))))) / ρ ^ BB6Theta.theta (K - 1) I.card) <
        Real.exp (ρ * (BB6Kit.GK N L R S T R * Real.log (α1 : ℝ) + BB6Kit.GK N L R S T S * Real.log (α2 : ℝ) + BB6Kit.GK N L R S T T * Real.log (α3 : ℝ)) + Real.log (N.factorial : ℝ) +
        (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (BB6Kit.bK K R S T (b1 / Nat.gcd b1 b3) (b3 / Nat.gcd b1 b3) (b2 / Nat.gcd b2 b3) (b3 / Nat.gcd b2 b3)) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L)) * Real.log ρ + 0.001) := by
  intro I
  have hI : I.card ≤ N := by simpa using I.card_le_univ
  obtain ⟨hSk, hSm, hfact⟩ := BB6Kit.rows_counts K L N kml hK hL hN hrows
  have h34 := BB6Kit.lemma34 K L N I.card hK hL hN hI
  have h314 := BB6Kit.bound314 K L ρ hK hL hρ
  -- reduced coefficients
  have hg13 : 0 < Nat.gcd b1 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hg23 : 0 < Nat.gcd b2 b3 := Nat.gcd_pos_of_pos_right _ hb3
  have hc2 : 0 < b3 / Nat.gcd b1 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg13
  have hc4 : 0 < b3 / Nat.gcd b2 b3 := Nat.div_pos (Nat.gcd_le_right _ hb3) hg23
  generalize b1 / Nat.gcd b1 b3 = c1
  generalize b3 / Nat.gcd b1 b3 = c2 at hc2 ⊢
  generalize b2 / Nat.gcd b2 b3 = c3
  generalize b3 / Nat.gcd b2 b3 = c4 at hc4 ⊢
  generalize hΛdef : ((b1 : ℝ) * Real.log (α1 : ℝ) + (b2 : ℝ) * Real.log (α2 : ℝ) - (b3 : ℝ) * Real.log (α3 : ℝ)) = Λ at hΛ hsmall ⊢
  -- sizes
  have hNpos : 0 < N := by
    rw [hN]
    refine Nat.div_pos ?_ (by norm_num)
    have : 3 * 4 * 5 ≤ K * (K + 1) * L := Nat.mul_le_mul (Nat.mul_le_mul hK (by omega)) hL
    omega
  have hprod : 0 < R * S * T := lt_of_lt_of_le hNpos hRST
  have hR : 0 < R := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hS : 0 < S := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hT : 0 < T := Nat.pos_of_ne_zero (by rintro rfl; simp at hprod)
  have hRr : (1:ℝ) ≤ R := by exact_mod_cast hR
  have hSr : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hLr : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hKr : (3:ℝ) ≤ K := by exact_mod_cast hK
  have hb3r : (0:ℝ) < b3 := by exact_mod_cast hb3
  have hc2r : (0:ℝ) < c2 := by exact_mod_cast hc2
  have hc4r : (0:ℝ) < c4 := by exact_mod_cast hc4
  have hNr : (0:ℝ) < N := by exact_mod_cast hNpos
  have hρ0 : 0 < ρ := by linarith
  have hlr : 0 < Real.log ρ := Real.log_pos (by linarith)
  have hNA : (N:ℝ) = ((K:ℝ) * ((K:ℝ) + 1) / 2) * L := by
    have hdvd : 2 ∣ K * (K + 1) * L := (Nat.even_mul_succ_self K).two_dvd.mul_right L
    rw [hN, Nat.cast_div hdvd (by norm_num : ((2:ℕ):ℝ) ≠ 0)]
    push_cast
    ring
  have hRSTr : (N:ℝ) ≤ (R:ℝ) * S * T := by exact_mod_cast hRST
  -- Λ′
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (L : ℝ) * T * |Λ| / (2 * b3) := ⟨_, rfl⟩
  have hX0 : 0 < X := by
    rw [hX]
    have := abs_pos.mpr hΛ
    positivity
  have hLpX : BB6Kit.lamPrime L T b3 Λ = X * Real.exp X := by
    unfold BB6Kit.lamPrime
    rw [hX]
    ring
  generalize hLpdef : BB6Kit.lamPrime L T b3 Λ = Lp at hsmall hLpX ⊢
  have hLpos : 0 < Lp := by rw [hLpX]; positivity
  have hXLp : X ≤ Lp := by
    rw [hLpX]
    exact le_mul_of_one_le_right hX0.le (Real.one_le_exp hX0.le)
  -- (3.14)
  have hg : 0 ≤ BB6Kit.gK N R S T ∧ BB6Kit.gK N R S T ≤ 1 / 4 := by
    unfold BB6Kit.gK
    have h12 : (N:ℝ) / (12 * (R:ℝ) * S * T) ≤ 1 / 12 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h0 : 0 ≤ (N:ℝ) / (12 * (R:ℝ) * S * T) := by positivity
    constructor <;> linarith
  have h314' : ρ * BB6Kit.GK N L R S T T * |Λ| / (b3 : ℝ) < 0.001 := by
    have e : ρ * BB6Kit.GK N L R S T T * |Λ| / (b3 : ℝ) = ρ * N * BB6Kit.gK N R S T * X := by
      unfold BB6Kit.GK
      rw [hX]
      field_simp
      try ring
    rw [e]
    have p1 : ρ * N * BB6Kit.gK N R S T * X ≤ ρ * N * (1 / 4) * Lp := by
      have := mul_le_mul hg.2 hXLp hX0.le (by norm_num)
      have hρN : 0 ≤ ρ * N := by positivity
      have h2 := mul_le_mul_of_nonneg_left this hρN
      linarith
    have p2 : ρ * N * (1 / 4) * Lp < ρ * N * (1 / 4) * ρ ^ (-((K : ℝ) * L)) :=
      mul_lt_mul_of_pos_left hsmall (by positivity)
    have p3 : ρ * N * (1 / 4) * ρ ^ (-((K : ℝ) * L)) = ρ * ((K : ℝ) * ((K : ℝ) + 1) * L) / 8 * ρ ^ (-((K : ℝ) * L)) := by
      rw [hNA]; ring
    linarith
  -- (3.15)
  have hlogLp : Real.log Lp < -((K : ℝ) * L) * Real.log ρ := by
    have := Real.log_lt_log hLpos hsmall
    rwa [Real.log_rpow hρ0] at this
  have hn : ((N - I.card : ℕ) : ℝ) = (N : ℝ) - I.card := Nat.cast_sub hI
  have hIr : (I.card : ℝ) ≤ N := by exact_mod_cast hI
  have F1 : ((N - I.card : ℕ) : ℝ) * Real.log Lp ≤ ((N : ℝ) - I.card) * (-((K : ℝ) * L) * Real.log ρ) := by
    rw [hn]
    exact mul_le_mul_of_nonneg_left hlogLp.le (by linarith)
  -- Lemma 3.4 and the bracket identity
  have h34' := mul_le_mul_of_nonneg_right h34 hlr.le
  have F4 : (2 * ((N : ℝ) * ((K : ℝ) - 1) / 3) -
      (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) +
      (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
          16 / (3 * (K : ℝ) ^ 2 * L))) * Real.log ρ ≤ 0 := by
    have e : 2 * ((N : ℝ) * ((K : ℝ) - 1) / 3) -
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 + 2 / (L : ℝ) - 6 / ((K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2)) +
        (N : ℝ) ^ 2 / (2 * (K : ℝ)) * (1 - 2 / (3 * (L : ℝ)) - 2 / (3 * (K : ℝ) * L) - 1 / (3 * (L : ℝ) ^ 2) -
            16 / (3 * (K : ℝ) ^ 2 * L)) = -(2 * ((K : ℝ) + 1) * L / (3 * K)) := by
      have hK0 : (K : ℝ) ≠ 0 := by linarith
      have hL0 : (L : ℝ) ≠ 0 := hLr.ne'
      rw [hNA]
      field_simp
      ring
    rw [e]
    have : 0 < 2 * ((K : ℝ) + 1) * L / (3 * K) := by positivity
    have h2 := mul_pos this hlr
    linarith
  -- η₀, ζ₀
  obtain ⟨η0, hη0⟩ : ∃ η0 : ℝ, η0 = ((R : ℝ) - 1) / 2 + (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ0 : ℝ, ζ0 = ((S : ℝ) - 1) / 2 + (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2) := ⟨_, rfl⟩
  have hη0n : 0 ≤ η0 := by
    rw [hη0]
    have : (0:ℝ) ≤ (c1 : ℝ) / c2 := by positivity
    have : (0:ℝ) ≤ (c1 : ℝ) / c2 * (((T : ℝ) - 1) / 2) := mul_nonneg this (by linarith)
    linarith
  have hζ0n : 0 ≤ ζ0 := by
    rw [hζ0]
    have : (0:ℝ) ≤ (c3 : ℝ) / c4 := by positivity
    have : (0:ℝ) ≤ (c3 : ℝ) / c4 * (((T : ℝ) - 1) / 2) := mul_nonneg this (by linarith)
    linarith
  have hbK : BB6Kit.bK K R S T c1 c2 c3 c4 = ((c2 : ℝ) * η0) * ((c4 : ℝ) * ζ0) *
      (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) ^ (-(12 : ℝ) / ((K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1))) := by
    unfold BB6Kit.bK
    rw [hη0, hζ0]
  rw [hbK, ← hη0, ← hζ0]
  have hsk0 : (∑ i, (kml i).1) ≠ 0 := by
    intro h0
    have : (∑ i, ((kml i).1 : ℝ)) = 0 := by exact_mod_cast h0
    rw [hSk] at this
    have : (0:ℝ) < (N : ℝ) * ((K : ℝ) - 1) / 3 := by
      have : (0:ℝ) < (K : ℝ) - 1 := by linarith
      positivity
    linarith
  have hsm0 : (∑ i, (kml i).2.1) ≠ 0 := by
    intro h0
    have : (∑ i, ((kml i).2.1 : ℝ)) = 0 := by exact_mod_cast h0
    rw [hSm] at this
    have : (0:ℝ) < (N : ℝ) * ((K : ℝ) - 1) / 3 := by
      have : (0:ℝ) < (K : ℝ) - 1 := by linarith
      positivity
    linarith
  rcases eq_or_lt_of_le hη0n with h0 | hηp
  · rw [← h0, mul_zero, zero_pow hsk0]
    simp only [mul_zero, zero_mul, zero_div]
    exact Real.exp_pos _
  rcases eq_or_lt_of_le hζ0n with h0 | hζp
  · rw [← h0, mul_zero, zero_pow hsm0]
    simp only [mul_zero, zero_mul, zero_div]
    exact Real.exp_pos _
  -- positive case: compare logarithms
  have hlead : ∀ i, 0 < (c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
      (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)) := by
    intro i
    have := Nat.factorial_pos (kml i).1
    have := Nat.factorial_pos (kml i).2.1
    positivity
  have hPL : 0 < ∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
      (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ))) := prod_pos (fun i _ => hlead i)
  have hPf : 0 < ∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k)) := by
    apply prod_pos
    intro k _
    have := Nat.factorial_pos k
    positivity
  have hlogPL : Real.log (∏ i, ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
      (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ)))) =
      (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log c2 + (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log c4 -
        2 * (L : ℝ) * Real.log (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) := by
    rw [Real.log_prod (fun i _ => (hlead i).ne')]
    have e : ∀ i, Real.log ((c2 : ℝ) ^ (kml i).1 * (c4 : ℝ) ^ (kml i).2.1 /
        (((kml i).1.factorial : ℝ) * ((kml i).2.1.factorial : ℝ))) =
        ((kml i).1 : ℝ) * Real.log c2 + ((kml i).2.1 : ℝ) * Real.log c4 -
          (Real.log ((kml i).1.factorial : ℝ) + Real.log ((kml i).2.1.factorial : ℝ)) := by
      intro i
      have f1 : (0:ℝ) < ((kml i).1.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have f2 : (0:ℝ) < ((kml i).2.1.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, Real.log_mul f1.ne' f2.ne']
    rw [sum_congr rfl (fun i _ => e i), sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, hSk, hSm, hfact]
  have hlogb : (N : ℝ) * ((K : ℝ) - 1) / 3 * Real.log (((c2 : ℝ) * η0) * ((c4 : ℝ) * ζ0) *
      (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) ^ (-(12 : ℝ) / ((K : ℝ) * ((K : ℝ) - 1) * ((K : ℝ) + 1)))) =
      (N : ℝ) * ((K : ℝ) - 1) / 3 * (Real.log c2 + Real.log η0 + Real.log c4 + Real.log ζ0) -
        2 * (L : ℝ) * Real.log (∏ k ∈ Finset.Ico 1 K, ((k.factorial : ℝ) ^ (K - k))) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul hc2r.ne' hηp.ne', Real.log_mul hc4r.ne' hζp.ne', Real.log_rpow hPf]
    have hK1 : (K : ℝ) - 1 ≠ 0 := by linarith
    have hK0 : (K : ℝ) ≠ 0 := by linarith
    have hK2 : (K : ℝ) + 1 ≠ 0 := by linarith
    rw [hNA]
    field_simp
    ring
  rw [hlogb]
  -- the generic exponential/logarithm step
  have key : ∀ (Lq Fa PL A Bv Gt r E : ℝ) (n Sk Sm Th : ℕ), 0 < Lq → 0 < Fa → 0 < PL → 0 < A → 0 < Bv → 0 < r →
      (n : ℝ) * Real.log Lq + Real.log Fa + Real.log PL + (Sk : ℝ) * Real.log A + (Sm : ℝ) * Real.log Bv + Gt -
        (Th : ℝ) * Real.log r < E →
      Lq ^ n * (Fa * PL * A ^ Sk * Bv ^ Sm * Real.exp Gt / r ^ Th) < Real.exp E := by
    intro Lq Fa PL A Bv Gt r E n Sk Sm Th hLq hFa hPL' hA hB hr H
    have e : Lq ^ n * (Fa * PL * A ^ Sk * Bv ^ Sm * Real.exp Gt / r ^ Th) =
        Real.exp ((n : ℝ) * Real.log Lq + Real.log Fa + Real.log PL + (Sk : ℝ) * Real.log A +
          (Sm : ℝ) * Real.log Bv + Gt - (Th : ℝ) * Real.log r) := by
      rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add,
        Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
        Real.exp_log hLq, Real.exp_log hFa, Real.exp_log hPL', Real.exp_log hA, Real.exp_log hB, Real.exp_log hr]
      ring
    rw [e]
    exact Real.exp_lt_exp.mpr H
  apply key _ _ _ _ _ _ _ _ _ _ _ _ hLpos (by exact_mod_cast Nat.factorial_pos N) hPL (mul_pos hρ0 hηp)
    (mul_pos hρ0 hζp) hρ0
  rw [hlogPL, hn, Real.log_mul hρ0.ne' hηp.ne', Real.log_mul hρ0.ne' hζp.ne']
  push_cast
  rw [hSk, hSm]
  rw [hn] at F1
  linear_combination F1 + h34' + F4 + h314'
