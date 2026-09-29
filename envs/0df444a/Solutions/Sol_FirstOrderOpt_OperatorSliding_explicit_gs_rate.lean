-- Prove2me | solution 1 for FirstOrderOpt.OperatorSliding.explicit_gs_rate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:46:57.869315+00:00
-- url     : https://prove2.me/submissions/9b48bbb0-39dd-4b3d-a9f9-3a251c64d3d1

import Mathlib

namespace FirstOrderOpt.OperatorSliding

theorem aux_egr_term (L M Dtilde N a t x : ℝ) (hL : 0 < L) (hM : 0 < M) (hD : 0 < Dtilde)
    (hN : 1 ≤ N) (ha : 1 ≤ a) (ht1 : 1 ≤ t) (hx : 1 ≤ x)
    (hceil : M ^ 2 * N * a ^ 2 / (Dtilde * L ^ 2) ≤ t) :
    (2 / (a + 1)) * (2 / ((t + 1) * (t + 2))) /
      ((2 / (a * (a + 1))) * (2 * L / a) * (1 - 2 / ((t + 1) * (t + 2))) * (x / 2) ^ 2
        * (2 / ((x - 1 + 1) * (x - 1 + 2)))) ≤ 4 * Dtilde * L / (M ^ 2 * N * t) := by
  have h1 : 1 - 2 / ((t + 1) * (t + 2)) = t * (t + 3) / ((t + 1) * (t + 2)) := by
    field_simp
    ring
  have h2 : x - 1 + 1 = x := by ring
  have h3 : x - 1 + 2 = x + 1 := by ring
  rw [h1, h2, h3]
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hx0 : 0 < x := by linarith
  have hN0 : 0 < N := by linarith
  have e : (2 / (a + 1)) * (2 / ((t + 1) * (t + 2))) /
      ((2 / (a * (a + 1))) * (2 * L / a) * (t * (t + 3) / ((t + 1) * (t + 2))) * (x / 2) ^ 2
        * (2 / (x * (x + 1)))) = 2 * a ^ 2 * (x + 1) / (L * t * (t + 3) * x) := by
    field_simp
  rw [e]
  have hc : M ^ 2 * N * a ^ 2 ≤ t * (Dtilde * L ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hceil
    exact hceil
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hx2 : x + 1 ≤ 2 * x := by linarith
  have hA : 0 ≤ M ^ 2 * N * t := by positivity
  calc 2 * a ^ 2 * (x + 1) * (M ^ 2 * N * t)
      ≤ 2 * a ^ 2 * (2 * x) * (M ^ 2 * N * t) := by
        apply mul_le_mul_of_nonneg_right _ hA
        apply mul_le_mul_of_nonneg_left hx2
        positivity
    _ = 4 * x * t * (M ^ 2 * N * a ^ 2) := by ring
    _ ≤ 4 * x * t * (t * (Dtilde * L ^ 2)) := by
        apply mul_le_mul_of_nonneg_left hc
        positivity
    _ ≤ 4 * Dtilde * L * (L * t * (t + 3) * x) := by
        have : 0 ≤ 4 * x * t * Dtilde * L ^ 2 * 3 := by positivity
        nlinarith

end FirstOrderOpt.OperatorSliding

open FirstOrderOpt.OperatorSliding

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (X : Set E) (f h chi Ψ : E → ℝ) (hΨ : ∀ u, Ψ u = f u + h u + chi u)
    (V : E → E → ℝ) (hVnonneg : ∀ a b, 0 ≤ V a b)
    (L M : ℝ) (hL : 0 < L) (hM : 0 < M)
    (x0 xstar : E) (hx0 : x0 ∈ X) (hxstar : xstar ∈ X)
    (hxstarOpt : ∀ w ∈ X, Ψ xstar ≤ Ψ w)
    (N : ℕ) (hN : 1 ≤ N) (Dtilde : ℝ) (hDtilde : 0 < Dtilde)
    (p P Γ β γ : ℕ → ℝ) (T : ℕ → ℕ)
    (hp : ∀ t : ℕ, p t = (t : ℝ) / 2)
    (hP : ∀ t : ℕ, P t = 2 / (((t : ℝ) + 1) * ((t : ℝ) + 2)))
    (hΓ : ∀ k : ℕ, 1 ≤ k → Γ k = 2 / ((k : ℝ) * ((k : ℝ) + 1)))
    (hβ : ∀ k : ℕ, 1 ≤ k → β k = 2 * L / (k : ℝ))
    (hγ : ∀ k : ℕ, 1 ≤ k → γ k = 2 / ((k : ℝ) + 1))
    (hT : ∀ k : ℕ, 1 ≤ k → T k = ⌈M ^ 2 * (N : ℝ) * (k : ℝ) ^ 2 / (Dtilde * L ^ 2)⌉₊)
    (xbar : ℕ → E) (hxbar0 : xbar 0 = x0)
    (hBd : Ψ (xbar N) - Ψ xstar ≤
      Γ N * β 1 / (1 - P (T 1)) * V x0 xstar
        + M ^ 2 * Γ N / 2 *
            ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
              γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))) :
    Ψ (xbar N) - Ψ xstar ≤ 2 * L / ((N : ℝ) * ((N : ℝ) + 1)) * (3 * V x0 xstar + 2 * Dtilde) := by
  have hV := hVnonneg x0 xstar
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  have hGN : Γ N = 2 / ((N:ℝ) * ((N:ℝ)+1)) := hΓ N hN
  have hGNpos : 0 < Γ N := by rw [hGN]; positivity
  have hTk : ∀ k : ℕ, 1 ≤ k → (M ^ 2 * (N : ℝ) * (k : ℝ) ^ 2 / (Dtilde * L ^ 2)) ≤ (T k : ℝ) := by
    intro k hk
    rw [hT k hk]
    exact Nat.le_ceil _
  have hTpos : ∀ k : ℕ, 1 ≤ k → 1 ≤ T k := by
    intro k hk
    rw [hT k hk]
    have hk' : (0:ℝ) < k := by exact_mod_cast hk
    exact Nat.ceil_pos.mpr (by positivity)
  -- first term
  have hfirst : Γ N * β 1 / (1 - P (T 1)) ≤ 3 * L * Γ N := by
    have ht : (1:ℝ) ≤ T 1 := by exact_mod_cast hTpos 1 le_rfl
    have hP1 : P (T 1) ≤ 1 / 3 := by
      rw [hP (T 1), div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hpos : 0 < 1 - P (T 1) := by linarith
    rw [hβ 1 le_rfl, div_le_iff₀ hpos, Nat.cast_one, div_one]
    nlinarith [mul_pos hL hGNpos]
  -- inner sums
  have hS : ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
      γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))
        ≤ 4 * Dtilde * L / M ^ 2 := by
    calc _ ≤ ∑ k ∈ Finset.Icc 1 N, 4 * Dtilde * L / (M ^ 2 * N) := by
          apply Finset.sum_le_sum
          intro k hk
          rw [Finset.mem_Icc] at hk
          have htk : (1:ℝ) ≤ T k := by exact_mod_cast hTpos k hk.1
          have hkr : (1:ℝ) ≤ k := by exact_mod_cast hk.1
          calc _ ≤ ∑ i ∈ Finset.Icc 1 (T k), 4 * Dtilde * L / (M ^ 2 * N * (T k : ℝ)) := by
                apply Finset.sum_le_sum
                intro i hi
                rw [Finset.mem_Icc] at hi
                have hir : (1:ℝ) ≤ i := by exact_mod_cast hi.1
                rw [hγ k hk.1, hΓ k hk.1, hβ k hk.1, hP (T k), hp i, hP (i-1),
                  Nat.cast_sub hi.1, Nat.cast_one]
                exact aux_egr_term L M Dtilde N k (T k) i hL hM hDtilde hNr hkr htk hir
                  (hTk k hk.1)
            _ = 4 * Dtilde * L / (M ^ 2 * N) := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
                field_simp
      _ = 4 * Dtilde * L / M ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
          field_simp
  have hsecond : M ^ 2 * Γ N / 2 *
      ∑ k ∈ Finset.Icc 1 N, ∑ i ∈ Finset.Icc 1 (T k),
        γ k * P (T k) / (Γ k * β k * (1 - P (T k)) * p i ^ 2 * P (i - 1))
        ≤ 2 * Γ N * L * Dtilde := by
    calc _ ≤ M ^ 2 * Γ N / 2 * (4 * Dtilde * L / M ^ 2) := by
          apply mul_le_mul_of_nonneg_left hS
          positivity
      _ = 2 * Γ N * L * Dtilde := by
          field_simp
          ring
  have hrhs : 2 * L / ((N : ℝ) * ((N : ℝ) + 1)) * (3 * V x0 xstar + 2 * Dtilde)
      = 3 * L * Γ N * V x0 xstar + 2 * Γ N * L * Dtilde := by
    rw [hGN]
    field_simp
  rw [hrhs]
  have := mul_le_mul_of_nonneg_right hfirst hV
  linarith
