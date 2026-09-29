-- Prove2me | solution 1 for FoundationsRL.Bandits.epsilon_greedy_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T05:42:20.318386+00:00
-- url     : https://prove2.me/submissions/5843fd77-4f6f-4ab4-a4e9-35dad418cb68

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret



namespace FoundationsRL.Bandits

lemma eg_sum (T : ℕ) : ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t:ℝ) + 1) ≤ 2 * Real.sqrt T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ]
    have ha := Real.sq_sqrt (show (0:ℝ) ≤ T by positivity)
    have hb := Real.sq_sqrt (show (0:ℝ) ≤ (T:ℝ) + 1 by positivity)
    have hbpos : 0 < Real.sqrt ((T:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have ha0 := Real.sqrt_nonneg (T:ℝ)
    have key : 1 / Real.sqrt ((T:ℝ) + 1) ≤ 2 * Real.sqrt ((T:ℝ) + 1) - 2 * Real.sqrt T := by
      rw [div_le_iff₀ hbpos]
      nlinarith [sq_nonneg (Real.sqrt (T:ℝ) - Real.sqrt ((T:ℝ) + 1))]
    push_cast
    linarith

theorem eg_main : ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (ε : ℝ), ε = ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / T) ^ ((1 : ℝ) / 3) →
        ∀ (piHat : ℕ → Fin A) (p : ℕ → Fin A → ℝ),
          (∀ t : ℕ, ∀ a : Fin A,
              p t a = (1 - ε) * (if a = piHat t then (1 : ℝ) else 0) + ε * (1 / A)) →
          ∀ (fhat : ℕ → Fin A → ℝ),
          (∀ t : ℕ, ∀ a : Fin A, fhat t a ≤ fhat t (piHat t)) →
          (∀ t ∈ Finset.range T, ∀ a : Fin A,
              |fhat t a - fStar a| ≤
                Real.sqrt ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / (ε * (t + 1)))) →
          regret fStar piStar T p ≤
            C * (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) *
              (Real.log ((A : ℝ) * T / δ)) ^ ((1 : ℝ) / 3) := by
  refine ⟨5, by norm_num, ?_⟩
  intro A hA fStar hf01 piStar hstar T hT δ hδ hδ1 ε hε piHat p hp fhat hgreedy hgood
  set L := Real.log ((A : ℝ) * T / δ) with hL
  have hAR : (1:ℝ) ≤ A := by exact_mod_cast hA
  have hTR : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hLpos : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hδ]; nlinarith)
  have hAL : 0 < (A:ℝ) * L := by positivity
  set u := ((A:ℝ) * L) ^ ((1:ℝ) / 3) with hu
  set v := (T:ℝ) ^ ((1:ℝ) / 3) with hv
  have hupos : 0 < u := Real.rpow_pos_of_pos hAL _
  have hvpos : 0 < v := Real.rpow_pos_of_pos (by linarith) _
  have hu3 : u ^ 3 = (A:ℝ) * L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hAL.le]; norm_num
  have hv3 : v ^ 3 = (T:ℝ) := by
    rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hεuv : ε = u / v := by
    rw [hε, Real.div_rpow hAL.le (by linarith)]
  have hεpos : 0 < ε := by rw [hεuv]; positivity
  have htarget : (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) * L ^ ((1 : ℝ) / 3)
      = u * v ^ 2 := by
    have h1 : (A : ℝ) ^ ((1 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) = u := by
      rw [hu, Real.mul_rpow (by linarith) hLpos.le]
    have h2 : (T : ℝ) ^ ((2 : ℝ) / 3) = v ^ 2 := by
      rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    rw [h2, ← h1]; ring
  set K := (A:ℝ) * L / ε with hK
  have hKuv : K = u ^ 2 * v := by
    rw [hK, ← hu3, hεuv]; field_simp
  have hround : ∀ t ∈ Finset.range T, fStar piStar - ∑ a : Fin A, p t a * fStar a ≤
      2 * Real.sqrt K * (1 / Real.sqrt ((t:ℝ) + 1)) + ε := by
    intro t ht
    have hw : ∀ a, |fhat t a - fStar a| ≤ Real.sqrt K / Real.sqrt ((t:ℝ) + 1) := by
      intro a
      have := hgood t ht a
      rwa [← div_div, Real.sqrt_div' _ (by positivity)] at this
    have hsum : ∑ a : Fin A, p t a * fStar a =
        (1 - ε) * fStar (piHat t) + ε * (1 / A) * ∑ a, fStar a := by
      have e1 : ∀ a, p t a * fStar a =
          (1 - ε) * (if a = piHat t then fStar a else 0) + ε * (1 / A) * fStar a := by
        intro a; rw [hp]; split_ifs <;> ring
      simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
    have hw1 := abs_le.mp (hw piStar)
    have hw2 := abs_le.mp (hw (piHat t))
    have hg := hgreedy t piStar
    have hD0 : 0 ≤ fStar piStar - fStar (piHat t) := by linarith [hstar (piHat t)]
    have hS0 : 0 ≤ (1 / (A:ℝ)) * ∑ a, fStar a :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => (hf01 a).1)
    have hf1 : fStar piStar ≤ 1 := (hf01 piStar).2
    have hdiv : Real.sqrt K / Real.sqrt ((t:ℝ) + 1) = Real.sqrt K * (1 / Real.sqrt ((t:ℝ) + 1)) := by
      ring
    rw [hsum]
    nlinarith [mul_nonneg hεpos.le hD0, mul_nonneg hεpos.le hS0,
      mul_le_mul_of_nonneg_left hf1 hεpos.le]
  have hsqK : Real.sqrt K = u * Real.sqrt v := by
    rw [hKuv, Real.sqrt_mul' _ hvpos.le, Real.sqrt_sq hupos.le]
  have hsqT : Real.sqrt (T:ℝ) = v * Real.sqrt v := by
    rw [← hv3, show v ^ 3 = v ^ 2 * v by ring, Real.sqrt_mul' _ hvpos.le,
      Real.sqrt_sq hvpos.le]
  have hsv : Real.sqrt v ^ 2 = v := Real.sq_sqrt hvpos.le
  have hK0 : 0 ≤ Real.sqrt K := Real.sqrt_nonneg _
  unfold regret
  calc ∑ t ∈ Finset.range T, (fStar piStar - ∑ a : Fin A, p t a * fStar a)
      ≤ ∑ t ∈ Finset.range T, (2 * Real.sqrt K * (1 / Real.sqrt ((t:ℝ) + 1)) + ε) :=
        Finset.sum_le_sum hround
    _ = 2 * Real.sqrt K * ∑ t ∈ Finset.range T, 1 / Real.sqrt ((t:ℝ) + 1) + T * ε := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ ≤ 2 * Real.sqrt K * (2 * Real.sqrt T) + T * ε := by
        gcongr
        exact eg_sum T
    _ = 5 * (u * v ^ 2) := by
        rw [hsqK, hsqT, hεuv, ← hv3]
        field_simp
        rw [hsv]
        ring
    _ = 5 * (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) * L ^ ((1 : ℝ) / 3) := by
        rw [← htarget]; ring

end FoundationsRL.Bandits

open FoundationsRL.Bandits

theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (ε : ℝ), ε = ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / T) ^ ((1 : ℝ) / 3) →
        ∀ (piHat : ℕ → Fin A) (p : ℕ → Fin A → ℝ),
          -- Eq. (2.6): ε-Greedy plays the empirical maximizer with probability `1 - ε`
          -- and a uniform random decision with probability `ε`.
          (∀ t : ℕ, ∀ a : Fin A,
              p t a = (1 - ε) * (if a = piHat t then (1 : ℝ) else 0) + ε * (1 / A)) →
          ∀ (fhat : ℕ → Fin A → ℝ),
          (∀ t : ℕ, ∀ a : Fin A, fhat t a ≤ fhat t (piHat t)) →
          -- Eq. (2.9): the good event, holding with probability at least `1 - δ`.
          (∀ t ∈ Finset.range T, ∀ a : Fin A,
              |fhat t a - fStar a| ≤ Real.sqrt ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / (ε * (t + 1)))) →
          regret fStar piStar T p ≤
            C * (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) *
              (Real.log ((A : ℝ) * T / δ)) ^ ((1 : ℝ) / 3) := by
  exact eg_main
