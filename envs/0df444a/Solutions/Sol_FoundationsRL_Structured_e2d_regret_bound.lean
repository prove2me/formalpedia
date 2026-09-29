-- Prove2me | solution 1 for FoundationsRL.Structured.e2d_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:05:25.968522+00:00
-- url     : https://prove2.me/submissions/da6fdf7d-5742-4a24-9e73-aa7cf1966eeb

import Mathlib
import Definitions.Def_FoundationsRL_Structured_DEC
import Definitions.Def_FoundationsRL_Structured_OracleGuarantee
import Definitions.Def_FoundationsRL_Structured_regret

namespace FoundationsRL.Structured

/-- Pointwise payoff bound for the inverse-gap-weighting distribution. -/
theorem aux_e2d_payoff_le {S : Type*} [Fintype S] (γ : ℝ) (hγ : 0 < γ)
    (g : S → ℝ) (A : ℝ) (Δ q p : S → ℝ)
    (hp_nonneg : ∀ π, 0 ≤ p π) (hp_sum : ∑ π, p π = 1)
    (hpΔ : ∑ π, p π * Δ π ≤ A / (2 * γ))
    (hqpos : ∀ π, 0 < q π) (hqp : ∀ π, q π ≤ p π)
    (hq_inv : ∀ π, 1 / q π = A + 2 * γ * Δ π)
    (hΔg : ∀ π a, g a - g π = Δ π - Δ a)
    (f : S → ℝ) (a : S) :
    ∑ π, p π * (f a - f π - γ * (f π - g π) ^ 2) ≤ (2 * A + 1) / (2 * γ) := by
  set h : S → ℝ := fun π => f π - g π with hh
  have hid : ∑ π, p π * (f a - f π - γ * (f π - g π) ^ 2)
      = ∑ π, p π * Δ π + ∑ π, p π * (-h π - γ / 2 * h π ^ 2)
        + (h a - Δ a) * ∑ π, p π - ∑ π, p π * (γ / 2 * h π ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun π _ => ?_
    have := hΔg π a
    simp only [hh]
    linear_combination (p π) * this
  have hS2 : ∑ π, p π * (-h π - γ / 2 * h π ^ 2) ≤ 1 / (2 * γ) := by
    calc ∑ π, p π * (-h π - γ / 2 * h π ^ 2) ≤ ∑ π, p π * (1 / (2 * γ)) := by
          refine Finset.sum_le_sum fun π _ => ?_
          refine mul_le_mul_of_nonneg_left ?_ (hp_nonneg π)
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (γ * h π + 1)]
      _ = 1 / (2 * γ) := by rw [← Finset.sum_mul, hp_sum, one_mul]
  have hS3 : p a * (γ / 2 * h a ^ 2) ≤ ∑ π, p π * (γ / 2 * h π ^ 2) :=
    Finset.single_le_sum (f := fun π => p π * (γ / 2 * h π ^ 2))
      (fun π _ => mul_nonneg (hp_nonneg π) (by positivity)) (Finset.mem_univ a)
  have hpa : 0 < p a := lt_of_lt_of_le (hqpos a) (hqp a)
  have hC2 : h a - p a * (γ / 2 * h a ^ 2) ≤ 1 / (2 * γ * p a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (γ * p a * h a - 1)]
  have hC3 : 1 / (2 * γ * p a) ≤ A / (2 * γ) + Δ a := by
    have h1 : 1 / p a ≤ 1 / q a := one_div_le_one_div_of_le (hqpos a) (hqp a)
    rw [hq_inv a] at h1
    have h2 : 1 / (2 * γ * p a) = (1 / (2 * γ)) * (1 / p a) := by
      field_simp
    have h3 : A / (2 * γ) + Δ a = (1 / (2 * γ)) * (A + 2 * γ * Δ a) := by
      field_simp
    rw [h2, h3]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hB : (2 * A + 1) / (2 * γ) = A / (2 * γ) + 1 / (2 * γ) + A / (2 * γ) := by
    field_simp
    ring
  rw [hid, hp_sum, hB]
  linarith

/-- Uniform upper bound on `decGf` (via inverse gap weighting). -/
theorem aux_e2d_decGf_le {S : Type*} [Fintype S] [Nonempty S] (F : Set (S → ℝ))
    (piStar : (S → ℝ) → S) (γ : ℝ) (hγ : 0 < γ) (g : S → ℝ) :
    decGf F piStar γ g ≤ (2 * (Fintype.card S : ℝ) + 1) / (2 * γ) := by
  classical
  obtain ⟨π0, hπ0⟩ := Finite.exists_max g
  set A : ℝ := (Fintype.card S : ℝ) with hAdef
  have hA : 1 ≤ A := by
    rw [hAdef]; exact_mod_cast Fintype.card_pos
  set Δ : S → ℝ := fun π => g π0 - g π with hΔdef
  have hΔ : ∀ π, 0 ≤ Δ π := fun π => sub_nonneg.2 (hπ0 π)
  have hden : ∀ π, 0 < A + 2 * γ * Δ π := fun π => by
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ.le) (hΔ π)
    linarith
  set q : S → ℝ := fun π => 1 / (A + 2 * γ * Δ π) with hqdef
  have hqpos : ∀ π, 0 < q π := fun π => one_div_pos.2 (hden π)
  have hq_le : ∀ π, q π ≤ 1 / A := fun π => by
    refine one_div_le_one_div_of_le (by linarith) ?_
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ.le) (hΔ π)
    linarith
  have hQ : ∑ π, q π ≤ 1 := by
    calc ∑ π, q π ≤ ∑ _π : S, 1 / A := Finset.sum_le_sum fun π _ => hq_le π
      _ = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hAdef]
        field_simp
  set p : S → ℝ := fun π => q π + if π = π0 then 1 - ∑ σ, q σ else 0 with hpdef
  have hqp : ∀ π, q π ≤ p π := fun π => by
    simp only [hpdef]
    split_ifs <;> linarith
  have hp_nonneg : ∀ π, 0 ≤ p π := fun π => le_trans (hqpos π).le (hqp π)
  have hp_sum : ∑ π, p π = 1 := by
    simp only [hpdef, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hpΔ : ∑ π, p π * Δ π ≤ A / (2 * γ) := by
    calc ∑ π, p π * Δ π ≤ ∑ _π : S, 1 / (2 * γ) := by
          refine Finset.sum_le_sum fun π _ => ?_
          have e : p π * Δ π = q π * Δ π := by
            by_cases hπ : π = π0
            · subst hπ; simp [hΔdef]
            · simp [hpdef, hπ]
          rw [e]
          simp only [hqdef]
          rw [one_div_mul_eq_div, div_le_div_iff₀ (hden π) (by positivity)]
          have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hγ.le) (hΔ π)
          nlinarith
      _ = A / (2 * γ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hAdef]
        field_simp
  have hq_inv : ∀ π, 1 / q π = A + 2 * γ * Δ π := fun π => by
    simp only [hqdef, one_div_one_div]
  have hΔg : ∀ π a, g a - g π = Δ π - Δ a := fun π a => by
    simp only [hΔdef]; ring
  have hB : 0 ≤ (2 * A + 1) / (2 * γ) := by positivity
  have hV : sSup ((fun f : S → ℝ =>
      ∑ π, p π * (f (piStar f) - f π - γ * (f π - g π) ^ 2)) '' F)
      ≤ (2 * A + 1) / (2 * γ) := by
    refine Real.sSup_le ?_ hB
    rintro _ ⟨f, _, rfl⟩
    exact aux_e2d_payoff_le γ hγ g A Δ q p hp_nonneg hp_sum hpΔ hqpos hqp hq_inv hΔg f
      (piStar f)
  unfold decGf
  by_cases hbdd : BddBelow ((fun p : S → ℝ =>
      sSup ((fun f : S → ℝ =>
          ∑ π, p π * (f (piStar f) - f π - γ * (f π - g π) ^ 2)) '' F))
    '' {p : S → ℝ | (∀ π, 0 ≤ p π) ∧ ∑ π, p π = 1})
  · refine le_trans (csInf_le hbdd ⟨p, ⟨hp_nonneg, hp_sum⟩, rfl⟩) hV
  · rw [Real.sInf_of_not_bddBelow hbdd]
    exact hB

end FoundationsRL.Structured

open FoundationsRL.Structured

theorem solution {S : Type*} [Fintype S] (F : Set (S → ℝ))
    (piStar : (S → ℝ) → S) (hpiStar : ∀ f ∈ F, ∀ π, f π ≤ f (piStar f))
    (fstar : S → ℝ) (hfstar : fstar ∈ F)
    (T : ℕ) (γ : ℝ) (hγ : 0 < γ)
    (fhat : Fin T → S → ℝ) (hfhat : ∀ t, fhat t ∈ convexHull ℝ F)
    (p : Fin T → S → ℝ)
    (hp_nonneg : ∀ t π, 0 ≤ p t π) (hp_sum : ∀ t, ∑ π, p t π = 1)
    (hp_min : ∀ t, ∀ f ∈ F,
      ∑ π, p t π * (f (piStar f) - f π - γ * (f π - fhat t π) ^ 2) ≤ decGf F piStar γ (fhat t))
    (EstSq : ℝ) (hOracle : OracleGuarantee T fhat fstar p EstSq) :
    regret fstar (piStar fstar) T p ≤ dec F piStar γ * T + γ * EstSq := by
  have hround : ∀ t : Fin T, fstar (piStar fstar) - ∑ π, p t π * fstar π
      ≤ dec F piStar γ + γ * ∑ π, p t π * (fhat t π - fstar π) ^ 2 := by
    intro t
    have : Nonempty S := by
      rcases isEmpty_or_nonempty S with h | h
      · have := hp_sum t
        simp at this
      · exact h
    have hmin := hp_min t fstar hfstar
    have hdec : decGf F piStar γ (fhat t) ≤ dec F piStar γ := by
      unfold dec
      refine le_csSup ⟨(2 * (Fintype.card S : ℝ) + 1) / (2 * γ), ?_⟩ ⟨fhat t, hfhat t, rfl⟩
      rintro _ ⟨g, _, rfl⟩
      exact aux_e2d_decGf_le F piStar γ hγ g
    have hid : ∑ π, p t π * (fstar (piStar fstar) - fstar π - γ * (fstar π - fhat t π) ^ 2)
          + γ * ∑ π, p t π * (fhat t π - fstar π) ^ 2
        = fstar (piStar fstar) * ∑ π, p t π - ∑ π, p t π * fstar π := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun π _ => ?_
      ring
    rw [hp_sum t, mul_one] at hid
    linarith
  unfold regret
  unfold OracleGuarantee at hOracle
  calc ∑ t : Fin T, (fstar (piStar fstar) - ∑ π, p t π * fstar π)
      ≤ ∑ t : Fin T, (dec F piStar γ + γ * ∑ π, p t π * (fhat t π - fstar π) ^ 2) :=
        Finset.sum_le_sum fun t _ => hround t
    _ = dec F piStar γ * T + γ * ∑ t : Fin T, ∑ π, p t π * (fhat t π - fstar π) ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, ← Finset.mul_sum]
        ring
    _ ≤ dec F piStar γ * T + γ * EstSq := by
        have := mul_le_mul_of_nonneg_left hOracle hγ.le
        linarith
