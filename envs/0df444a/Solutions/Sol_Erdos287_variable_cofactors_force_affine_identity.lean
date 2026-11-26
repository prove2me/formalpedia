-- Prove2me | solution 1 for Erdos287.variable_cofactors_force_affine_identity
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T19:26:44.511955+00:00
-- url     : https://prove2.me/submissions/448e0657-cae8-44c3-b962-c2408d25859f

import Mathlib

open Finset

set_option autoImplicit false

private theorem unit_sign (e : ℤ) (he : |e| = 1) : e = 1 ∨ e = -1 := by
  have h₁ := le_abs_self e
  have h₂ := neg_le_abs e
  have hn : e ≠ 0 := fun hz => by simp [hz] at he
  rw [he] at h₁ h₂
  omega

private theorem adjacent_coprime (c d : ℕ) (p q : ℤ) (h : |(c : ℤ) * p - (d : ℤ) * q| = 1) :
    c.Coprime d := by
  apply Nat.isCoprime_iff_coprime.mp
  rcases unit_sign _ h with h₁ | h₁
  · exact ⟨p, -q, by linear_combination h₁⟩
  · exact ⟨-p, q, by linear_combination -h₁⟩

private theorem abs_three (x y z : ℤ) : |x - y + z| ≤ |x| + |y| + |z| := by
  have h : |x - y| ≤ |x| + |y| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le x (-y)
  exact (abs_add_le (x - y) z).trans (add_le_add h le_rfl)

private theorem same_cofactors (B c₁ d₁ c₂ d₂ : ℕ) (p₁ q₁ p₂ q₂ : ℤ)
    (hc₁ : 0 < c₁) (h₁ : c₁ ≤ B) (h₂ : c₂ ≤ B) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (he₁ : |(c₁ : ℤ) * p₁ - (d₁ : ℤ) * q₁| = 1)
    (he₂ : |(c₂ : ℤ) * p₂ - (d₂ : ℤ) * q₂| = 1)
    (hgap : (B : ℤ) ^ 2 * |p₁ * q₂ - p₂ * q₁| + (B : ℤ) * (q₁ + q₂) < q₁ * q₂) :
    c₁ = c₂ ∧ d₁ = d₂ := by
  let e₁ := (c₁ : ℤ) * p₁ - (d₁ : ℤ) * q₁
  let e₂ := (c₂ : ℤ) * p₂ - (d₂ : ℤ) * q₂
  let Δ := (c₂ : ℤ) * d₁ - (c₁ : ℤ) * d₂
  have hdet : Δ * (q₁ * q₂) =
      (c₁ : ℤ) * c₂ * (p₁ * q₂ - p₂ * q₁) - (c₂ : ℤ) * e₁ * q₂ + (c₁ : ℤ) * e₂ * q₁ := by
    dsimp [Δ, e₁, e₂]
    ring
  change |e₁| = 1 at he₁
  change |e₂| = 1 at he₂
  have hc₁' : (0 : ℤ) ≤ c₁ := by positivity
  have hc₂' : (0 : ℤ) ≤ c₂ := by positivity
  have h₁' : (c₁ : ℤ) ≤ B := by exact_mod_cast h₁
  have h₂' : (c₂ : ℤ) ≤ B := by exact_mod_cast h₂
  have hB : (0 : ℤ) ≤ B := by positivity
  have habs : |Δ * (q₁ * q₂)| ≤
      (B : ℤ) ^ 2 * |p₁ * q₂ - p₂ * q₁| + (B : ℤ) * (q₁ + q₂) := by
    calc
      _ ≤ |(c₁ : ℤ) * c₂ * (p₁ * q₂ - p₂ * q₁)| + |(c₂ : ℤ) * e₁ * q₂| + |(c₁ : ℤ) * e₂ * q₁| := by
        rw [hdet]
        exact abs_three _ _ _
      _ = (c₁ : ℤ) * c₂ * |p₁ * q₂ - p₂ * q₁| + (c₂ : ℤ) * q₂ + (c₁ : ℤ) * q₁ := by
        simp only [abs_mul, abs_of_nonneg hc₁', abs_of_nonneg hc₂', he₁, he₂, mul_one,
          abs_of_pos hq₁, abs_of_pos hq₂]
      _ ≤ (B : ℤ) * B * |p₁ * q₂ - p₂ * q₁| + (B : ℤ) * q₂ + (B : ℤ) * q₁ :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul h₁' h₂' hc₂' hB) (abs_nonneg _))
          (mul_le_mul_of_nonneg_right h₂' hq₂.le)) (mul_le_mul_of_nonneg_right h₁' hq₁.le)
      _ = _ := by ring
  have hz : Δ = 0 := by
    by_contra hn
    have hh : q₁ * q₂ ≤ |Δ * (q₁ * q₂)| := by
      simpa only [abs_mul, abs_of_pos (mul_pos hq₁ hq₂), one_mul] using
        mul_le_mul_of_nonneg_right (Int.one_le_abs hn) (mul_nonneg hq₁.le hq₂.le)
    exact hgap.not_ge (hh.trans habs)
  have heq : c₂ * d₁ = c₁ * d₂ := by
    exact_mod_cast (sub_eq_zero.mp hz)
  have hcop₁ := adjacent_coprime c₁ d₁ p₁ q₁ he₁
  have hcop₂ := adjacent_coprime c₂ d₂ p₂ q₂ he₂
  have hd₁ : c₁ ∣ c₂ := hcop₁.dvd_of_dvd_mul_right (heq.symm ▸ dvd_mul_right c₁ d₂)
  have hd₂ : c₂ ∣ c₁ := hcop₂.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right c₂ d₁)
  have hc : c₁ = c₂ := Nat.dvd_antisymm hd₁ hd₂
  exact ⟨hc, Nat.eq_of_mul_eq_mul_left hc₁ (by simpa only [← hc] using heq)⟩

/-- In a parameter window with small variation of the affine value ratio,
three adjacent-multiple witnesses give a single affine identity, even when
both cofactors may vary with the parameter. -/
theorem solution (T : Finset ℤ) (a b r s Y H : ℤ) (B : ℕ)
    (hY : 2 * (B : ℤ) < Y)
    (hq : ∀ t ∈ T, Y ≤ r * t + s)
    (hwidth : ∀ t ∈ T, ∀ u ∈ T, |t - u| ≤ H)
    (hgap : (B : ℤ) ^ 2 * |a * s - b * r| * H < Y * (Y - 2 * (B : ℤ)))
    (hcert : ∀ t ∈ T, ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c ≤ B ∧ d ≤ B ∧
      |(c : ℤ) * (a * t + b) - (d : ℤ) * (r * t + s)| = 1) :
    T.card ≤ 2 ∨ ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ c ≤ B ∧ d ≤ B ∧
      (c : ℤ) * a = (d : ℤ) * r ∧ |(c : ℤ) * b - (d : ℤ) * s| = 1 := by
  classical
  by_cases hcard : T.card ≤ 2
  · exact Or.inl hcard
  obtain ⟨u, hu⟩ := card_pos.mp (by omega : 0 < T.card)
  choose! c d hc hd hcb hdb hadj using hcert
  have hY₀ : 0 < Y := by
    have hB : (0 : ℤ) ≤ B := by positivity
    omega
  have hsame (t : ℤ) (ht : t ∈ T) : c t = c u ∧ d t = d u := by
    have hdet : (a * t + b) * (r * u + s) - (a * u + b) * (r * t + s) = (a * s - b * r) * (t - u) := by ring
    have hdiff : (B : ℤ) ^ 2 * |(a * t + b) * (r * u + s) - (a * u + b) * (r * t + s)| ≤
        (B : ℤ) ^ 2 * |a * s - b * r| * H := by
      rw [hdet, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (hwidth t ht u hu) (by positivity)
    have htY := hq t ht
    have huY := hq u hu
    have hprod : (Y - (B : ℤ)) * (Y - (B : ℤ)) ≤ (r * t + s - (B : ℤ)) * (r * u + s - (B : ℤ)) :=
      mul_le_mul (by omega) (by omega) (by omega) (by omega)
    have hroom : Y * (Y - 2 * (B : ℤ)) + (B : ℤ) * (r * t + s + (r * u + s)) ≤
        (r * t + s) * (r * u + s) := by linear_combination hprod
    have hgap' : (B : ℤ) ^ 2 * |(a * t + b) * (r * u + s) - (a * u + b) * (r * t + s)| +
        (B : ℤ) * (r * t + s + (r * u + s)) < (r * t + s) * (r * u + s) := by
      linarith only [hdiff.trans_lt hgap, hroom]
    exact same_cofactors B (c t) (d t) (c u) (d u) _ _ _ _ (hc t ht) (hcb t ht) (hcb u hu)
      (hY₀.trans_le htY) (hY₀.trans_le huY) (hadj t ht) (hadj u hu) hgap'
  let value (t : ℤ) := (c u : ℤ) * (a * t + b) - (d u : ℤ) * (r * t + s)
  have hv (t : ℤ) (ht : t ∈ T) : |value t| = 1 := by
    obtain ⟨h₁, h₂⟩ := hsame t ht
    simpa only [value, h₁, h₂] using hadj t ht
  have hline : (c u : ℤ) * a = (d u : ℤ) * r := by
    by_contra hdif
    have hcount : T.card ≤ ({-1, 1} : Finset ℤ).card := by
      apply card_le_card_of_injOn value
      · intro t ht
        rcases unit_sign _ (hv t ht) with h | h <;> simp [h]
      · intro t _ v _ ht
        have hp : ((c u : ℤ) * a - (d u : ℤ) * r) * (t - v) = 0 := by
          dsimp only [value] at ht
          linear_combination ht
        exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hdif))
    exact hcard (hcount.trans (by decide))
  right
  refine ⟨c u, d u, hc u hu, hd u hu, hcb u hu, hdb u hu, hline, ?_⟩
  have hconst : value u = (c u : ℤ) * b - (d u : ℤ) * s := by
    dsimp only [value]
    linear_combination u * hline
  exact hconst ▸ hv u hu

