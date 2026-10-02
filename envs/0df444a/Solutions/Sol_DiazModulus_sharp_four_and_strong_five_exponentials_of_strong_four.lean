-- Prove2me | solution 1 for DiazModulus.sharp_four_and_strong_five_exponentials_of_strong_four
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T14:42:36.050677+00:00
-- url     : https://prove2.me/submissions/1414f4b9-136a-4a12-b60c-78143dfdcd9b

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

/-!
# Strong four exponentials implies the sharp four and the strong five exponentials conjectures

With Baker's theorem `hB` in its two-logarithm inhomogeneous form, and Hermite–Lindemann.
Write `ℓᵢⱼ := xᵢyⱼ − βᵢⱼ`, so that each `exp ℓᵢⱼ` is algebraic and `xᵢyⱼ = ℓᵢⱼ + βᵢⱼ ∈ ℒ̃`.

1. The strong four exponentials conjecture, applied to `![x₁, x₂]` and `![y₁, y₂]`, makes one of
   the two pairs `Q̄`-dependent: `x₂ = c x₁` or `y₂ = d y₁`, the multiplier being algebraic and,
   by `ℚ`-independence, not rational.
2. If `x₂ = c x₁`, then `ℓ₂ⱼ − c ℓ₁ⱼ = c β₁ⱼ − β₂ⱼ` is algebraic for each `j`. Baker's theorem with
   coefficients `(−c, 1)` forces a rational relation `p ℓ₁ⱼ + q ℓ₂ⱼ = 0`, `(p, q) ≠ 0`. As `c ∉ ℚ`,
   `p + q c ≠ 0`, so `ℓ₁ⱼ` and `ℓ₂ⱼ` are algebraic, hence `0` by Hermite–Lindemann.
   If `y₂ = d y₁`, the same argument runs along the rows. This is the sharp four exponentials
   statement.
3. Strong five from sharp four: `x₂/x₁ = α₂₁/α₁₁` is algebraic, so `η x₂/x₁ − β` is an algebraic
   logarithm of an algebraic number, hence `0` by Hermite–Lindemann: `η x₂ = β x₁`.
-/

open Complex ComplexConjugate

namespace DiazSharpFourOfStrongFour

open DiazModulus

/-- Hermite–Lindemann in the form used here: an algebraic logarithm of an algebraic number
is `0`. -/
theorem eq_zero_of_alg {l : ℂ} (hl : l ∈ Qbar) (he : IsAlgebraic ℚ (Complex.exp l)) :
    l = 0 := by
  by_contra h
  exact hermite_lindemann_holds l h (mem_Qbar_iff.mp hl) he

theorem ratCast_mem_Qbar (r : ℚ) : (r : ℂ) ∈ Qbar := SubfieldClass.ratCast_mem Qbar r

/-- `x y ∈ ℒ̃` as soon as `α` is algebraic and `exp (x y − α)` is algebraic. -/
theorem mul_mem_logAlgTilde {x y α : ℂ} (hα : α ∈ Qbar)
    (he : IsAlgebraic ℚ (Complex.exp (x * y - α))) : x * y ∈ LogAlgTilde := by
  have h1 : (1 : ℂ) ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert _ _)
  have hlog : x * y - α ∈ LogAlg := he
  have hl : x * y - α ∈ LogAlgTilde := Submodule.subset_span (Set.mem_insert_of_mem _ hlog)
  have hα' : α ∈ LogAlgTilde := by
    have := LogAlgTilde.smul_mem (⟨α, hα⟩ : Qbar) h1
    simpa [Subfield.smul_def] using this
  simpa using LogAlgTilde.add_mem hl hα'

/-- A `ℚ`-independent pair which is `Q̄`-dependent: the second entry is an algebraic,
non-rational multiple of the first. -/
theorem dep_pair {a b : ℂ} (hQ : LinearIndependent ℚ ![a, b])
    (hQbar : ¬ LinearIndependent (↥Qbar) ![a, b]) :
    ∃ c : ℂ, c ∈ Qbar ∧ (∀ r : ℚ, c ≠ r) ∧ b = c * a := by
  rw [LinearIndependent.pair_iff] at hQ hQbar
  obtain ⟨s, t, hst, hne⟩ : ∃ s t : ↥Qbar, s • a + t • b = 0 ∧ ¬(s = 0 ∧ t = 0) := by
    by_contra hcon
    exact hQbar fun s t hst => by_contra fun hne => hcon ⟨s, t, hst, hne⟩
  have hst' : (s : ℂ) * a + (t : ℂ) * b = 0 := by
    simpa [Subfield.smul_def, smul_eq_mul] using hst
  have ha : a ≠ 0 := by
    intro ha
    have := hQ 1 0 (by simp [ha])
    exact one_ne_zero this.1
  have ht : (t : ℂ) ≠ 0 := by
    intro ht
    rw [ht, zero_mul, add_zero] at hst'
    have hs : (s : ℂ) = 0 := (mul_eq_zero.mp hst').resolve_right ha
    exact hne ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hb : b = -(s : ℂ) / t * a := by
    rw [div_mul_eq_mul_div, eq_div_iff ht]
    linear_combination hst'
  refine ⟨-(s : ℂ) / t, Qbar.div_mem (Qbar.neg_mem s.2) t.2, ?_, hb⟩
  intro r hr
  have := hQ r (-1) (by
    rw [Rat.smul_def, Rat.smul_def, hb, hr]
    push_cast
    ring)
  norm_num at this

/-- Two logarithms of algebraic numbers `l, l'` with `l' − c l` algebraic, for some algebraic
non-rational `c`, both vanish. Baker's theorem with coefficients `(−c, 1)` gives a rational
relation `p l + q l' = 0`, `(p, q) ≠ 0`; then `p + q c ≠ 0` makes `l` and `l'` algebraic, and
Hermite–Lindemann makes them `0`. -/
theorem both_zero
    (hB : ∀ x y a b : ℂ,
      IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
      (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
      IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
      Transcendental ℚ (a * x + b * y))
    {l l' c : ℂ} (hl : IsAlgebraic ℚ (Complex.exp l)) (hl' : IsAlgebraic ℚ (Complex.exp l'))
    (hc : c ∈ Qbar) (hcQ : ∀ r : ℚ, c ≠ r) (hA : l' - c * l ∈ Qbar) :
    l = 0 ∧ l' = 0 := by
  obtain ⟨p, q, hpq, hne⟩ :
      ∃ p q : ℚ, (p : ℂ) * l + (q : ℂ) * l' = 0 ∧ ¬(p = 0 ∧ q = 0) := by
    by_contra hcon
    refine hB l l' (-c) 1 hl hl' (fun p q hpq => by_contra fun hne => hcon ⟨p, q, hpq, hne⟩)
      (mem_Qbar_iff.mp (Qbar.neg_mem hc)) isAlgebraic_one (fun h => one_ne_zero h.2) ?_
    have e : -c * l + 1 * l' = l' - c * l := by ring
    rw [e, ← mem_Qbar_iff]
    exact hA
  have hD : (p : ℂ) + (q : ℂ) * c ≠ 0 := by
    intro hD
    by_cases hq : q = 0
    · have hp : p = 0 := by simpa [hq] using hD
      exact hne ⟨hp, hq⟩
    · have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      apply hcQ (-p / q)
      push_cast
      rw [eq_div_iff hqC]
      linear_combination hD
  have e1 : l = -(q : ℂ) * (l' - c * l) / ((p : ℂ) + (q : ℂ) * c) := by
    rw [eq_div_iff hD]
    linear_combination hpq
  have e2 : l' = (p : ℂ) * (l' - c * l) / ((p : ℂ) + (q : ℂ) * c) := by
    rw [eq_div_iff hD]
    linear_combination c * hpq
  have hDQ : (p : ℂ) + (q : ℂ) * c ∈ Qbar :=
    Qbar.add_mem (ratCast_mem_Qbar p) (Qbar.mul_mem (ratCast_mem_Qbar q) hc)
  refine ⟨eq_zero_of_alg ?_ hl, eq_zero_of_alg ?_ hl'⟩
  · rw [e1]
    exact Qbar.div_mem (Qbar.mul_mem (Qbar.neg_mem (ratCast_mem_Qbar q)) hA) hDQ
  · rw [e2]
    exact Qbar.div_mem (Qbar.mul_mem (ratCast_mem_Qbar p) hA) hDQ

/-- Steps 1–2: the sharp four exponentials statement. -/
theorem sharp_four (hS : StrongFourExponentials)
    (hB : ∀ x y a b : ℂ,
          IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
          (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
          IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
          Transcendental ℚ (a * x + b * y)) :
    ∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
        x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂ := by
  intro x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ hx hy ha₁₁ ha₁₂ ha₂₁ ha₂₂ h₁₁ h₁₂ h₂₁ h₂₂
  have q₁₁ := mem_Qbar_iff.mpr ha₁₁
  have q₁₂ := mem_Qbar_iff.mpr ha₁₂
  have q₂₁ := mem_Qbar_iff.mpr ha₂₁
  have q₂₂ := mem_Qbar_iff.mpr ha₂₂
  -- the strong four exponentials conjecture: one of the two pairs is `Q̄`-dependent
  have hdep : ¬ LinearIndependent (↥Qbar) ![x₁, x₂] ∨ ¬ LinearIndependent (↥Qbar) ![y₁, y₂] := by
    by_contra h
    rw [not_or, not_not, not_not] at h
    exact hS x₁ x₂ y₁ y₂ h.1 h.2 ⟨mul_mem_logAlgTilde q₁₁ h₁₁, mul_mem_logAlgTilde q₁₂ h₁₂,
      mul_mem_logAlgTilde q₂₁ h₂₁, mul_mem_logAlgTilde q₂₂ h₂₂⟩
  -- the four logarithms `ℓᵢⱼ = xᵢyⱼ − αᵢⱼ` vanish
  have hall : x₁ * y₁ - β₁₁ = 0 ∧ x₁ * y₂ - β₁₂ = 0 ∧ x₂ * y₁ - β₂₁ = 0 ∧
      x₂ * y₂ - β₂₂ = 0 := by
    rcases hdep with h | h
    · obtain ⟨c, hc, hcQ, hx₂⟩ := dep_pair hx h
      have e1 := both_zero hB h₁₁ h₂₁ hc hcQ (by
        have e : x₂ * y₁ - β₂₁ - c * (x₁ * y₁ - β₁₁) = c * β₁₁ - β₂₁ := by
          linear_combination y₁ * hx₂
        rw [e]
        exact Qbar.sub_mem (Qbar.mul_mem hc q₁₁) q₂₁)
      have e2 := both_zero hB h₁₂ h₂₂ hc hcQ (by
        have e : x₂ * y₂ - β₂₂ - c * (x₁ * y₂ - β₁₂) = c * β₁₂ - β₂₂ := by
          linear_combination y₂ * hx₂
        rw [e]
        exact Qbar.sub_mem (Qbar.mul_mem hc q₁₂) q₂₂)
      exact ⟨e1.1, e2.1, e1.2, e2.2⟩
    · obtain ⟨d, hd, hdQ, hy₂⟩ := dep_pair hy h
      have e1 := both_zero hB h₁₁ h₁₂ hd hdQ (by
        have e : x₁ * y₂ - β₁₂ - d * (x₁ * y₁ - β₁₁) = d * β₁₁ - β₁₂ := by
          linear_combination x₁ * hy₂
        rw [e]
        exact Qbar.sub_mem (Qbar.mul_mem hd q₁₁) q₁₂)
      have e2 := both_zero hB h₂₁ h₂₂ hd hdQ (by
        have e : x₂ * y₂ - β₂₂ - d * (x₂ * y₁ - β₂₁) = d * β₂₁ - β₂₂ := by
          linear_combination x₂ * hy₂
        rw [e]
        exact Qbar.sub_mem (Qbar.mul_mem hd q₂₁) q₂₂)
      exact ⟨e1.1, e1.2, e2.1, e2.2⟩
  obtain ⟨e₁₁, e₁₂, e₂₁, e₂₂⟩ := hall
  exact ⟨sub_eq_zero.mp e₁₁, sub_eq_zero.mp e₁₂, sub_eq_zero.mp e₂₁, sub_eq_zero.mp e₂₂⟩

/-- Step 3: the strong five exponentials statement follows from the sharp four exponentials one. -/
theorem five_of_four
    (h4 : ∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
          LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
          IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
          IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
          IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
          x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂) :
    ∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ η → η ≠ 0 →
        IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
        IsAlgebraic ℚ β →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
        IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
        x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁ := by
  intro x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β hx hy hη _hη0 ha₁₁ ha₁₂ ha₂₁ ha₂₂ hβ
    h₁₁ h₁₂ h₂₁ h₂₂ h5
  have q₁₁ := mem_Qbar_iff.mpr ha₁₁
  have q₂₁ := mem_Qbar_iff.mpr ha₂₁
  obtain ⟨e₁₁, e₁₂, e₂₁, e₂₂⟩ :=
    h4 x₁ x₂ y₁ y₂ α₁₁ α₁₂ α₂₁ α₂₂ hx hy ha₁₁ ha₁₂ ha₂₁ ha₂₂ h₁₁ h₁₂ h₂₁ h₂₂
  -- the fifth number: `x₂ / x₁ = α₂₁ / α₁₁` is algebraic
  have hx₁ : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hy₁ : y₁ ≠ 0 := by simpa using hy.ne_zero 0
  have hα₁₁ : α₁₁ ≠ 0 := by
    rw [← e₁₁]
    exact mul_ne_zero hx₁ hy₁
  have hq : η * x₂ / x₁ = η * α₂₁ / α₁₁ := by
    rw [div_eq_div_iff hx₁ hα₁₁]
    linear_combination (-η * x₂) * e₁₁ + (η * x₁) * e₂₁
  have h5' : η * x₂ / x₁ - β = 0 := by
    refine eq_zero_of_alg ?_ h5
    rw [hq]
    exact Qbar.sub_mem (Qbar.div_mem (Qbar.mul_mem (mem_Qbar_iff.mpr hη) q₂₁) q₁₁)
      (mem_Qbar_iff.mpr hβ)
  have h5'' := sub_eq_zero.mp h5'
  rw [div_eq_iff hx₁] at h5''
  exact ⟨e₁₁, e₁₂, e₂₁, e₂₂, h5''⟩

end DiazSharpFourOfStrongFour

open DiazModulus DiazSharpFourOfStrongFour in
theorem solution (hS : StrongFourExponentials)
    (hB : ∀ x y a b : ℂ,
          IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
          (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
          IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
          Transcendental ℚ (a * x + b * y)) :
    (∀ x₁ x₂ y₁ y₂ β₁₁ β₁₂ β₂₁ β₂₂ : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ β₁₁ → IsAlgebraic ℚ β₁₂ → IsAlgebraic ℚ β₂₁ → IsAlgebraic ℚ β₂₂ →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - β₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - β₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - β₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - β₂₂)) →
        x₁ * y₁ = β₁₁ ∧ x₁ * y₂ = β₁₂ ∧ x₂ * y₁ = β₂₁ ∧ x₂ * y₂ = β₂₂) ∧
    (∀ x₁ x₂ y₁ y₂ η α₁₁ α₁₂ α₂₁ α₂₂ β : ℂ,
        LinearIndependent ℚ ![x₁, x₂] → LinearIndependent ℚ ![y₁, y₂] →
        IsAlgebraic ℚ η → η ≠ 0 →
        IsAlgebraic ℚ α₁₁ → IsAlgebraic ℚ α₁₂ → IsAlgebraic ℚ α₂₁ → IsAlgebraic ℚ α₂₂ →
        IsAlgebraic ℚ β →
        IsAlgebraic ℚ (Complex.exp (x₁ * y₁ - α₁₁)) → IsAlgebraic ℚ (Complex.exp (x₁ * y₂ - α₁₂)) →
        IsAlgebraic ℚ (Complex.exp (x₂ * y₁ - α₂₁)) → IsAlgebraic ℚ (Complex.exp (x₂ * y₂ - α₂₂)) →
        IsAlgebraic ℚ (Complex.exp (η * x₂ / x₁ - β)) →
        x₁ * y₁ = α₁₁ ∧ x₁ * y₂ = α₁₂ ∧ x₂ * y₁ = α₂₁ ∧ x₂ * y₂ = α₂₂ ∧ η * x₂ = β * x₁) :=
  ⟨sharp_four hS hB, five_of_four (sharp_four hS hB)⟩
