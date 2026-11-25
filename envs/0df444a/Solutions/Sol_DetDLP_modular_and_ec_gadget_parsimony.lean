-- Prove2me | solution 1 for DetDLP.modular_and_ec_gadget_parsimony
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:35.68413+00:00
-- url     : https://prove2.me/submissions/c72c2e40-8ca1-4889-9680-fac564f1a79f

import Mathlib

set_option autoImplicit false

theorem solution :
    (∀ (q x y z : ℕ) (γ : Bool) (ssum : ℕ),
       x < q → y < q → z < q →
       ((x + y = ssum ∧ z + (if γ then 1 else 0) * q = ssum) ↔
         (z = (x + y) % q ∧ γ = decide (q ≤ x + y) ∧ ssum = x + y))) ∧
    (∀ (q x y z θ u₁ u₂ : ℕ),
       x < q → y < q → z < q →
       ((x * y = u₁ ∧ θ * q = u₂ ∧ u₂ + z = u₁) ↔
         (z = (x * y) % q ∧ θ = (x * y) / q ∧ θ < q ∧ u₁ = x * y ∧ u₂ = ((x * y) / q) * q))) ∧
    (∀ (p : ℕ) [Fact p.Prime] (u : ZMod p) (ζ : Bool) (winv : ZMod p),
       (((if ζ then (1 : ZMod p) else 0) * u = 0 ∧
         (if ζ then (1 : ZMod p) else 0) * winv = 0 ∧
         (1 - (if ζ then (1 : ZMod p) else 0)) * (u * winv) =
           1 - (if ζ then (1 : ZMod p) else 0)) ↔
        (ζ = decide (u = 0) ∧ winv = u⁻¹))) ∧
    ((∀ (ι₁ ι₂ ζx ζy : Bool),
        let b : Bool → ℤ := fun x => if x then 1 else 0
        let σ₁ := b ι₁
        let σ₂ := (1 - b ι₁) * b ι₂
        let σ₃ := (1 - b ι₁) * (1 - b ι₂) * b ζx * b ζy
        let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
        let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
        (σ₁ = 0 ∨ σ₁ = 1) ∧ (σ₂ = 0 ∨ σ₂ = 1) ∧ (σ₃ = 0 ∨ σ₃ = 1) ∧
        (σ₄ = 0 ∨ σ₄ = 1) ∧ (σ₅ = 0 ∨ σ₅ = 1) ∧
        σ₁ + σ₂ + σ₃ + σ₄ + σ₅ = 1) ∧
     (∀ (p : ℕ) [Fact p.Prime], 2 < p →
        ∀ (aE bE x₁ y₁ x₂ y₂ lsl : ZMod p) (ι₁ ι₂ : Bool),
          y₁ ^ 2 = x₁ ^ 3 + aE * x₁ + bE →
          y₂ ^ 2 = x₂ ^ 3 + aE * x₂ + bE →
          let ζx := decide (x₂ - x₁ = 0)
          let ζy := decide (y₁ + y₂ = 0)
          let b : Bool → ZMod p := fun x => if x then 1 else 0
          let σ₄ := (1 - b ι₁) * (1 - b ι₂) * (1 - b ζx)
          let σ₅ := (1 - b ι₁) * (1 - b ι₂) * b ζx * (1 - b ζy)
          ((σ₄ * ((x₂ - x₁) * lsl - (y₂ - y₁)) = 0 ∧
            σ₅ * (2 * y₁ * lsl - (3 * x₁ ^ 2 + aE)) = 0 ∧
            (1 - σ₄ - σ₅) * lsl = 0) ↔
           lsl =
             if (!ι₁ && !ι₂ && !ζx) then (y₂ - y₁) * (x₂ - x₁)⁻¹
             else if (!ι₁ && !ι₂ && ζx && !ζy) then (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹
             else 0))) := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩⟩
  · -- Conjunct 1: Modular addition wrap-bit parsimony
    intro q x y z γ ssum hx hy hz
    constructor
    · rintro ⟨rfl, hsum⟩
      have hmod : z = (x + y) % q := by
        rw [← hsum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
      have hγ : γ = decide (q ≤ x + y) := by
        cases γ with
        | false =>
          rw [if_neg Bool.false_ne_true, zero_mul, add_zero] at hsum
          symm
          rw [decide_eq_false_iff_not]
          omega
        | true =>
          rw [if_pos rfl, one_mul] at hsum
          symm
          rw [decide_eq_true_eq]
          omega
      exact ⟨hmod, hγ, rfl⟩
    · rintro ⟨rfl, rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      by_cases hq : q ≤ x + y
      · rw [decide_eq_true hq, if_pos rfl, one_mul]
        have hdiv : (x + y) / q = 1 := by
          have h1 : 1 * q ≤ x + y := by omega
          have h2 : x + y < (1 + 1) * q := by omega
          exact Nat.div_eq_of_lt_le h1 h2
        have hdm := Nat.mod_add_div (x + y) q
        rw [hdiv, mul_one] at hdm
        exact hdm
      · rw [decide_eq_false hq, if_neg Bool.false_ne_true, zero_mul, add_zero]
        exact Nat.mod_eq_of_lt (by omega)
  · -- Conjunct 2: Euclidean modular multiplication parsimony
    intro q x y z θ u₁ u₂ hx hy hz
    have hq_pos : 0 < q := by omega
    constructor
    · rintro ⟨rfl, rfl, hsum⟩
      have hz_eq : z = (x * y) % q := by
        rw [← hsum, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hz]
      have hθ_eq : θ = (x * y) / q := by
        rw [← hsum, add_comm, Nat.add_mul_div_right _ _ hq_pos,
          Nat.div_eq_zero_iff.mpr (Or.inr hz), zero_add]
      have hθ_lt : θ < q := by
        by_contra hge
        have hq_le : q ≤ θ := Nat.le_of_not_lt hge
        have h1 : q * q ≤ θ * q := Nat.mul_le_mul_right q hq_le
        have h2 : x * y < q * q := Nat.mul_lt_mul'' hx hy
        omega
      refine ⟨hz_eq, hθ_eq, hθ_lt, rfl, ?_⟩
      rw [← hθ_eq]
    · rintro ⟨hz_eq, hθ_eq, _, rfl, rfl⟩
      refine ⟨rfl, by rw [hθ_eq], ?_⟩
      rw [hz_eq, mul_comm ((x * y) / q) q, Nat.div_add_mod]
  · -- Conjunct 3: Prime-field zero-indicator parsimony
    intro p _ u ζ winv
    cases ζ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, zero_mul, sub_zero, one_mul, true_and,
        false_eq_decide_iff]
      constructor
      · intro hmul
        have hu : u ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at hmul
          exact zero_ne_one hmul
        refine ⟨hu, ?_⟩
        calc winv = u⁻¹ * (u * winv) := (inv_mul_cancel_left₀ hu winv).symm
          _ = u⁻¹ := by rw [hmul, mul_one]
      · rintro ⟨hu, rfl⟩
        exact mul_inv_cancel₀ hu
    | true =>
      simp only [↓reduceIte, one_mul, sub_self, zero_mul, and_true, true_eq_decide_iff]
      constructor
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, inv_zero.symm⟩
      · rintro ⟨rfl, rfl⟩
        exact ⟨rfl, inv_zero⟩
  · -- Conjunct 4.1: 5-branch partition of unity
    intro ι₁ ι₂ ζx ζy
    cases ι₁ <;> cases ι₂ <;> cases ζx <;> cases ζy <;> decide
  · -- Conjunct 4.2: Short-Weierstrass gated slope uniqueness
    intro p _ _hp2 aE bE x₁ y₁ x₂ y₂ lsl ι₁ ι₂ heq1 heq2
    dsimp only
    cases ι₁ with
    | true =>
      simp
    | false =>
      cases ι₂ with
      | true =>
        simp
      | false =>
        by_cases hdx : x₂ - x₁ = 0
        · have hζx : decide (x₂ - x₁ = 0) = true := decide_eq_true hdx
          rw [hζx]
          by_cases hsy : y₁ + y₂ = 0
          · have hζy : decide (y₁ + y₂ = 0) = true := decide_eq_true hsy
            rw [hζy]
            simp
          · have hζy : decide (y₁ + y₂ = 0) = false := decide_eq_false hsy
            rw [hζy]
            simp only [Bool.false_eq_true, Bool.not_false, Bool.not_true, Bool.and_self,
              Bool.and_false, ↓reduceIte, sub_zero, one_mul, sub_self, mul_zero, zero_mul,
              true_and, and_true]
            have hx_eq : x₂ = x₁ := sub_eq_zero.mp hdx
            have hy_sq : y₁ ^ 2 = y₂ ^ 2 := by
              rw [heq1, heq2, hx_eq]
            have hfac : (y₁ - y₂) * (y₁ + y₂) = 0 := by linear_combination hy_sq
            have hy_eq : y₁ = y₂ :=
              sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_right hsy)
            have h2y_ne : 2 * y₁ ≠ 0 := by
              rw [two_mul]
              intro h0
              apply hsy
              rw [← hy_eq]
              exact h0
            constructor
            · intro hlin
              have hmul : 2 * y₁ * lsl = 3 * x₁ ^ 2 + aE := sub_eq_zero.mp hlin
              calc lsl = lsl * (2 * y₁) * (2 * y₁)⁻¹ := by
                    rw [mul_assoc, mul_inv_cancel₀ h2y_ne, mul_one]
                _ = (2 * y₁ * lsl) * (2 * y₁)⁻¹ := by rw [mul_comm lsl (2 * y₁)]
                _ = (3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹ := by rw [hmul]
            · rintro rfl
              have hmul : 2 * y₁ * ((3 * x₁ ^ 2 + aE) * (2 * y₁)⁻¹) = 3 * x₁ ^ 2 + aE := by
                rw [mul_comm (3 * x₁ ^ 2 + aE) _, mul_inv_cancel_left₀ h2y_ne]
              rw [hmul, sub_self]
        · have hζx : decide (x₂ - x₁ = 0) = false := decide_eq_false hdx
          rw [hζx]
          simp only [Bool.false_eq_true, Bool.not_false, Bool.and_self, ↓reduceIte, sub_zero,
            one_mul, mul_zero, zero_mul, sub_self, and_self, and_true]
          constructor
          · intro hlin
            have hmul : (x₂ - x₁) * lsl = y₂ - y₁ := sub_eq_zero.mp hlin
            calc lsl = lsl * (x₂ - x₁) * (x₂ - x₁)⁻¹ := by
                  rw [mul_assoc, mul_inv_cancel₀ hdx, mul_one]
              _ = ((x₂ - x₁) * lsl) * (x₂ - x₁)⁻¹ := by rw [mul_comm lsl _]
              _ = (y₂ - y₁) * (x₂ - x₁)⁻¹ := by rw [hmul]
          · rintro rfl
            have hmul : (x₂ - x₁) * ((y₂ - y₁) * (x₂ - x₁)⁻¹) = y₂ - y₁ := by
              rw [mul_comm (y₂ - y₁) _, mul_inv_cancel_left₀ hdx]
            rw [hmul, sub_self]
