-- Prove2me | solution 1 for DiazModulus.involution_pencil_space_excludes_squares_and_reciprocals
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:28:19.566682+00:00
-- url     : https://prove2.me/submissions/7a74631c-79be-4c4f-8c66-eb6241bb4c28

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # An involution pencil space contains no `u²`, `u⁻²`, `(u − b)⁻¹`

`W = Q̄ + Q̄u + Q̄u⁻¹ + Σᵢ Q̄ q₁(u)ⁱ q₂(u)³⁻ⁱ / (u l₁(u) l₂(u))`, with `Λ = span(q₁, q₂)` a
base-point-free pencil of quadratics and `l₁, l₂ ∈ Λ` non-zero. Write `qⱼ` by coefficients and let
`A, B, Γ` be the Plücker coordinates, `D = A² + BΓ` (the resultant, non-zero by coprimality:
`D = a₂² q₂(x₁) q₂(x₂)` over the roots `xᵢ` of `q₁`). The involution of the pencil is
`τ(X) = (AX + B)/(ΓX − A)`; with `n = Γu − A`, `y = τ(u)` one has `n² q(y) = D q(u)` for `q ∈ Λ`.
Clearing denominators in a membership gives `N(u) L(u) = (u − β)(Q(u) L(u) + S(u))` (`N(β) ≠ 0`;
`u⁻²`: `N = 1, β = 0`; `(u − b)⁻¹`: `N = X, β = b`; `u²`: the `u⁻²` case for `1/u` and the
reversed quadratics). Since `u` is transcendental this is a polynomial identity, so it also holds
at `y`. Multiplying by `n⁷` and eliminating `S` gives a polynomial `T` over `Q̄` with `T(u) = 0`.
Evaluating `T` at `β` shows that `β` is a fixed point of `τ`; dividing by `X − β` and evaluating
once more gives `2 D ε N(β) = 0` with `ε² = D`, so `D = 0`, a contradiction.
-/

namespace R9_invis

open DiazModulus Polynomial

theorem aeval_eq_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (h : aeval u P = 0) :
    P = 0 := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact transcendental_iff.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
    fun h' => hu (mem_Qbar_iff.2 h')) P h

theorem transfer {u : ℂ} (hu : u ∉ Qbar) (P : (↥Qbar)[X]) (h : aeval u P = 0) (z : ℂ) :
    aeval z P = 0 := by
  rw [aeval_eq_zero hu h, map_zero]

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

/-- Value of the quadratic with coefficients `x₀, x₁, x₂`. -/
def qv (x₀ x₁ x₂ : ↥Qbar) (z : ℂ) : ℂ := (x₀ : ℂ) + x₁ * z + x₂ * z ^ 2

/-- `l₁ l₂` for `lᵢ = sᵢ q₁ + tᵢ q₂`, in terms of the values `x₁, x₂` of `q₁, q₂`. -/
def Lf (s₁ t₁ s₂ t₂ : ↥Qbar) (x₁ x₂ : ℂ) : ℂ :=
  ((s₁ : ℂ) * x₁ + t₁ * x₂) * ((s₂ : ℂ) * x₁ + t₂ * x₂)

/-- An element of `Sym³ Λ`, in terms of the values `x₁, x₂` of `q₁, q₂`. -/
def Sf (d₀ d₁ d₂ d₃ : ↥Qbar) (x₁ x₂ : ℂ) : ℂ :=
  (d₀ : ℂ) * x₂ ^ 3 + d₁ * x₁ * x₂ ^ 2 + d₂ * x₁ ^ 2 * x₂ + d₃ * x₁ ^ 3

/-- The resultant of two quadratics, through the Plücker coordinates. -/
def Dc (a₀ a₁ a₂ b₀ b₁ b₂ : ℂ) : ℂ :=
  (a₀ * b₂ - a₂ * b₀) ^ 2 + (a₀ * b₁ - a₁ * b₀) * (a₂ * b₁ - a₁ * b₂)

theorem quad_eval {q : (↥Qbar)[X]} (hq : q.natDegree ≤ 2) (z : ℂ) :
    aeval z q = qv (q.coeff 0) (q.coeff 1) (q.coeff 2) z := by
  rw [aeval_eq_sum_range' (n := 3) (by omega)]
  simp [Finset.sum_range_succ, qv, Subfield.smul_def]

/-! ## The resultant is non-zero -/

theorem res_ne {a₀ a₁ a₂ b₀ b₁ b₂ : ↥Qbar} (ha : (a₂ : ℂ) ≠ 0)
    (h : ∀ z, qv a₀ a₁ a₂ z = 0 → qv b₀ b₁ b₂ z ≠ 0) : Dc a₀ a₁ a₂ b₀ b₁ b₂ ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_quadratic_eq_zero (b := (a₁ : ℂ)) (c := (a₀ : ℂ)) ha
    (IsAlgClosed.exists_eq_mul_self _)
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : ℂ, (a₂ : ℂ) * x₂ = -a₁ - a₂ * x :=
    ⟨-a₁ / a₂ - x, by field_simp⟩
  have h1 : qv a₀ a₁ a₂ x = 0 := by simp only [qv]; linear_combination hx
  have ha₀ : (a₀ : ℂ) = a₂ * x * x₂ := by simp only [qv] at h1; linear_combination h1 - x * hx₂
  have ha₁ : (a₁ : ℂ) = -a₂ * (x + x₂) := by linear_combination hx₂
  have h2 : qv a₀ a₁ a₂ x₂ = 0 := by simp only [qv]; linear_combination ha₀ + x₂ * ha₁
  have hkey : Dc a₀ a₁ a₂ b₀ b₁ b₂ = (a₂ : ℂ) ^ 2 * qv b₀ b₁ b₂ x * qv b₀ b₁ b₂ x₂ := by
    simp only [Dc, qv]; rw [ha₀, ha₁]; ring
  rw [hkey]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 ha) (h x h1)) (h x₂ h2)

/-! ## Algebra of the involution -/

theorem rel {u y A B Γ a₀ a₁ a₂ b₀ b₁ b₂ : ℂ} (hA : A = a₀ * b₂ - a₂ * b₀)
    (hB : B = a₀ * b₁ - a₁ * b₀) (hΓ : Γ = a₂ * b₁ - a₁ * b₂) (hy : (Γ * u - A) * y = A * u + B) :
    (Γ * u - A) ^ 2 * (a₀ + a₁ * y + a₂ * y ^ 2) = (A ^ 2 + B * Γ) * (a₀ + a₁ * u + a₂ * u ^ 2) := by
  have : (Γ * u - A) ^ 2 * (a₀ + a₁ * y + a₂ * y ^ 2) =
      a₀ * (Γ * u - A) ^ 2 + a₁ * (A * u + B) * (Γ * u - A) + a₂ * (A * u + B) ^ 2 := by
    linear_combination (a₁ * (Γ * u - A) + a₂ * ((Γ * u - A) * y + (A * u + B))) * hy
  rw [this]; subst hA hB hΓ; ring

/-- The membership identity at `y`, multiplied by `n⁷`. -/
theorem alg2 {n y Y β e₀ e₁ c₁ c₂ c₃ r₁ r₂ : ℂ} {s₁ t₁ s₂ t₂ d₀ d₁ d₂ d₃ : ↥Qbar}
    (hy : n * y = Y)
    (E : (e₀ + e₁ * y) * Lf s₁ t₁ s₂ t₂ r₁ r₂ =
      (y - β) * ((c₃ + c₁ * y + c₂ * y ^ 2) * Lf s₁ t₁ s₂ t₂ r₁ r₂ + Sf d₀ d₁ d₂ d₃ r₁ r₂)) :
    (e₀ * n + e₁ * Y) * n ^ 2 * Lf s₁ t₁ s₂ t₂ (n ^ 2 * r₁) (n ^ 2 * r₂) =
      (Y - β * n) * ((c₃ * n ^ 2 + c₁ * Y * n + c₂ * Y ^ 2) *
        Lf s₁ t₁ s₂ t₂ (n ^ 2 * r₁) (n ^ 2 * r₂) + Sf d₀ d₁ d₂ d₃ (n ^ 2 * r₁) (n ^ 2 * r₂)) := by
  subst hy; simp only [Lf, Sf] at *; linear_combination n ^ 7 * E

/-- Eliminating `S` between the identities at `u` and at `y`. -/
theorem alg {u n Y β e₀ e₁ c₁ c₂ c₃ D x₁ x₂ : ℂ} {s₁ t₁ s₂ t₂ d₀ d₁ d₂ d₃ : ↥Qbar}
    (E1 : (e₀ + e₁ * u) * Lf s₁ t₁ s₂ t₂ x₁ x₂ =
      (u - β) * ((c₃ + c₁ * u + c₂ * u ^ 2) * Lf s₁ t₁ s₂ t₂ x₁ x₂ + Sf d₀ d₁ d₂ d₃ x₁ x₂))
    (H2 : (e₀ * n + e₁ * Y) * n ^ 2 * Lf s₁ t₁ s₂ t₂ (D * x₁) (D * x₂) =
      (Y - β * n) * ((c₃ * n ^ 2 + c₁ * Y * n + c₂ * Y ^ 2) *
        Lf s₁ t₁ s₂ t₂ (D * x₁) (D * x₂) + Sf d₀ d₁ d₂ d₃ (D * x₁) (D * x₂))) :
    D ^ 2 * Lf s₁ t₁ s₂ t₂ x₁ x₂ * ((u - β) * (n ^ 2 * (e₀ * n + e₁ * Y) - (Y - β * n) *
      ((c₃ * n ^ 2 + c₁ * Y * n + c₂ * Y ^ 2) - D * (c₃ + c₁ * u + c₂ * u ^ 2))) -
      D * (Y - β * n) * (e₀ + e₁ * u)) = 0 := by
  simp only [Lf, Sf] at *
  linear_combination (u - β) * H2 - D ^ 3 * (Y - β * n) * E1

/-! ## The core contradiction -/

theorem core {u : ℂ} (hu : u ∉ Qbar)
    (a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ β e₀ e₁ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ↥Qbar)
    (hD : Dc a₀ a₁ a₂ b₀ b₁ b₂ ≠ 0)
    (hL : Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) ≠ 0) (hN : (e₀ : ℂ) + e₁ * β ≠ 0)
    (E1 : ((e₀ : ℂ) + e₁ * u) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      (u - β) * (((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u))) : False := by
  -- E1 is a polynomial identity over `Q̄`
  let qP : ↥Qbar → ↥Qbar → ↥Qbar → (↥Qbar)[X] := fun x₀ x₁ x₂ => C x₀ + C x₁ * X + C x₂ * X ^ 2
  let LP := (C s₁ * qP a₀ a₁ a₂ + C t₁ * qP b₀ b₁ b₂) * (C s₂ * qP a₀ a₁ a₂ + C t₂ * qP b₀ b₁ b₂)
  let SP := C d₀ * qP b₀ b₁ b₂ ^ 3 + C d₁ * qP a₀ a₁ a₂ * qP b₀ b₁ b₂ ^ 2 +
    C d₂ * qP a₀ a₁ a₂ ^ 2 * qP b₀ b₁ b₂ + C d₃ * qP a₀ a₁ a₂ ^ 3
  let P := (C e₀ + C e₁ * X) * LP - (X - C β) * ((C c₃ + C c₁ * X + C c₂ * X ^ 2) * LP + SP)
  have hPz : ∀ z : ℂ, aeval z P = ((e₀ : ℂ) + e₁ * z) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ z) (qv b₀ b₁ b₂ z) -
      (z - β) * (((c₃ : ℂ) + c₁ * z + c₂ * z ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ z) (qv b₀ b₁ b₂ z) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ z) (qv b₀ b₁ b₂ z)) := by
    intro z
    simp only [P, LP, SP, qP, map_mul, map_add, map_sub, map_pow, aeval_X, aeval_C, am, Lf, Sf, qv]
  have hP : aeval u P = 0 := by rw [hPz]; exact sub_eq_zero.2 E1
  -- the involution `τ(X) = (AX + B)/(ΓX − A)`
  obtain ⟨A, hA⟩ : ∃ A : ↥Qbar, (A : ℂ) = a₀ * b₂ - a₂ * b₀ := ⟨a₀ * b₂ - a₂ * b₀, by push_cast; ring⟩
  obtain ⟨B, hB⟩ : ∃ B : ↥Qbar, (B : ℂ) = a₀ * b₁ - a₁ * b₀ := ⟨a₀ * b₁ - a₁ * b₀, by push_cast; ring⟩
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ↥Qbar, (Γ : ℂ) = a₂ * b₁ - a₁ * b₂ := ⟨a₂ * b₁ - a₁ * b₂, by push_cast; ring⟩
  obtain ⟨D, hDd⟩ : ∃ D : ↥Qbar, (D : ℂ) = A ^ 2 + B * Γ := ⟨A ^ 2 + B * Γ, by push_cast; ring⟩
  have hD' : (D : ℂ) ≠ 0 := by rw [hDd, hA, hB, hΓ]; exact hD
  have hn : (Γ : ℂ) * u - A ≠ 0 := by
    intro h
    by_cases hΓ0 : (Γ : ℂ) = 0
    · have hA0 : (A : ℂ) = 0 := by linear_combination -h + u * hΓ0
      exact hD' (by rw [hDd, hA0, hΓ0]; ring)
    · exact hu (by
        have : u = A / Γ := by field_simp; linear_combination h
        rw [this]; exact div_mem A.2 Γ.2)
  obtain ⟨y, hy⟩ : ∃ y : ℂ, ((Γ : ℂ) * u - A) * y = A * u + B :=
    ⟨(A * u + B) / (Γ * u - A), mul_div_cancel₀ _ hn⟩
  have hR₁ : ((Γ : ℂ) * u - A) ^ 2 * qv a₀ a₁ a₂ y = D * qv a₀ a₁ a₂ u := by
    rw [hDd]; exact rel hA hB hΓ hy
  have hR₂ : ((Γ : ℂ) * u - A) ^ 2 * qv b₀ b₁ b₂ y = D * qv b₀ b₁ b₂ u := by
    have := rel (u := u) (y := y) (A := -A) (B := -B) (Γ := -Γ) (a₀ := b₀) (a₁ := b₁) (a₂ := b₂) (b₀ := a₀)
      (b₁ := a₁) (b₂ := a₂) (by rw [hA]; ring) (by rw [hB]; ring) (by rw [hΓ]; ring)
      (by linear_combination -hy)
    rw [hDd]; simp only [qv]; linear_combination this
  have E : ((e₀ : ℂ) + e₁ * y) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ y) (qv b₀ b₁ b₂ y) =
      (y - β) * (((c₃ : ℂ) + c₁ * y + c₂ * y ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ y) (qv b₀ b₁ b₂ y) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ y) (qv b₀ b₁ b₂ y)) := by
    have := hPz y; rw [transfer hu P hP y] at this; exact sub_eq_zero.1 this.symm
  have H2 := alg2 hy E
  rw [hR₁, hR₂] at H2
  have hT := alg E1 H2
  have hT0 := (mul_eq_zero.1 hT).resolve_left (mul_ne_zero (pow_ne_zero 2 hD') hL)
  -- `T(u) = 0` is a polynomial identity: evaluate at `β`
  let nP : (↥Qbar)[X] := C Γ * X - C A
  let YP : (↥Qbar)[X] := C A * X + C B
  let mP := YP - C β * nP
  let NP := C e₀ + C e₁ * X
  let UP := nP ^ 2 * (C e₀ * nP + C e₁ * YP) - mP * ((C c₃ * nP ^ 2 + C c₁ * YP * nP +
    C c₂ * YP ^ 2) - C D * (C c₃ + C c₁ * X + C c₂ * X ^ 2))
  have hUz : ∀ z : ℂ, aeval z UP = ((Γ : ℂ) * z - A) ^ 2 * (e₀ * (Γ * z - A) + e₁ * (A * z + B)) -
      (A * z + B - β * (Γ * z - A)) * ((c₃ * (Γ * z - A) ^ 2 + c₁ * (A * z + B) * (Γ * z - A) +
        c₂ * (A * z + B) ^ 2) - D * (c₃ + c₁ * z + c₂ * z ^ 2)) := by
    intro z
    simp only [UP, mP, nP, YP, map_mul, map_add, map_sub, map_pow, aeval_X, aeval_C, am]
  have hmz : ∀ z : ℂ, aeval z mP = (A : ℂ) * z + B - β * (Γ * z - A) := by
    intro z; simp only [mP, nP, YP, map_mul, map_add, map_sub, aeval_X, aeval_C, am]
  have hNz : ∀ z : ℂ, aeval z NP = (e₀ : ℂ) + e₁ * z := by
    intro z; simp only [NP, map_mul, map_add, aeval_X, aeval_C, am]
  have h1 := transfer hu ((X - C β) * UP - C D * mP * NP) (by
    simp only [map_mul, map_sub, aeval_X, aeval_C, am, hUz, hmz, hNz]
    linear_combination hT0) β
  simp only [map_mul, map_sub, aeval_X, aeval_C, am, hUz, hmz, hNz] at h1
  have hfix : (A : ℂ) * β + B - β * (Γ * β - A) = 0 := by
    have : (D : ℂ) * (((A : ℂ) * β + B - β * (Γ * β - A)) * (e₀ + e₁ * β)) = 0 := by
      linear_combination -h1
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hD')).resolve_right hN
  -- `β` is a fixed point; divide by `X − β` and evaluate again
  have hU : aeval u UP - D * ((A : ℂ) - β * Γ) * (e₀ + e₁ * u) = 0 := by
    have hub : u - β ≠ 0 := sub_ne_zero.2 (fun e => hu (e ▸ β.2))
    have : (u - β) * (aeval u UP - D * ((A : ℂ) - β * Γ) * (e₀ + e₁ * u)) = 0 := by
      rw [hUz]; linear_combination hT0 + (D * (e₀ + e₁ * u)) * hfix
    exact (mul_eq_zero.1 this).resolve_left hub
  have h2 := transfer hu (UP - C D * (C A - C β * C Γ) * NP) (by
    simp only [map_mul, map_sub, aeval_C, am, hNz]; exact hU) β
  simp only [map_mul, map_sub, aeval_C, am, hNz, hUz] at h2
  rw [hfix, zero_mul, sub_zero] at h2
  have hY : (A : ℂ) * β + B = -((A : ℂ) - β * Γ) * β := by linear_combination hfix
  have hε2 : ((A : ℂ) - β * Γ) ^ 2 = D := by rw [hDd]; linear_combination (-(Γ : ℂ)) * hfix
  have h4 : ((A : ℂ) - β * Γ) * (2 * D * (e₀ + e₁ * β)) = 0 := by
    linear_combination -h2 + ((Γ : ℂ) * β - A) ^ 2 * e₁ * hY -
      ((A : ℂ) - β * Γ) * (e₀ + e₁ * β) * hε2
  have hε : (A : ℂ) - β * Γ = 0 := (mul_eq_zero.1 h4).resolve_right
    (mul_ne_zero (mul_ne_zero two_ne_zero hD') hN)
  exact hD' (by rw [← hε2, hε]; ring)

/-! ## From memberships to identities -/

theorem memb {u t X₁ X₂ M₁ M₂ : ℂ} (hu0 : u ≠ 0) (hM₁ : M₁ ≠ 0) (hM₂ : M₂ ≠ 0)
    (h : t ∈ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        X₁ ^ (i : ℕ) * X₂ ^ (3 - (i : ℕ)) / (u * M₁ * M₂)))) :
    ∃ c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ↥Qbar, t * u * (M₁ * M₂) =
      ((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * (M₁ * M₂) +
        ((d₀ : ℂ) * X₂ ^ 3 + d₁ * X₁ * X₂ ^ 2 + d₂ * X₁ ^ 2 * X₂ + d₃ * X₁ ^ 3) := by
  rw [Submodule.span_union, Submodule.mem_sup] at h
  obtain ⟨x, hx, z, hz, rfl⟩ := h
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hx
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, rfl⟩ := Submodule.mem_span_singleton.1 hw₂
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hz
  refine ⟨c₁, c₂, c₃, d 0, d 1, d 2, d 3, ?_⟩
  simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul, mul_one]
  simp
  field_simp
  ring

theorem excl_inv_sub {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ β : ↥Qbar}
    (hβ : (β : ℂ) ≠ 0) (hD : Dc a₀ a₁ a₂ b₀ b₁ b₂ ≠ 0)
    (hL : Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) ≠ 0) {c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ↥Qbar}
    (hE : (u - β)⁻¹ * u * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      ((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u)) : False := by
  have hub : (u - β) * (u - β)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.2 fun e => hu (e ▸ β.2))
  exact core hu a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ β 0 1 c₁ c₂ c₃ d₀ d₁ d₂ d₃ hD hL (by simpa using hβ)
    (by push_cast; linear_combination (u - β) * hE -
      (u * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u)) * hub)

theorem excl_inv_sq {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ : ↥Qbar}
    (hD : Dc a₀ a₁ a₂ b₀ b₁ b₂ ≠ 0)
    (hL : Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) ≠ 0) {c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ↥Qbar}
    (hE : (u ^ 2)⁻¹ * u * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      ((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u)) : False := by
  have hu2 : u ^ 2 * (u ^ 2)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero 2 fun e => hu (e ▸ Subfield.zero_mem _))
  exact core hu a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ 0 1 0 c₁ c₂ c₃ d₀ d₁ d₂ d₃ hD hL (by simp)
    (by push_cast; linear_combination u * hE -
      Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) * hu2)

/-- `u²` is the `u⁻²` case for `1/u` and the reversed quadratics. -/
theorem excl_sq {u : ℂ} (hu : u ∉ Qbar) {a₀ a₁ a₂ b₀ b₁ b₂ s₁ t₁ s₂ t₂ : ↥Qbar}
    (hD : Dc a₀ a₁ a₂ b₀ b₁ b₂ ≠ 0)
    (hL : Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) ≠ 0) {c₁ c₂ c₃ d₀ d₁ d₂ d₃ : ↥Qbar}
    (hE : u ^ 2 * u * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      ((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) +
        Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u)) : False := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ Subfield.zero_mem _)
  have hv : u⁻¹ ∉ Qbar := fun h => hu (by simpa using Subfield.inv_mem _ h)
  have hrev : ∀ x₀ x₁ x₂ : ↥Qbar, qv x₀ x₁ x₂ u = u ^ 2 * qv x₂ x₁ x₀ u⁻¹ := by
    intro x₀ x₁ x₂; simp only [qv]; field_simp; ring
  have hLr : Lf s₁ t₁ s₂ t₂ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      u ^ 4 * Lf s₁ t₁ s₂ t₂ (qv a₂ a₁ a₀ u⁻¹) (qv b₂ b₁ b₀ u⁻¹) := by
    rw [hrev a₀, hrev b₀]; simp only [Lf]; ring
  have hSr : Sf d₀ d₁ d₂ d₃ (qv a₀ a₁ a₂ u) (qv b₀ b₁ b₂ u) =
      u ^ 6 * Sf d₀ d₁ d₂ d₃ (qv a₂ a₁ a₀ u⁻¹) (qv b₂ b₁ b₀ u⁻¹) := by
    rw [hrev a₀, hrev b₀]; simp only [Sf]; ring
  rw [hLr, hSr] at hE
  rw [hLr] at hL
  refine core hv a₂ a₁ a₀ b₂ b₁ b₀ s₁ t₁ s₂ t₂ 0 1 0 c₁ c₃ c₂ d₀ d₁ d₂ d₃
    (by convert hD using 1; simp only [Dc]; ring) (right_ne_zero_of_mul hL) (by simp) ?_
  generalize Lf s₁ t₁ s₂ t₂ (qv a₂ a₁ a₀ u⁻¹) (qv b₂ b₁ b₀ u⁻¹) = ℓ at hE ⊢
  generalize Sf d₀ d₁ d₂ d₃ (qv a₂ a₁ a₀ u⁻¹) (qv b₂ b₁ b₀ u⁻¹) = σ at hE ⊢
  have hE' : u ^ 3 * ℓ = ((c₃ : ℂ) + c₁ * u + c₂ * u ^ 2) * ℓ + u ^ 2 * σ :=
    mul_left_cancel₀ (pow_ne_zero 4 hu0) (by linear_combination hE)
  push_cast
  field_simp
  linear_combination hE'

end R9_invis

open DiazModulus R9_invis Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (q₁ q₂ l₁ l₂ : Polynomial ↥Qbar)
    (hq₁ : q₁.natDegree ≤ 2) (hq₂ : q₂.natDegree ≤ 2) (hdeg : q₁.natDegree = 2 ∨ q₂.natDegree = 2)
    (hcop : IsCoprime q₁ q₂)
    (hl₁ : l₁ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₁0 : l₁ ≠ 0)
    (hl₂ : l₂ ∈ Submodule.span ↥Qbar ({q₁, q₂} : Set (Polynomial ↥Qbar))) (hl₂0 : l₂ ≠ 0) :
    u ^ 2 ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) ∧
      (u ^ 2)⁻¹ ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) ∧
      ∀ b ∈ Qbar, b ≠ 0 → (u - b)⁻¹ ∉ Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪ Set.range (fun i : Fin 4 =>
        Polynomial.aeval u q₁ ^ (i : ℕ) * Polynomial.aeval u q₂ ^ (3 - (i : ℕ)) /
          (u * Polynomial.aeval u l₁ * Polynomial.aeval u l₂))) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Subfield.zero_mem _)
  have hM₁ : aeval u l₁ ≠ 0 := fun h => hl₁0 (aeval_eq_zero hu h)
  have hM₂ : aeval u l₂ ≠ 0 := fun h => hl₂0 (aeval_eq_zero hu h)
  obtain ⟨s₁, t₁, rfl⟩ := Submodule.mem_span_pair.1 hl₁
  obtain ⟨s₂, t₂, rfl⟩ := Submodule.mem_span_pair.1 hl₂
  have hl : ∀ s t : ↥Qbar, aeval u (s • q₁ + t • q₂) =
      (s : ℂ) * qv (q₁.coeff 0) (q₁.coeff 1) (q₁.coeff 2) u +
        t * qv (q₂.coeff 0) (q₂.coeff 1) (q₂.coeff 2) u := by
    intro s t
    rw [map_add, map_smul, map_smul, quad_eval hq₁, quad_eval hq₂]; rfl
  -- the resultant
  have hno : ∀ z : ℂ, qv (q₁.coeff 0) (q₁.coeff 1) (q₁.coeff 2) z = 0 →
      qv (q₂.coeff 0) (q₂.coeff 1) (q₂.coeff 2) z ≠ 0 := by
    intro z h1 h2
    obtain ⟨f, g, hfg⟩ := hcop
    have := congrArg (aeval z) hfg
    rw [map_add, map_mul, map_mul, map_one, quad_eval hq₁, quad_eval hq₂, h1, h2] at this
    simp at this
  have hc2 : ∀ q : (↥Qbar)[X], q.natDegree = 2 → (q.coeff 2 : ℂ) ≠ 0 := by
    intro q hq h
    have h' : q.coeff 2 = 0 := Subtype.ext h
    rw [← hq, coeff_natDegree, leadingCoeff_eq_zero] at h'
    subst h'; simp at hq
  have hD : Dc (q₁.coeff 0) (q₁.coeff 1) (q₁.coeff 2) (q₂.coeff 0) (q₂.coeff 1) (q₂.coeff 2) ≠ 0 := by
    rcases hdeg with h | h
    · exact res_ne (hc2 q₁ h) hno
    · have := res_ne (hc2 q₂ h) (fun z h2 h1 => hno z h1 h2)
      convert this using 1; simp only [Dc]; ring
  have hL : Lf s₁ t₁ s₂ t₂ (qv (q₁.coeff 0) (q₁.coeff 1) (q₁.coeff 2) u)
      (qv (q₂.coeff 0) (q₂.coeff 1) (q₂.coeff 2) u) ≠ 0 := by
    simp only [Lf]; rw [← hl, ← hl]; exact mul_ne_zero hM₁ hM₂
  refine ⟨fun h => ?_, fun h => ?_, fun b hb hb0 h => ?_⟩
  · obtain ⟨c₁, c₂, c₃, d₀, d₁, d₂, d₃, hE⟩ := memb hu0 hM₁ hM₂ h
    rw [hl, hl, quad_eval hq₁, quad_eval hq₂] at hE
    exact excl_sq hu hD hL hE
  · obtain ⟨c₁, c₂, c₃, d₀, d₁, d₂, d₃, hE⟩ := memb hu0 hM₁ hM₂ h
    rw [hl, hl, quad_eval hq₁, quad_eval hq₂] at hE
    exact excl_inv_sq hu hD hL hE
  · obtain ⟨c₁, c₂, c₃, d₀, d₁, d₂, d₃, hE⟩ := memb hu0 hM₁ hM₂ h
    rw [hl, hl, quad_eval hq₁, quad_eval hq₂] at hE
    exact excl_inv_sub (β := ⟨b, hb⟩) hu hb0 hD hL hE
