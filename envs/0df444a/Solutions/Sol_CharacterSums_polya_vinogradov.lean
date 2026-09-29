-- Prove2me | solution 1 for CharacterSums.polya_vinogradov
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T02:25:42.053982+00:00
-- url     : https://prove2.me/submissions/786b6ef8-5334-4c42-acc4-d90e5446cc19

import Mathlib

set_option maxHeartbeats 1000000
set_option linter.all false

-- ==== upstream: Salt/LS/Defs.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, node L0.1: the frozen carriers `e` and `expSum`

Blueprint: `docs/blueprints/largesieve.md` (Rung 5 opener). This file freezes
the two carriers the whole track is built on:

* `e x = exp (2πi x)`, the additive character on `ℝ`;
* `expSum N a α = ∑ n < N, a n · e (n α)`, the exponential (trig) polynomial.

Together with the elementary trivia the analytic large sieve needs: `‖e x‖ = 1`,
1-periodicity, additivity, `e 0 = 1`, the conjugate identity
`conj (e x) = e (−x)`, and continuity of both `e` and `expSum` (the derivative
identities are deferred to W2). Continuity is registered with `@[fun_prop]` so
downstream integrability side goals discharge automatically — per the blueprint
docstring note, `expSum` is a finite sum of smooth terms and needs no
measurability nodes.
-/

namespace Salt.LS

open scoped BigOperators

/-- **L0.1 carrier.** The additive character `e(x) = exp(2πi·x)` on `ℝ`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- **L0.1 carrier.** The exponential polynomial `∑_{n<N} a n · e(nα)`. -/
noncomputable def expSum (N : ℕ) (a : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, a n * e (n * α)

/-- `e` has unit modulus: `‖e x‖ = 1`. -/
@[simp] lemma norm_e (x : ℝ) : ‖e x‖ = 1 := by
  have : e x = Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- `e 0 = 1`. -/
@[simp] lemma e_zero : e 0 = 1 := by
  unfold e; simp

/-- Additivity of `e`: `e (x + y) = e x * e y`. -/
lemma e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- `e 1 = 1`. -/
@[simp] lemma e_one : e 1 = 1 := by
  have : e 1 = Complex.exp (2 * (Real.pi : ℂ) * Complex.I) := by
    unfold e; congr 1; push_cast; ring
  rw [this, Complex.exp_two_pi_mul_I]

/-- `e` is 1-periodic: `e (x + 1) = e x`. -/
lemma e_add_one (x : ℝ) : e (x + 1) = e x := by
  rw [e_add, e_one, mul_one]

/-- The conjugate identity `conj (e x) = e (−x)`. -/
lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

/-- `e` is continuous. Registered with `@[fun_prop]`/`@[continuity]` so
integrability side goals in the track discharge by `fun_prop`. -/
@[continuity, fun_prop]
lemma continuous_e : Continuous e := by
  unfold e; fun_prop

/-- `expSum N a` is continuous (finite sum of smooth terms). -/
@[continuity, fun_prop]
lemma continuous_expSum (N : ℕ) (a : ℕ → ℂ) : Continuous (expSum N a) := by
  unfold expSum
  apply continuous_finsetSum
  intro n _
  fun_prop

end Salt.LS

-- ==== upstream: Salt/LS/GaussSum.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# Large sieve track, nodes L7.1 + L7.2: the Gauss-sum machinery

Blueprint: `docs/blueprints/largesieve.md` (W4, character form).

Work over a primitive Dirichlet character `χ : DirichletCharacter ℂ q` (`q ≥ 1`,
composite allowed) and the standard primitive additive character
`ψ = ZMod.stdAddChar : AddChar (ZMod q) ℂ`, `ψ j = exp (2πi j / q)`.

* **L7.2** (`gaussSum_normSq_of_primitive`, specialised as `gaussSum_normSq`):
  `‖gaussSum χ ψ‖² = q` for **all** `q` (not just prime). mathlib's
  `gaussSum_mul_gaussSum_eq_card` is `[Field R]`-only, so we take the
  Parseval-over-residues route that works at composite moduli. Compute
  `T := ∑_{n : ZMod q} ‖gaussSum χ (ψ.mulShift n)‖²` two ways:
  - via `gaussSum_mulShift_of_isPrimitive`, `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · τ`,
    so `T = (∑_a ‖χ a‖²) · ‖τ‖²`;
  - expanding the square and using additive-character orthogonality
    (`AddChar.sum_mulShift`), `∑_n ψ(n·(a−b)) = q·δ_{a,b}`, so `T = q · ∑_a ‖χ a‖²`.
  Equate and cancel the positive factor `∑_a ‖χ a‖²` (its `a = 1` term is `1`).
  The argument never computes `φ(q)` and holds for any primitive additive
  character.

* **L7.1** (`dirichlet_inversion`, `dirichlet_inversion'`): the Gauss-sum
  inversion `∑_a χ⁻¹ a · ψ(n·a) = χ n · gaussSum χ⁻¹ ψ`, i.e.
  `gaussSum_mulShift_of_isPrimitive` at the primitive character `χ⁻¹`
  (`conductor_inv` gives primitivity of the inverse). Solving for `χ n` uses
  `gaussSum χ⁻¹ ψ ≠ 0` (`gaussSum_ne_zero`, itself from L7.2 and `q ≥ 1`).

* **The `e`-bridge** (`stdAddChar_eq_e`): `ψ a = e (a.val / q)`, connecting
  mathlib's `stdAddChar`/`toCircle` plumbing to the track carrier
  `e x = exp (2πi x)`. This lets L7.3 rewrite `∑_a χ⁻¹ a · ψ(n·a)` as an
  `expSum`-style evaluation at the Farey point `n/q`.
-/

namespace Salt.LS

open scoped BigOperators
open AddChar DirichletCharacter ComplexConjugate

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

/-! ### L7.2 — `‖gaussSum χ ψ‖² = q` for primitive `χ`, all `q` -/

/-- **L7.2 (general additive character).** For a primitive Dirichlet character `χ`
and *any* primitive additive character `ψ` on `ZMod q`, `‖gaussSum χ ψ‖² = q`
(with `q` arbitrary — composite included). -/
theorem gaussSum_normSq_of_primitive (hχ : χ.IsPrimitive)
    {ψ : AddChar (ZMod q) ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (q : ℝ) := by
  -- `conj (ψ x) = ψ (-x)`, from primitivity/roots-of-unity.
  have hR : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]; exact Nat.pos_of_ne_zero (NeZero.ne q)
  have hψconj : ∀ x : ZMod q, conj (ψ x) = ψ (-x) := fun x => by
    rw [AddChar.starComp_apply hR, AddChar.inv_apply]
  -- `conj (χ n) = χ⁻¹ n` and the norm-symmetry `χ⁻¹ n · conj (χ⁻¹ n) = χ n · conj (χ n)`.
  have hconj : ∀ n : ZMod q, conj (χ n) = χ⁻¹ n := fun n => by
    rw [starRingEnd_apply, MulChar.star_apply']
  have hnn : ∀ n : ZMod q, χ⁻¹ n * conj (χ⁻¹ n) = χ n * conj (χ n) := fun n => by
    rw [← hconj n, Complex.conj_conj]; ring
  -- shift relation `gaussSum χ (ψ.mulShift n) = χ⁻¹ n · gaussSum χ ψ`.
  have hG : ∀ n : ZMod q, gaussSum χ (ψ.mulShift n) = χ⁻¹ n * gaussSum χ ψ :=
    fun n => gaussSum_mulShift_of_isPrimitive ψ hχ n
  -- `gaussSum χ (ψ.mulShift n)` expands definitionally.
  have hexp : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) = ∑ a : ZMod q, χ a * ψ (n * a) := fun _ => rfl
  -- expansion of `‖gaussSum χ (ψ.mulShift n)‖²` as a double sum.
  have Gn_conj : ∀ n : ZMod q,
      gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
        = ∑ a : ZMod q, ∑ b : ZMod q, χ a * conj (χ b) * ψ (n * (a - b)) := by
    intro n
    rw [hexp n, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_mul (starRingEnd ℂ), hψconj (n * b)]
    have hcomb : ψ (n * a) * ψ (-(n * b)) = ψ (n * (a - b)) := by
      rw [← AddChar.map_add_eq_mul, show n * a + -(n * b) = n * (a - b) from by ring]
    calc χ a * ψ (n * a) * (conj (χ b) * ψ (-(n * b)))
        = χ a * conj (χ b) * (ψ (n * a) * ψ (-(n * b))) := by ring
      _ = χ a * conj (χ b) * ψ (n * (a - b)) := by rw [hcomb]
  -- Way 2: `T = q · ∑_a χ a · conj (χ a)` (additive orthogonality).
  have hI : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by
    simp_rw [Gn_conj]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    -- collapse the inner `∑_n` via additive orthogonality
    have hstep : ∀ b : ZMod q,
        ∑ n : ZMod q, χ a * conj (χ b) * ψ (n * (a - b))
          = χ a * conj (χ b) * (if a = b then (q : ℂ) else 0) := fun b => by
      rw [← Finset.mul_sum, AddChar.sum_mulShift (a - b) hψ, ZMod.card]
      congr 1
      simp only [Nat.cast_ite, Nat.cast_zero, sub_eq_zero]
    simp_rw [hstep, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq Finset.univ a (fun b => χ a * conj (χ b) * (q : ℂ))]
    rw [if_pos (Finset.mem_univ a)]
    ring
  -- Way 1: `T = (∑_a χ a · conj (χ a)) · (gaussSum χ ψ · conj (gaussSum χ ψ))`.
  have hII : ∑ n : ZMod q, gaussSum χ (ψ.mulShift n) * conj (gaussSum χ (ψ.mulShift n))
      = (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hG n, map_mul, ← hnn n]
    ring
  -- Equate the two computations.
  have key : (∑ a : ZMod q, χ a * conj (χ a)) * (gaussSum χ ψ * conj (gaussSum χ ψ))
      = (q : ℂ) * ∑ a : ZMod q, χ a * conj (χ a) := by rw [← hII, hI]
  -- Descend to `ℝ`: both `∑_a χ a conj (χ a)` and `τ conj τ` are real casts.
  have hSumCast : (∑ a : ZMod q, χ a * conj (χ a))
      = ((∑ a : ZMod q, ‖χ a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.mul_conj']; norm_cast
  have hτ : gaussSum χ ψ * conj (gaussSum χ ψ) = ((‖gaussSum χ ψ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; norm_cast
  rw [hSumCast, hτ] at key
  have keyR : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (q : ℝ) * ∑ a : ZMod q, ‖χ a‖ ^ 2 := by exact_mod_cast key
  -- `∑_a ‖χ a‖² > 0` (the `a = 1` term is `1`), so we may cancel it.
  have hS : (∑ a : ZMod q, ‖χ a‖ ^ 2) ≠ 0 := by
    have hpos : 0 < ∑ a : ZMod q, ‖χ a‖ ^ 2 := by
      apply Finset.sum_pos'
      · intro a _; positivity
      · refine ⟨1, Finset.mem_univ 1, ?_⟩
        rw [MulChar.map_one, norm_one]; norm_num
    exact ne_of_gt hpos
  have hcancel : (∑ a : ZMod q, ‖χ a‖ ^ 2) * ‖gaussSum χ ψ‖ ^ 2
      = (∑ a : ZMod q, ‖χ a‖ ^ 2) * (q : ℝ) := by rw [keyR]; ring
  exact mul_left_cancel₀ hS hcancel

/-- **L7.2.** For a primitive Dirichlet character `χ` mod `q` and the standard
additive character, `‖gaussSum χ ψ‖² = q`, for all `q ≥ 1` (composite included). -/
theorem gaussSum_normSq (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ)‖ ^ 2 = (q : ℝ) :=
  gaussSum_normSq_of_primitive χ hχ (ZMod.isPrimitive_stdAddChar q)

/-- For primitive `χ`, the Gauss sum with the standard additive character is
nonzero (immediate from L7.2 and `q ≥ 1`). -/
theorem gaussSum_ne_zero (hχ : χ.IsPrimitive) :
    gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) ≠ 0 := by
  have hnorm := gaussSum_normSq χ hχ
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  intro h
  rw [h, norm_zero] at hnorm
  have hq0 : (q : ℝ) = 0 := by rw [← hnorm]; norm_num
  linarith

/-! ### L7.1 — Gauss-sum inversion for primitive `χ` -/

omit [NeZero q] in
/-- `χ⁻¹` is primitive when `χ` is (`conductor_inv`). -/
theorem isPrimitive_inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  have h : χ⁻¹.conductor = q := by rw [DirichletCharacter.conductor_inv]; exact hχ
  exact h

/-- **L7.1 (inversion, sum form).** For primitive `χ` and every `n : ZMod q`
(units and non-units alike),
`∑ a, χ⁻¹ a · ψ (n·a) = χ n · gaussSum χ⁻¹ ψ`. -/
theorem dirichlet_inversion (hχ : χ.IsPrimitive) (n : ZMod q) :
    ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  calc ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a)
      = gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod q) ℂ).mulShift n) := by
        simp only [gaussSum, AddChar.mulShift_apply]
    _ = χ n * gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
        rw [gaussSum_mulShift_of_isPrimitive _ hχ', inv_inv]

/-- **L7.1 (inversion, solved for `χ`).** For primitive `χ`,
`χ n = (gaussSum χ⁻¹ ψ)⁻¹ · ∑ a, χ⁻¹ a · ψ (n·a)`. This is the character
LS-expansion form consumed by L7.3. -/
theorem dirichlet_inversion' (hχ : χ.IsPrimitive) (n : ZMod q) :
    χ n = (gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ))⁻¹
        * ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar (n * a) := by
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  rw [dirichlet_inversion χ hχ n, mul_comm (χ n),
    ← mul_assoc, inv_mul_cancel₀ (gaussSum_ne_zero χ⁻¹ hχ'), one_mul]

/-! ### The `e`-bridge -/

/-- **The `e`-bridge (deliverable 3).** mathlib's standard additive character
`ZMod.stdAddChar` on `ZMod q` is the track carrier `e` at the Farey point:
`ψ a = e (a.val / q)`. -/
theorem stdAddChar_eq_e (a : ZMod q) :
    (ZMod.stdAddChar a : ℂ) = e ((a.val : ℝ) / q) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp]
  unfold e
  congr 1
  push_cast
  ring

end Salt.LS

-- ==== upstream: Salt/LS/Dist.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# L0.2 — the mod-1 circle distance `dist₁`

Design: `docs/blueprints/largesieve.md`, "Carrier choices" and node `L0.2`.

`dist₁ x y` is the distance from `x - y` to the nearest integer, i.e. the
distance between `x` and `y` on the circle `ℝ / ℤ`. We implement it via
mathlib's `round` function rather than the `AddCircle` norm: `AddCircle`
carries its own quotient-type coercions (`UnitAddCircle.norm_eq` unfolds to
exactly `|x - round x|`, but only after passing through `(· : UnitAddCircle)`),
whereas the spec lemmas below all consume `x y : ℝ` directly, so the bare
`round`-based definition avoids coercion overhead. The key mathlib facts
driving every lemma here are `abs_sub_round` (`|t - round t| ≤ 1/2`) and
`round_le` (`round` minimizes `|t - m|` over `m : ℤ`, i.e.
`|t - round t| ≤ |t - m|` for every integer `m`).
-/

namespace Salt.LS

/-- The mod-1 circle distance: the distance from `x - y` to the nearest
integer. -/
noncomputable def dist₁ (x y : ℝ) : ℝ := |x - y - round (x - y)|

@[simp]
theorem dist₁_self (x : ℝ) : dist₁ x x = 0 := by simp [dist₁]

theorem dist₁_nonneg (x y : ℝ) : 0 ≤ dist₁ x y := abs_nonneg _

theorem dist₁_le_half (x y : ℝ) : dist₁ x y ≤ 1 / 2 := abs_sub_round (x - y)

theorem dist₁_le_abs (x y : ℝ) : dist₁ x y ≤ |x - y| := by
  unfold dist₁
  simpa using round_le (x - y) 0

theorem dist₁_comm (x y : ℝ) : dist₁ x y = dist₁ y x := by
  have h1 : dist₁ x y ≤ dist₁ y x := by
    have := round_le (x - y) (-round (y - x))
    have he : x - y - ((-round (y - x) : ℤ) : ℝ) = -(y - x - round (y - x)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  have h2 : dist₁ y x ≤ dist₁ x y := by
    have := round_le (y - x) (-round (x - y))
    have he : y - x - ((-round (x - y) : ℤ) : ℝ) = -(x - y - round (x - y)) := by
      push_cast; ring
    rw [he, abs_neg] at this
    exact this
  exact le_antisymm h1 h2

theorem dist₁_add_int_left (x y : ℝ) (n : ℤ) : dist₁ (x + n) y = dist₁ x y := by
  unfold dist₁
  have hxy : x + (n : ℝ) - y = (x - y) + (n : ℝ) := by ring
  rw [hxy, round_add_intCast]
  congr 1
  push_cast
  ring

theorem dist₁_add_int_right (x y : ℝ) (n : ℤ) : dist₁ x (y + n) = dist₁ x y := by
  rw [dist₁_comm x (y + n), dist₁_add_int_left y x n, dist₁_comm]

theorem dist₁_triangle (x y z : ℝ) : dist₁ x z ≤ dist₁ x y + dist₁ y z := by
  unfold dist₁
  have h1 : |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| :=
    round_le (x - z) (round (x - y) + round (y - z))
  have h2 : x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)
      = (x - y - round (x - y)) + (y - z - round (y - z)) := by push_cast; ring
  calc |x - z - round (x - z)|
      ≤ |x - z - ((round (x - y) + round (y - z) : ℤ) : ℝ)| := h1
    _ = |(x - y - round (x - y)) + (y - z - round (y - z))| := by rw [h2]
    _ ≤ |x - y - round (x - y)| + |y - z - round (y - z)| := abs_add_le _ _

theorem dist₁_eq_zero_iff (x y : ℝ) : dist₁ x y = 0 ↔ ∃ n : ℤ, x - y = n := by
  unfold dist₁
  rw [abs_eq_zero, sub_eq_zero]
  constructor
  · intro h
    exact ⟨round (x - y), h⟩
  · rintro ⟨n, hn⟩
    rw [hn, round_intCast]

end Salt.LS

-- ==== upstream: Salt/BV/PolyaVinogradov.lean ====
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/


/-!
# V2.PV — the Pólya–Vinogradov inequality

Design: `docs/blueprints/bv.md`, node `V2.PV`. For a *primitive* Dirichlet
character `χ` mod `f` (with `f ≥ 2`, hence `χ ≠ 1`), the partial character sums
`∑_{m < t} χ(m)` are bounded, **uniformly in `t`**, by `√f · (1 + log f)`.

Route (classical, adapted to the landed Gauss-sum toolkit `Salt/LS/GaussSum.lean`):

1. **Gauss-sum inversion** (`dirichlet_inversion'`): expand each `χ(m)` as
   `τ⁻¹ · ∑_a χ⁻¹(a) · ψ(m·a)` with `ψ = ZMod.stdAddChar`, `τ = gaussSum χ⁻¹ ψ`,
   and swap the `m`/`a` sums:
   `∑_{m<t} χ(m) = τ⁻¹ · ∑_a χ⁻¹(a) · ∑_{m<t} ψ(m·a)`.
2. **Geometric sums** (`geom_e_bound`): `∑_{m<t} ψ(m·a) = ∑_{m<t} (ψ a)^m` is a
   geometric series in `ψ a = e(a.val/f)`, bounded by `1/(2·dist₁(a.val/f, 0))`
   via the chord estimate `‖e θ − 1‖ ≥ 4·dist₁(θ, 0)` (`chord`, from
   `‖exp(ix)−1‖ = 2|sin(x/2)|` and Jordan's inequality `2/π·|x| ≤ |sin x|`).
   The `a = 0` term drops (`χ⁻¹(0) = 0` since `0` is a non-unit).
3. **Harmonic sum** (`dist_lb` + `term_le` + `sum_H_le`): `dist₁(k/f,0) ≥
   k(f−k)/f²`, so the `a`-sum is `≤ f·H_{f−1} ≤ f·(1 + log f)` via
   `harmonic_le_one_add_log`.
4. **Assemble** using `‖τ⁻¹‖ = 1/√f` (`gaussSum_normSq` at `χ⁻¹`).

This is (to our knowledge) the first machine-checked Pólya–Vinogradov in any
library.
-/

namespace Salt.BV

open scoped BigOperators
open Salt.LS

/-! ### The chord estimate `‖e θ − 1‖ ≥ 4·dist₁(θ, 0)` -/

/-- **Chord bound.** `‖e θ − 1‖ = 2|sin(πθ)| ≥ 4·dist₁(θ, 0)`, uniformly in `θ`
(Jordan's inequality after reducing `θ` mod `1`). -/
lemma chord (θ : ℝ) : 4 * dist₁ θ 0 ≤ ‖e θ - 1‖ := by
  have hdd : dist₁ θ 0 = |θ - (round θ : ℝ)| := by
    unfold dist₁; simp only [sub_zero]
  have hnorm : ‖e θ - 1‖ = 2 * |Real.sin (Real.pi * θ)| := by
    have he : e θ = Complex.exp (Complex.I * ((2 * Real.pi * θ : ℝ) : ℂ)) := by
      unfold e; congr 1; push_cast; ring
    rw [he, Complex.norm_exp_I_mul_ofReal_sub_one,
        show (2 * Real.pi * θ) / 2 = Real.pi * θ from by ring,
        Real.norm_eq_abs, abs_mul, abs_two]
  have hsin_eq :
      |Real.sin (Real.pi * (θ - (round θ : ℝ)))| = |Real.sin (Real.pi * θ)| := by
    rw [show Real.pi * (θ - (round θ : ℝ)) = Real.pi * θ - (round θ : ℝ) * Real.pi from by ring,
        Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
    simp
  have hsin : 2 * dist₁ θ 0 ≤ |Real.sin (Real.pi * θ)| := by
    rw [hdd, ← hsin_eq]
    have hle : |Real.pi * (θ - (round θ : ℝ))| ≤ Real.pi / 2 := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      have hh : |θ - (round θ : ℝ)| ≤ 1 / 2 := by rw [← hdd]; exact dist₁_le_half θ 0
      nlinarith [Real.pi_pos, hh]
    have hj := Real.mul_abs_le_abs_sin hle
    have hcompute :
        2 / Real.pi * |Real.pi * (θ - (round θ : ℝ))| = 2 * |θ - (round θ : ℝ)| := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    rw [hcompute] at hj
    exact hj
  rw [hnorm]; linarith [hsin]

/-! ### The geometric-sum bound -/

/-- **Geometric bound.** For `dist₁ θ 0 > 0` (so `e θ ≠ 1`), the geometric partial
sum is bounded uniformly in the length `t`:
`‖∑_{m<t} (e θ)^m‖ ≤ 1/(2·dist₁(θ, 0))`. -/
lemma geom_e_bound (θ : ℝ) (t : ℕ) (hd : 0 < dist₁ θ 0) :
    ‖∑ m ∈ Finset.range t, (e θ) ^ m‖ ≤ 1 / (2 * dist₁ θ 0) := by
  have hchord : 4 * dist₁ θ 0 ≤ ‖e θ - 1‖ := chord θ
  have hpos : 0 < ‖e θ - 1‖ := lt_of_lt_of_le (by linarith) hchord
  have hzne : e θ ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hpos; exact lt_irrefl 0 hpos
  have hnum : ‖(e θ) ^ t - 1‖ ≤ 2 := by
    calc ‖(e θ) ^ t - 1‖ ≤ ‖(e θ) ^ t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_e, one_pow, norm_one]; norm_num
  have hdpos2 : (0 : ℝ) < 2 * dist₁ θ 0 := by linarith
  rw [geom_sum_eq hzne t, norm_div, div_le_iff₀ hpos]
  calc ‖(e θ) ^ t - 1‖ ≤ 2 := hnum
    _ = 1 / (2 * dist₁ θ 0) * (4 * dist₁ θ 0) := by
        rw [eq_comm, div_mul_eq_mul_div, one_mul, div_eq_iff hdpos2.ne']; ring
    _ ≤ 1 / (2 * dist₁ θ 0) * ‖e θ - 1‖ := by
        apply mul_le_mul_of_nonneg_left hchord
        exact le_of_lt (one_div_pos.mpr hdpos2)

/-! ### The `dist₁` lower bound and the harmonic sum -/

/-- **Denominator-sharp lower bound.** For `0 < k < f`,
`dist₁(k/f, 0) ≥ k(f−k)/f²`. Proof: every integer `n` has
`|k/f − n| ≥ k(f−k)/f²` (case split on `n ≤ 0` vs `n ≥ 1`); instantiate at
`n = round(k/f)`. -/
lemma dist_lb (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ dist₁ ((k : ℝ) / (f : ℝ)) 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hf0 : (0 : ℝ) < f := by linarith
  have hfne : (f : ℝ) ≠ 0 := hf0.ne'
  have hkfpos : (0 : ℝ) < (k : ℝ) / (f : ℝ) := div_pos hkR hf0
  have key : ∀ n : ℤ,
      (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ |(k : ℝ) / (f : ℝ) - (n : ℝ)| := by
    intro n
    have h1 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ (k : ℝ) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg (k : ℝ)) hf0.le]
    have h2 : (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 ≤ ((f : ℝ) - k) / (f : ℝ) := by
      rw [div_le_div_iff₀ (pow_pos hf0 2) hf0]
      nlinarith [mul_nonneg (sq_nonneg ((f : ℝ) - k)) hf0.le]
    rcases le_or_gt (n : ℝ) 0 with hn | hn
    · rw [abs_of_nonneg (by linarith)]
      linarith
    · have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnZ
      have hkf1 : (k : ℝ) / (f : ℝ) < 1 := by rw [div_lt_one hf0]; exact hkfR
      rw [abs_of_nonpos (by linarith)]
      have hfk_eq : ((f : ℝ) - k) / (f : ℝ) = 1 - (k : ℝ) / (f : ℝ) := by field_simp
      linarith
  have hdd : dist₁ ((k : ℝ) / (f : ℝ)) 0
      = |(k : ℝ) / (f : ℝ) - (round ((k : ℝ) / (f : ℝ)) : ℝ)| := by
    unfold dist₁; simp only [sub_zero]
  rw [hdd]
  exact key (round ((k : ℝ) / (f : ℝ)))

/-- `dist₁(k/f, 0) > 0` for `0 < k < f`. -/
lemma dist_pos (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    0 < dist₁ ((k : ℝ) / (f : ℝ)) 0 := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hfkR : (0 : ℝ) < (f : ℝ) - k := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hBpos : (0 : ℝ) < (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 :=
    div_pos (mul_pos hkR hfkR) (pow_pos hf0 2)
  exact lt_of_lt_of_le hBpos (dist_lb f k hk hkf)

/-- **Per-term harmonic bound.** `1/(2·dist₁(k/f,0)) ≤ (f/2)·(1/k + 1/(f−k))`. -/
lemma term_le (f k : ℕ) (hk : 0 < k) (hkf : k < f) :
    1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hkfR : (k : ℝ) < f := by exact_mod_cast hkf
  have hfkR : (0 : ℝ) < (f : ℝ) - k := by linarith
  have hf0 : (0 : ℝ) < f := by linarith
  have hlb := dist_lb f k hk hkf
  have hBpos : (0 : ℝ) < (k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2 :=
    div_pos (mul_pos hkR hfkR) (pow_pos hf0 2)
  have step1 : 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2)) := by
    apply one_div_le_one_div_of_le
    · linarith
    · linarith
  have step2 : 1 / (2 * ((k : ℝ) * ((f : ℝ) - k) / (f : ℝ) ^ 2))
      = ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
    rw [eq_comm]
    field_simp
    ring
  rw [step2] at step1
  exact step1

/-- **The harmonic sum.** `∑_{k<f, k≠0} 1/(2·dist₁(k/f,0)) ≤ f·(1 + log f)`. -/
lemma sum_H_le (f : ℕ) (hf : 2 ≤ f) :
    ∑ k ∈ Finset.range f,
        (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
      ≤ (f : ℝ) * (1 + Real.log f) := by
  -- the two inner harmonic sums are each `≤ 1 + log f`
  have hEq : ((harmonic (f - 1) : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 (f - 1), (1 : ℝ) / k := by
    rw [harmonic_eq_sum_Icc]; push_cast
    apply Finset.sum_congr rfl; intro k _; rw [one_div]
  have hA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k ≤ 1 + Real.log f := by
    have hIco : Finset.Ico 1 f = Finset.Icc 1 (f - 1) := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [hIco, ← hEq]
    calc ((harmonic (f - 1) : ℚ) : ℝ) ≤ 1 + Real.log ((f - 1 : ℕ) : ℝ) :=
          harmonic_le_one_add_log (f - 1)
      _ ≤ 1 + Real.log f := by
          have h01 : (0 : ℝ) < ((f - 1 : ℕ) : ℝ) := by
            have : 0 < f - 1 := by omega
            exact_mod_cast this
          have hle : ((f - 1 : ℕ) : ℝ) ≤ (f : ℝ) := by exact_mod_cast Nat.sub_le f 1
          have := Real.log_le_log h01 hle
          linarith
  have hBA : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k)
      = ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k := by
    apply Finset.sum_nbij' (fun k => f - k) (fun k => f - k)
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; omega
    · intro k hk; rw [Finset.mem_Ico] at hk; rw [Nat.cast_sub hk.2.le]
  have hB : ∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k) ≤ 1 + Real.log f := by
    rw [hBA]; exact hA
  -- convert the guarded `range` sum to a sum over `Ico 1 f`
  have hconv : ∀ k : ℕ,
      (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = (if k ≠ 0 then 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) else 0) := by
    intro k; by_cases h : k = 0 <;> simp [h]
  have hrange :
      ∑ k ∈ Finset.range f,
          (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0))
        = ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0) := by
    rw [Finset.sum_congr rfl (fun k _ => hconv k), ← Finset.sum_filter]
    congr 1
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hrange]
  calc ∑ k ∈ Finset.Ico 1 f, 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)
      ≤ ∑ k ∈ Finset.Ico 1 f, ((f : ℝ) / 2) * (1 / (k : ℝ) + 1 / ((f : ℝ) - k)) := by
        apply Finset.sum_le_sum; intro k hk
        rw [Finset.mem_Ico] at hk
        exact term_le f k hk.1 hk.2
    _ = ((f : ℝ) / 2)
        * ((∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / k)
            + (∑ k ∈ Finset.Ico 1 f, (1 : ℝ) / ((f : ℝ) - k))) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ ((f : ℝ) / 2) * (2 * (1 + Real.log f)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hA, hB]
    _ = (f : ℝ) * (1 + Real.log f) := by ring

/-! ### The theorem -/

/-- **Pólya–Vinogradov (primitive characters).** For a primitive Dirichlet
character `χ` mod `f` with `2 ≤ f` (hence `χ ≠ 1`), the partial character sums
are bounded, uniformly in `t`, by `√f · (1 + log f)`. -/
theorem polya_vinogradov {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t : ℕ) :
    ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖ ≤ Real.sqrt f * (1 + Real.log f) := by
  haveI : Fact (1 < f) := ⟨hf⟩
  set ψ : AddChar (ZMod f) ℂ := ZMod.stdAddChar with hψ
  have hχ' : χ⁻¹.IsPrimitive := isPrimitive_inv χ hχ
  have hf0 : (0 : ℝ) < f := by
    have : 0 < f := by omega
    exact_mod_cast this
  -- Step 1: Gauss-sum inversion + sum swap.
  have hA : ∑ m ∈ Finset.range t, χ (m : ZMod f)
      = (gaussSum χ⁻¹ ψ)⁻¹
        * ∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)) := by
    have expand : ∀ m : ℕ, χ (m : ZMod f)
        = (gaussSum χ⁻¹ ψ)⁻¹ * ∑ a : ZMod f, χ⁻¹ a * ψ ((m : ZMod f) * a) := by
      intro m
      rw [hψ]
      exact dirichlet_inversion' χ hχ (m : ZMod f)
    rw [Finset.sum_congr rfl (fun m _ => expand m), ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  -- Step 2: `‖τ‖ = √f`.
  have hτnorm : ‖gaussSum χ⁻¹ ψ‖ = Real.sqrt f := by
    rw [hψ, ← Real.sqrt_sq (norm_nonneg _), gaussSum_normSq χ⁻¹ hχ']
  -- Step 3: per-term bound `‖χ⁻¹ a‖ · ‖geom a‖ ≤ H a`.
  have hterm : ∀ a : ZMod f,
      ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)‖
        ≤ (if a.val = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) := by
    intro a
    by_cases ha : a.val = 0
    · rw [if_pos ha]
      have ha0 : a = 0 := (ZMod.val_eq_zero a).mp ha
      have hz : χ⁻¹ a = 0 := ha0 ▸ MulChar.map_nonunit χ⁻¹ not_isUnit_zero
      simp [hz]
    · rw [if_neg ha]
      have hval_pos : 0 < a.val := Nat.pos_of_ne_zero ha
      have hval_lt : a.val < f := ZMod.val_lt a
      have hnorm_le : ‖χ⁻¹ a‖ ≤ 1 := χ⁻¹.norm_le_one a
      have hGeq : (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))
          = ∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m := by
        apply Finset.sum_congr rfl; intro m _
        rw [show ((m : ZMod f) * a) = m • a from by rw [nsmul_eq_mul],
            AddChar.map_nsmul_eq_pow, hψ, stdAddChar_eq_e]
      rw [hGeq]
      have hdpos : 0 < dist₁ ((a.val : ℝ) / (f : ℝ)) 0 := dist_pos f a.val hval_pos hval_lt
      have hgeom : ‖∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m‖
          ≤ 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0) :=
        geom_e_bound ((a.val : ℝ) / (f : ℝ)) t hdpos
      calc ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, (e ((a.val : ℝ) / (f : ℝ))) ^ m‖
          ≤ 1 * (1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) :=
            mul_le_mul hnorm_le hgeom (norm_nonneg _) (by norm_num)
        _ = 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0) := one_mul _
  -- Step 4: bound the inner `a`-sum by `f·(1 + log f)`.
  have hinner :
      ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
        ≤ (f : ℝ) * (1 + Real.log f) := by
    calc ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
        ≤ ∑ a : ZMod f, ‖χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖ :=
          norm_sum_le _ _
      _ = ∑ a : ZMod f, ‖χ⁻¹ a‖ * ‖∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a)‖ := by
          simp_rw [norm_mul]
      _ ≤ ∑ a : ZMod f,
            (if a.val = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((a.val : ℝ) / (f : ℝ)) 0)) := by
          apply Finset.sum_le_sum; intro a _; exact hterm a
      _ = ∑ k ∈ Finset.range f,
            (if k = 0 then (0 : ℝ) else 1 / (2 * dist₁ ((k : ℝ) / (f : ℝ)) 0)) := by
          apply Finset.sum_nbij' (fun a : ZMod f => a.val) (fun k : ℕ => (k : ZMod f))
          · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
          · intro k _; exact Finset.mem_univ _
          · intro a _; exact ZMod.natCast_zmod_val a
          · intro k hk; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
          · intro a _; rfl
      _ ≤ (f : ℝ) * (1 + Real.log f) := sum_H_le f hf
  -- Step 5: assemble.
  have hspos : 0 < Real.sqrt f := Real.sqrt_pos.mpr hf0
  have hs : Real.sqrt f * Real.sqrt f = f := Real.mul_self_sqrt hf0.le
  have hsinv : (Real.sqrt f)⁻¹ * (f : ℝ) = Real.sqrt f := by
    rw [inv_mul_eq_div, div_eq_iff hspos.ne']; exact hs.symm
  rw [hA, norm_mul, norm_inv, hτnorm]
  calc (Real.sqrt f)⁻¹
        * ‖∑ a : ZMod f, χ⁻¹ a * (∑ m ∈ Finset.range t, ψ ((m : ZMod f) * a))‖
      ≤ (Real.sqrt f)⁻¹ * ((f : ℝ) * (1 + Real.log f)) := by
        apply mul_le_mul_of_nonneg_left hinner
        exact le_of_lt (inv_pos.mpr hspos)
    _ = Real.sqrt f * (1 + Real.log f) := by
        rw [← mul_assoc, hsinv]

/-- **Prefix-max form** (consumed by V2a). Since the Pólya–Vinogradov bound is
uniform in the prefix length `t`, the maximum of `‖∑_{m<t} χ(m)‖` over all
`t ≤ T` obeys the same bound. -/
theorem polya_vinogradov_sup' {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (T : ℕ) :
    (Finset.range (T + 1)).sup' Finset.nonempty_range_add_one
        (fun t => ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖)
      ≤ Real.sqrt f * (1 + Real.log f) := by
  rw [Finset.sup'_le_iff]
  intro t _
  exact polya_vinogradov χ hχ hf t

end Salt.BV



theorem solution {f : ℕ} [NeZero f] (χ : DirichletCharacter ℂ f)
    (hχ : χ.IsPrimitive) (hf : 2 ≤ f) (t : ℕ) :
    ‖∑ m ∈ Finset.range t, χ (m : ZMod f)‖ ≤ Real.sqrt f * (1 + Real.log f) :=
  Salt.BV.polya_vinogradov χ hχ hf t
