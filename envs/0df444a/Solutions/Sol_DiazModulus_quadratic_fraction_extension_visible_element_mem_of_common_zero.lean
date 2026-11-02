-- Prove2me | solution 1 for DiazModulus.quadratic_fraction_extension_visible_element_mem_of_common_zero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:33:21.856408+00:00
-- url     : https://prove2.me/submissions/29aa52f3-7745-4864-aa51-9e555f037037

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A common zero of `P` and `S` on `P¹` puts a `t_x` in `H₀ + Q̄·Q S/(u P)`

Let `u ∉ Q̄`, `H₀ = span(1, u, u⁻¹)`, `g = Q(u) S(u)/(u P(u))` and `T = H₀ + Q̄g`. Every step writes
`g = κ t + h` with `κ ∈ Q̄ ∖ 0`, `h ∈ H₀` and `t` one of `u²`, `u⁻²`, `(u − b)⁻¹` (`b ∈ Q̄ ∖ 0`); then
`t = κ⁻¹(g − h) ∈ T`. The membership `h ∈ H₀` always comes from `R(u)/u ∈ H₀` for `deg R ≤ 2`.

**Reduction.** In both cases `g = Q(u) r(u)/(u m(u))` with `m ≠ 0`, `deg m, deg r ≤ 1`, `m` coprime
to `Q`, `deg Q = 2` if `m` is constant, and `r ∉ Q̄·m`.
* `¬ IsCoprime P S`: an irreducible common factor has a root `a ∈ Q̄` (roots in `ℂ` of polynomials
  over `Q̄` are algebraic), so `P = (X − a) m`, `S = (X − a) r`, and `u − a` cancels. `r = k m` would
  give `S = k P`.
* common zero at `∞` (`P.coeff 2 = S.coeff 2 = 0`): take `m = P`, `r = S`.

**Core**, with `N = Q r` (`deg N ≤ 3`):
* `m = m₁` constant: `deg r = 1` (else `r ∈ Q̄·m`), `deg N = 3`, and
  `g = (lc N/m₁) u² + m₁⁻¹ (N − lc N·X³)(u)/u`.
* `m = m₀ (X − b)`: `Q(b) ≠ 0` (coprime), `r(b) ≠ 0` (else `r ∈ Q̄·m`), so `N(b) ≠ 0`.
  If `b = 0`: `N − N(0) = X R` and `g = (N(0)/m₀) u⁻² + m₀⁻¹ R(u)/u`.
  If `b ≠ 0`: with `c = N(b)/b`, `N − cX = (X − b) R` and `g = (c/m₀)(u − b)⁻¹ + m₀⁻¹ R(u)/u`.
-/

namespace R21b_V1

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem smul_def' (c : ↥Qbar) (z : ℂ) : c • z = (c : ℂ) * z := rfl

theorem u_ne_zero {u : ℂ} (hu : u ∉ Qbar) : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem sub_ne_zero' {u : ℂ} (hu : u ∉ Qbar) (b : ↥Qbar) : u - b ≠ 0 :=
  fun h => hu (by rw [sub_eq_zero.1 h]; exact b.2)

/-- A polynomial over `Q̄` of positive degree has a root in `Q̄`. -/
theorem exists_root {p : (↥Qbar)[X]} (hp : 0 < p.natDegree) : ∃ b : ↥Qbar, p.IsRoot b := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective (k := ℂ)
    (R := ↥Qbar) Subtype.val_injective p (by
      rw [degree_eq_natDegree (ne_zero_of_natDegree_gt hp)]; exact_mod_cast hp.ne')
  by_cases hzq : z ∈ Qbar
  · refine ⟨⟨z, hzq⟩, ?_⟩
    have : aeval (algebraMap (↥Qbar) ℂ ⟨z, hzq⟩) p = 0 := hz
    rw [aeval_algebraMap_apply, coe_aeval_eq_eval] at this
    exact Subtype.val_injective (by simpa using this)
  · exact absurd (transcendental_iff.1 (tr_of_not_mem hzq) p hz) (ne_zero_of_natDegree_gt hp)

theorem divroot (p : (↥Qbar)[X]) {b : ↥Qbar} (hb : p.IsRoot b) :
    ∃ q : (↥Qbar)[X], p = (X - C b) * q ∧ q.natDegree = p.natDegree - 1 :=
  ⟨_, (mul_divByMonic_eq_iff_isRoot.2 hb).symm, by
    rw [natDegree_divByMonic _ (monic_X_sub_C b), natDegree_X_sub_C]⟩

theorem coprime_eval {m Q : (↥Qbar)[X]} (h : IsCoprime m Q) {b : ↥Qbar} (hb : m.IsRoot b) :
    Q.eval b ≠ 0 := by
  obtain ⟨x, y, e⟩ := h
  intro hQ
  simpa [hb.eq_zero, hQ] using congrArg (eval b) e

/-- `R(u)/u ∈ H₀` when `deg R ≤ 2`. -/
theorem quad_div_mem {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have e : aeval u R / u = (R.coeff 1 : ℂ) + (R.coeff 2 : ℂ) * u + (R.coeff 0 : ℂ) * u⁻¹ := by
    rw [aeval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, smul_def']
    field_simp
    ring
  have hs : ∀ x ∈ ({1, u, u⁻¹} : Set ℂ), x ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) :=
    fun x hx => Submodule.subset_span hx
  have := add_mem (add_mem (Submodule.smul_mem _ (R.coeff 1) (hs 1 (by simp)))
    (Submodule.smul_mem _ (R.coeff 2) (hs u (by simp))))
    (Submodule.smul_mem _ (R.coeff 0) (hs u⁻¹ (by simp)))
  rw [e]
  simpa only [smul_def', mul_one] using this

/-- `g = κ t + h` with `κ ≠ 0`, `h ∈ H₀` puts `t` in `H₀ + Q̄g`. -/
theorem fin {u g t h : ℂ} (κ : ↥Qbar) (hκ : κ ≠ 0)
    (hh : h ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ)) (e : g = κ * t + h) :
    t ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) := by
  have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ
  have hle : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ) :=
    Submodule.span_mono (by intro x hx; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢; tauto)
  have ht : t = κ⁻¹ • (g - h) := by
    rw [smul_def', e, add_sub_cancel_right]; push_cast; field_simp
  rw [ht]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (by simp)) (hle hh))

theorem deg1 {p : (↥Qbar)[X]} (h2 : p.natDegree ≤ 2) (hc : p.coeff 2 = 0) : p.natDegree ≤ 1 := by
  by_contra h
  have e : p.natDegree = 2 := by omega
  have hp : p ≠ 0 := by rintro rfl; simp at e
  exact (leadingCoeff_ne_zero.2 hp) (by rw [leadingCoeff, e]; exact hc)

/-- The core: `g = Q(u) r(u)/(u m(u))` with `deg m, deg r ≤ 1`, `r ∉ Q̄·m`. -/
theorem core {u : ℂ} (hu : u ∉ Qbar) {m r Q : (↥Qbar)[X]} (hm0 : m ≠ 0) (hm : m.natDegree ≤ 1)
    (hr : r.natDegree ≤ 1) (hQ : Q.natDegree ≤ 2) (hmQ : IsCoprime m Q)
    (hmc : m.natDegree = 0 → Q.natDegree = 2) (hrm : ∀ k : ↥Qbar, r ≠ C k * m) :
    (u ^ 2 ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u r / (u * aeval u m)} : Set ℂ) ∨
      (u ^ 2)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u r / (u * aeval u m)} : Set ℂ) ∨
      ∃ a ∈ Qbar, a ≠ 0 ∧
        (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u r / (u * aeval u m)} : Set ℂ)) := by
  have hu0 := u_ne_zero hu
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    have := hmc (natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hmQ))
    simp at this
  have hNd : (Q * r).natDegree ≤ 3 := natDegree_mul_le.trans (by omega)
  rw [← map_mul]
  rcases Nat.eq_zero_or_pos m.natDegree with hmd | hmd
  · -- `m` constant: `u²`
    have hQ2 := hmc hmd
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = C m₁ := ⟨_, eq_C_of_natDegree_eq_zero hmd⟩
    have hm₁ : m₁ ≠ 0 := fun h => hm0 (by rw [h, C_0])
    have hr1 : r.natDegree = 1 := by
      by_contra h
      obtain ⟨k, rfl⟩ : ∃ k, r = C k := ⟨_, eq_C_of_natDegree_eq_zero (show r.natDegree = 0 by omega)⟩
      exact hrm (k / m₁) (by rw [← C_mul, div_mul_cancel₀ _ hm₁])
    have hr0 : r ≠ 0 := by rintro rfl; simp at hr1
    have hN3 : (Q * r).natDegree = 3 := by rw [natDegree_mul hQ0 hr0, hQ2, hr1]
    have hlc : (Q * r).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (mul_ne_zero hQ0 hr0)
    have hNu : aeval u (Q * r) = aeval u (Q * r).eraseLead + ((Q * r).leadingCoeff : ℂ) * u ^ 3 := by
      conv_lhs => rw [← eraseLead_add_C_mul_X_pow (Q * r)]
      rw [hN3]
      simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am]
    have hm₁' : (m₁ : ℂ) ≠ 0 := by exact_mod_cast hm₁
    refine Or.inl (fin ((Q * r).leadingCoeff * m₁⁻¹) (mul_ne_zero hlc (inv_ne_zero hm₁))
      (Submodule.smul_mem _ m₁⁻¹
        (quad_div_mem hu0 ((eraseLead_natDegree_le (Q * r)).trans (by omega)))) ?_)
    rw [hNu, smul_def', aeval_C, am]
    push_cast
    field_simp
    ring
  · -- `m = m₀ (X − b)`
    obtain ⟨b, hb⟩ := exists_root hmd
    obtain ⟨m', hmm', hm'd⟩ := divroot m hb
    obtain ⟨m₀, rfl⟩ : ∃ m₀, m' = C m₀ :=
      ⟨_, eq_C_of_natDegree_eq_zero (show m'.natDegree = 0 by omega)⟩
    have hm₀ : m₀ ≠ 0 := fun h => hm0 (by rw [hmm', h, C_0, mul_zero])
    have hm₀' : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm₀
    have hmu : aeval u m = (u - b) * m₀ := by
      rw [hmm']; simp only [map_mul, map_sub, aeval_X, aeval_C, am]
    have hQb := coprime_eval hmQ hb
    have hrb : r.eval b ≠ 0 := by
      intro hrb
      obtain ⟨r', hrr', hr'd⟩ := divroot r hrb
      obtain ⟨k, rfl⟩ : ∃ k, r' = C k :=
        ⟨_, eq_C_of_natDegree_eq_zero (show r'.natDegree = 0 by omega)⟩
      apply hrm (k / m₀)
      have e : C (k / m₀) * C m₀ = C k := by rw [← C_mul, div_mul_cancel₀ _ hm₀]
      rw [hrr', hmm']
      linear_combination (-(X - C b)) * e
    have hNb : (Q * r).eval b ≠ 0 := by rw [eval_mul]; exact mul_ne_zero hQb hrb
    have hub := sub_ne_zero' hu b
    by_cases hb0 : b = 0
    · -- `u⁻²`
      subst hb0
      obtain ⟨R, hR, hRd⟩ := divroot (Q * r - C ((Q * r).eval 0)) (b := 0) (by simp)
      rw [natDegree_sub_C] at hRd
      have hNu : aeval u (Q * r) = (Q * r).eval 0 + u * aeval u R := by
        have := congrArg (aeval u) hR
        simp only [map_sub, map_mul, aeval_X, aeval_C, am, map_zero, sub_zero] at this ⊢
        linear_combination this
      refine Or.inr (Or.inl (fin ((Q * r).eval 0 * m₀⁻¹) (mul_ne_zero hNb (inv_ne_zero hm₀))
        (Submodule.smul_mem _ m₀⁻¹ (quad_div_mem hu0 (R := R) (by omega))) ?_))
      rw [hNu, hmu, smul_def']
      push_cast
      field_simp
      ring
    · -- `(u − b)⁻¹`
      have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb0
      set c : ↥Qbar := (Q * r).eval b / b with hc
      have hc0 : c ≠ 0 := div_ne_zero hNb hb0
      obtain ⟨R, hR, hRd⟩ := divroot (Q * r - C c * X) (b := b) (by
        simp only [IsRoot, eval_sub, eval_mul, eval_C, eval_X, hc]; field_simp; ring)
      have hdeg : (Q * r - C c * X).natDegree ≤ 3 :=
        (natDegree_sub_le _ _).trans (max_le hNd ((natDegree_C_mul_le _ _).trans (by simp)))
      have hNu : aeval u (Q * r) = c * u + (u - b) * aeval u R := by
        have := congrArg (aeval u) hR
        simp only [map_sub, map_mul, aeval_X, aeval_C, am] at this ⊢
        linear_combination this
      refine Or.inr (Or.inr ⟨b, b.2, hb', fin (c * m₀⁻¹) (mul_ne_zero hc0 (inv_ne_zero hm₀))
        (Submodule.smul_mem _ m₀⁻¹ (quad_div_mem hu0 (R := R) (by omega))) ?_⟩)
      rw [hNu, hmu, smul_def']
      push_cast
      field_simp

end R21b_V1

open DiazModulus R21b_V1 in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS : S.natDegree ≤ 2)
    (hSP : ∀ k : ↥Qbar, S ≠ C k * P) (hz : (¬ IsCoprime P S ∨ (P.coeff 2 = 0 ∧ S.coeff 2 = 0))) :
    (u ^ 2 ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ) ∨ (u ^ 2)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ) ∨ ∃ a ∈ Qbar, a ≠ 0 ∧ (u - a)⁻¹ ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S / (u * aeval u P)} : Set ℂ)) := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.1 hcop)
    simp [this] at hdeg
  have hP2 : P.natDegree ≤ 2 := hdeg ▸ le_max_left _ _
  have hQ2 : Q.natDegree ≤ 2 := hdeg ▸ le_max_right _ _
  have hQ2of : P.natDegree ≤ 1 → Q.natDegree = 2 := fun h => by
    rcases le_total P.natDegree Q.natDegree with h' | h'
    · rwa [max_eq_right h'] at hdeg
    · rw [max_eq_left h'] at hdeg; omega
  rcases hz with hnc | ⟨hPc, hSc⟩
  · obtain ⟨z, hzi, hzP, hzS⟩ : ∃ z, Irreducible z ∧ z ∣ P ∧ z ∣ S := by
      by_contra h
      push Not at h
      exact hnc (isCoprime_of_irreducible_dvd (fun h' => hP0 h'.1) h)
    obtain ⟨a, ha⟩ := exists_root (Irreducible.natDegree_pos hzi)
    have hroot : ∀ {F : (↥Qbar)[X]}, z ∣ F → F.IsRoot a := fun ⟨w, hw⟩ => by
      rw [hw, IsRoot, eval_mul, ha.eq_zero, zero_mul]
    obtain ⟨m, hPm, hmd⟩ := divroot P (hroot hzP)
    obtain ⟨r, hSr, hrd⟩ := divroot S (hroot hzS)
    have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hPm; exact hP0 hPm
    have hua := sub_ne_zero' hu a
    have hmu := aeval_ne_zero hu hm0
    have hu0 := u_ne_zero hu
    have e : aeval u Q * aeval u S / (u * aeval u P) = aeval u Q * aeval u r / (u * aeval u m) := by
      rw [hPm, hSr]
      simp only [map_mul, map_sub, aeval_X, aeval_C, am]
      field_simp
    rw [e]
    refine core hu hm0 (by omega) (by omega) hQ2 (by rw [hPm] at hcop; exact hcop.of_mul_left_right)
      (fun h => hQ2of (by omega)) (fun k hk => hSP k ?_)
    rw [hSr, hPm, hk]
    ring
  · exact core hu hP0 (deg1 hP2 hPc) (deg1 hS hSc) hQ2 hcop (fun h => hQ2of (by omega)) hSP
