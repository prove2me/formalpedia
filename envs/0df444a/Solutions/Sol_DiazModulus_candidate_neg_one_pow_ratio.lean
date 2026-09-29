-- Prove2me | solution 1 for DiazModulus.candidate_neg_one_pow_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:37:42.562092+00:00
-- url     : https://prove2.me/submissions/74c2ce0a-321f-4404-8c0c-68c304f74091

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_conj_ratio_multiplier_relation
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open Complex ComplexConjugate

namespace NegOnePowRatio

/-- Complex conjugation as a `ℚ`-algebra map, used to transport algebraicity. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

theorem alg_I : IsAlgebraic ℚ Complex.I := by
  refine IsAlgebraic.of_pow (n := 2) two_pos ?_
  rw [Complex.I_sq]
  exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg

theorem ratAlg (q : ℚ) : IsAlgebraic ℚ (q : ℂ) := isAlgebraic_ratCast ℚ q

/-- `u ū = |u|²`. -/
theorem mul_conj_eq (u : ℂ) : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

/-- For a candidate, `u ū` is algebraic. -/
theorem mul_conj_alg {u : ℂ} (hu : DiazModulus.IsCandidate u) :
    IsAlgebraic ℚ (u * conj u) := by
  rw [mul_conj_eq]; exact hu.2.1.pow 2

/-- A candidate is off the real axis (otherwise `u = ±|u|` is algebraic; Hermite–Lindemann). -/
theorem im_ne_zero {u : ℂ} (hu : DiazModulus.IsCandidate u) : u.im ≠ 0 := by
  obtain ⟨hu0, hn, he⟩ := hu
  intro h
  have hcu : conj u = u := Complex.conj_eq_iff_im.2 h
  have hsq : u ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [← mul_conj_eq, hcu, sq]
  have halg : IsAlgebraic ℚ u :=
    IsAlgebraic.of_pow two_pos (by rw [hsq]; exact hn.pow 2)
  exact DiazModulus.hermite_lindemann_holds u hu0 halg he

/-- A candidate is off the imaginary axis (otherwise `u = ±i|u|` is algebraic). -/
theorem re_ne_zero {u : ℂ} (hu : DiazModulus.IsCandidate u) : u.re ≠ 0 := by
  obtain ⟨hu0, hn, he⟩ := hu
  intro h
  have hcu : conj u = -u := by
    apply Complex.ext <;> simp [h]
  have hsq : u ^ 2 = -((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [← mul_conj_eq, hcu]; ring
  have halg : IsAlgebraic ℚ u :=
    IsAlgebraic.of_pow two_pos (by rw [hsq]; exact (hn.pow 2).neg)
  exact DiazModulus.hermite_lindemann_holds u hu0 halg he

theorem re_im_zero {x y : ℝ} (h : (x : ℂ) + (y : ℂ) * Complex.I = 0) : x = 0 ∧ y = 0 := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp at h1 h2
  exact ⟨h1, h2⟩

/-- A nontrivial relation `a ρ + b z + c z̄ = 0` (`ρ = u ū`, `u ≠ 0`) with `Im z ≠ 0` has
`b = c ≠ 0`, and then `a ρ + 2 b Re z = 0`. -/
theorem rel_re {u z : ℂ} {a b c : ℚ} (hu : u ≠ 0) (hne : ¬(a = 0 ∧ b = 0 ∧ c = 0))
    (hrel : (a : ℂ) * (u * conj u) + (b : ℂ) * z + (c : ℂ) * conj z = 0) (hY : z.im ≠ 0) :
    b ≠ 0 ∧ (a : ℂ) * (u * conj u) + 2 * (b : ℂ) * ((z.re : ℝ) : ℂ) = 0 := by
  have hρ : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := mul_conj_eq u
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
  have hcz : conj z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have key : (((a : ℝ) * ‖u‖ ^ 2 + ((b : ℝ) + (c : ℝ)) * z.re : ℝ) : ℂ)
      + ((((b : ℝ) - (c : ℝ)) * z.im : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination hrel - (a : ℂ) * hρ - (b : ℂ) * hz - (c : ℂ) * hcz
  obtain ⟨hre, him⟩ := re_im_zero key
  have hbc : b = c := by
    have : (b : ℝ) - (c : ℝ) = 0 := (mul_eq_zero.1 him).resolve_right hY
    exact_mod_cast sub_eq_zero.1 this
  subst hbc
  have hb : b ≠ 0 := by
    intro hb0
    apply hne
    refine ⟨?_, hb0, hb0⟩
    rw [hb0] at hre
    have h1 : (a : ℝ) * ‖u‖ ^ 2 = 0 := by simpa using hre
    have hnu : ‖u‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hu)
    exact_mod_cast (mul_eq_zero.1 h1).resolve_right hnu
  refine ⟨hb, ?_⟩
  have hreC := congrArg (fun x : ℝ => (x : ℂ)) hre
  push_cast at hreC
  linear_combination hreC + (a : ℂ) * hρ

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`. -/
theorem trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra ℚ ℂ} {x : ℂ} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) y) :
    Algebra.trdeg ℚ ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin ℚ ({x'} : Set ↥B))
      = Algebra.adjoin ℚ ({x} : Set ℂ) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ≃ₐ[ℚ] ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* ℂ)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({x'} : Set ↥B)

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {x z : ℂ} : z ∈ E x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem self_mem_E (x : ℂ) : x ∈ E x := by
  rw [mem_E_iff]
  have h : x = algebraMap ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ
      ⟨x, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem inv_mem_E {x z : ℂ} (h : z ∈ E x) : z⁻¹ ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact h.inv

theorem mem_E_of_mul {x z : ℂ} (hx : x ≠ 0) (h : x * z ∈ E x) : z ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hx) (mem_E_iff.1 (self_mem_E x)) h

theorem mem_E_of_sq {x z : ℂ} (h : z ^ 2 ∈ E x) : z ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_pow two_pos h

end NegOnePowRatio

open NegOnePowRatio in
/-- With `w₀ = πi` and `s = u/ū`: if `e^{s w₀}` were algebraic, the multiplier relation for
`(u, w₀)` would give `π·Im u = aρ/(2b)`, so `u`, `ū`, `w₀` and `s w₀` would all be algebraic
over `ℚ[πi]`. Four exponentials (transcendence degree one) on `[[s w₀, w₀], [u, ū]]` then
forces a rational relation, which is impossible off the axes. -/
theorem solution (u : ℂ) (hu : DiazModulus.IsCandidate u) :
    Transcendental ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I * u / conj u)) := by
  intro hs
  have hu0 := hu.1
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hre := re_ne_zero hu
  have him := im_ne_zero hu
  have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set w₀ : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hw₀
  have hw₀0 : w₀ ≠ 0 := mul_ne_zero hπ Complex.I_ne_zero
  have hw₀re : w₀.re = 0 := by rw [hw₀]; simp
  have hw₀im : w₀.im = Real.pi := by rw [hw₀]; simp
  have hew₀ : IsAlgebraic ℚ (Complex.exp w₀) := by
    rw [hw₀, Complex.exp_pi_mul_I]; exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
  -- Step 1: the multiplier relation for `w₀ = πi`
  have hsw : IsAlgebraic ℚ (Complex.exp (u * w₀ / conj u)) := by
    have e : u * w₀ / conj u = w₀ * u / conj u := by ring
    rw [e]; exact hs
  obtain ⟨a, b, c, hne, hrel⟩ :=
    DiazModulus.conj_ratio_multiplier_relation u w₀ hre him hu.2.2 hew₀ hsw
  have hzre : (u * w₀).re = -(Real.pi * u.im) := by
    rw [Complex.mul_re, hw₀re, hw₀im]; ring
  have hzim : (u * w₀).im = Real.pi * u.re := by
    rw [Complex.mul_im, hw₀re, hw₀im]; ring
  have hY : (u * w₀).im ≠ 0 := by rw [hzim]; exact mul_ne_zero Real.pi_ne_zero hre
  obtain ⟨hb0, hX⟩ := rel_re hu0 hne hrel hY
  rw [hzre] at hX
  -- `w₀ · Im u = a ρ i / (2b)` is algebraic
  have hb2 : ((2 * b : ℚ) : ℂ) ≠ 0 := by
    push_cast; exact mul_ne_zero two_ne_zero (by exact_mod_cast hb0)
  have hθw : w₀ * ((u.im : ℝ) : ℂ)
      = (a : ℂ) * (u * conj u) * Complex.I / ((2 * b : ℚ) : ℂ) := by
    rw [eq_div_iff hb2, hw₀]
    push_cast at hX ⊢
    linear_combination (-Complex.I) * hX
  -- Step 2: everything lies in `E w₀`, the numbers algebraic over `ℚ[πi]`
  have hρE : u * conj u ∈ E w₀ := mem_E_of_alg (mul_conj_alg hu)
  have hIE : Complex.I ∈ E w₀ := mem_E_of_alg alg_I
  have hθE : ((u.im : ℝ) : ℂ) ∈ E w₀ := by
    refine mem_E_of_mul hw₀0 ?_
    rw [hθw, div_eq_mul_inv]
    exact mul_mem (mul_mem (mul_mem (mem_E_of_alg (ratAlg a)) hρE) hIE)
      (mem_E_of_alg (ratAlg (2 * b)).inv)
  have htE : ((u.re : ℝ) : ℂ) ∈ E w₀ := by
    refine mem_E_of_sq ?_
    have e : ((u.re : ℝ) : ℂ) ^ 2 = u * conj u - ((u.im : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_apply]; push_cast; ring
    rw [e]
    exact sub_mem hρE (pow_mem hθE 2)
  have huE : u ∈ E w₀ := by
    rw [← Complex.re_add_im u]
    exact add_mem htE (mul_mem hθE hIE)
  have hcuE : conj u ∈ E w₀ := by
    have e : conj u = ((u.re : ℝ) : ℂ) - ((u.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e]
    exact sub_mem htE (mul_mem hθE hIE)
  have h11E : w₀ * u / conj u ∈ E w₀ := by
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (self_mem_E w₀) huE) (inv_mem_E hcuE)
  -- the transcendence degree is at most one
  have htr : Algebra.trdeg ℚ
      ↥(Algebra.adjoin ℚ ({w₀ * u / conj u, w₀, u, conj u} : Set ℂ)) ≤ 1 := by
    have hxB : w₀ ∈ Algebra.adjoin ℚ ({w₀ * u / conj u, w₀, u, conj u} : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    refine trdeg_le_one_of_adjoin_singleton hxB ?_
    have hle : Algebra.adjoin ℚ ({w₀ * u / conj u, w₀, u, conj u} : Set ℂ) ≤ E w₀ := by
      refine Algebra.adjoin_le ?_
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h | h <;> rw [h, SetLike.mem_coe]
      exacts [h11E, self_mem_E w₀, huE, hcuE]
    intro y hy
    exact mem_E_iff.1 (hle hy)
  -- four exponentials on `[[s w₀, w₀], [u, ū]]`
  have h110 : w₀ * u / conj u ≠ 0 := div_ne_zero (mul_ne_zero hw₀0 hu0) hcu
  have hdet : w₀ * u / conj u * conj u = w₀ * u := div_mul_cancel₀ _ hcu
  rcases DiazModulus.four_exponentials_trdeg_one (w₀ * u / conj u) w₀ u (conj u)
      hs hew₀ hu.2.2 (exp_conj_alg hu.2.2) h110 hw₀0 hu0 hcu hdet htr with
    ⟨p, q, hpq, -, h2⟩ | ⟨p, q, hpq, -, h2⟩
  · -- rows: `p w₀ + q ū = 0`; the real part gives `q Re u = 0`
    have hre2 := congrArg Complex.re h2
    have e : (↑p * w₀ + ↑q * conj u).re = (q : ℝ) * u.re := by simp [hw₀re, hw₀im]
    rw [e, Complex.zero_re] at hre2
    have hq : q = 0 := by exact_mod_cast (mul_eq_zero.1 hre2).resolve_right hre
    rw [hq, Rat.cast_zero, zero_mul, add_zero] at h2
    have hp : p = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right hw₀0
    exact hpq ⟨hp, hq⟩
  · -- columns: `p u + q ū = 0`, impossible off the axes
    have hre2 := congrArg Complex.re h2
    have him2 := congrArg Complex.im h2
    simp at hre2 him2
    have h3 : ((p + q : ℚ) : ℝ) * u.re = 0 := by push_cast; linear_combination hre2
    have h4 : ((p - q : ℚ) : ℝ) * u.im = 0 := by push_cast; linear_combination him2
    have h5 : p + q = 0 := by exact_mod_cast (mul_eq_zero.1 h3).resolve_right hre
    have h6 : p - q = 0 := by exact_mod_cast (mul_eq_zero.1 h4).resolve_right him
    exact hpq ⟨by linarith, by linarith⟩

#print axioms solution
