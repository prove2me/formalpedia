-- Prove2me | solution 1 for DiazModulus.aligned_norm_free_no_rational_log_matrix
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-13T09:28:21.123496+00:00
-- url     : https://prove2.me/submissions/ecd73626-3ae1-402b-9a69-ba51bbe322aa

import Mathlib
import Definitions.Def_DiazModulus

section
-- inlined from DZ_LEAFSPLIT_core

/-!
# A period split of the irrational-angle leaf, and the degeneracy of the same split on the
# real-generic leaf.

Nothing here is claimed as new mathematics.  Every statement is elementary once the
parametrisation `u = Log α + 2πi n` is written down.

`HermiteLindemann` and the transcendence of `π` are taken as **explicit hypotheses**
wherever they are needed, never imported, so `#print axioms` stays clean.
-/

open Complex ComplexConjugate

namespace DiazLeafSplit

open DiazModulus

/-! ## 0. Algebraicity bookkeeping -/

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ Qbar := mem_Qbar_iff.symm

theorem alg_rat (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q)

theorem alg_int (n : ℤ) : IsAlgebraic ℚ ((n : ℂ)) := by
  simpa using alg_rat (n : ℚ)

/-- Complex conjugation as a `ℚ`-algebra map, used only to transport algebraicity. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem alg_div {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z / w) := by
  rw [alg_iff_mem] at *
  exact Subfield.div_mem _ hz hw

theorem alg_mul {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z * w) := by
  rw [alg_iff_mem] at *
  exact Subfield.mul_mem _ hz hw

theorem alg_neg {z : ℂ} (hz : IsAlgebraic ℚ z) : IsAlgebraic ℚ (-z) := by
  rw [alg_iff_mem] at *
  exact Subfield.neg_mem _ hz

theorem alg_pow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℕ) : IsAlgebraic ℚ (z ^ n) := by
  rw [alg_iff_mem] at *
  exact Subfield.pow_mem _ hz n

/-! ## 1. The two leaves and the split predicate -/

/-- **Leaf 1**, `DiazModulus.diaz_of_exp_real_generic`, verbatim. -/
def Leaf1 : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
    u.im ≠ 0 → Complex.exp u ≠ 1 → u.re ≠ 0 → Transcendental ℚ (Complex.exp u)

/-- **Leaf 2**, `DiazModulus.diaz_of_exp_not_real_irrational_angle`, verbatim. -/
def Leaf2 : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    Transcendental ℚ (Complex.exp u)

/-- **The split predicate.**  `π (Im u + r π)` is algebraic for some non-zero rational `r`.

Geometrically (`period_aligned_iff_fibre` below): some non-zero rational multiple of `u`
has a *second* point of algebraic modulus in its exponential fibre. -/
def PeriodAligned (u : ℂ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)

/-- Leaf 2 restricted to the period-aligned half. -/
def Leaf2Aligned : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    Transcendental ℚ (Complex.exp u)

/-- Leaf 2 restricted to the period-free half. -/
def Leaf2Free : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (¬ ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    Transcendental ℚ (Complex.exp u)

/-! ## 2. The reduction: the two halves are exactly leaf 2 -/

theorem leaf2_of_halves (hA : Leaf2Aligned) (hB : Leaf2Free) : Leaf2 := by
  intro u hu0 hmod hnr hax hirr
  by_cases h : ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)
  · exact hA u hu0 hmod hnr hax hirr h
  · exact hB u hu0 hmod hnr hax hirr h

theorem aligned_of_leaf2 (h : Leaf2) : Leaf2Aligned :=
  fun u a b c d e _ => h u a b c d e

theorem free_of_leaf2 (h : Leaf2) : Leaf2Free :=
  fun u a b c d e _ => h u a b c d e

theorem leaf2_iff_halves : Leaf2 ↔ (Leaf2Aligned ∧ Leaf2Free) :=
  ⟨fun h => ⟨aligned_of_leaf2 h, free_of_leaf2 h⟩, fun h => leaf2_of_halves h.1 h.2⟩

end DiazLeafSplit

namespace DiazLeafSplit

open DiazModulus

/-! ## 3. The route lemma: a period-aligned counterexample puts an algebraic multiple of
`1/(iπ)` into `ℒ`. -/

theorem recip_pi_of_aligned_candidate (u : ℂ)
    (hirr : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi)
    (hal : PeriodAligned u)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) :
    ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ γ ≠ 0 ∧
      IsAlgebraic ℚ (Complex.exp (γ / ((Real.pi : ℂ) * Complex.I))) := by
  obtain ⟨r, hr0, halg⟩ := hal
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπC : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ0
  set s : ℝ := u.im + (r : ℝ) * Real.pi with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    refine hirr ⟨-r, ?_⟩
    have : u.im = -((r : ℝ) * Real.pi) := by rw [hs_def] at h; linarith
    push_cast
    linarith [this]
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  set ν : ℂ := Complex.I * ((s : ℝ) : ℂ) with hν_def
  have hν0 : ν ≠ 0 := mul_ne_zero Complex.I_ne_zero hsC
  -- the exponential of `ν` is algebraic
  have hdenne : ((r.den : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
  have hmul : (((2 * r.den : ℕ)) : ℂ) * ν =
      ((r.den : ℕ) : ℂ) * (u - conj u) + ((r.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.sub_conj, hν_def, hs_def]
    push_cast [Rat.cast_def]
    field_simp
  have hkey : Complex.exp ν ^ (2 * r.den) =
      (Complex.exp u / conj (Complex.exp u)) ^ r.den := by
    rw [← Complex.exp_nat_mul, hmul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
      mul_one, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_conj]
  have hexpν : IsAlgebraic ℚ (Complex.exp ν) := by
    refine IsAlgebraic.of_pow (n := 2 * r.den) (by positivity) ?_
    rw [hkey]
    exact alg_pow (alg_div hexp (alg_conj hexp)) r.den
  refine ⟨-(((Real.pi * s : ℝ)) : ℂ), alg_neg (by rw [hs_def] at halg ⊢; exact halg), ?_, ?_⟩
  · simp only [neg_ne_zero, Complex.ofReal_ne_zero]
    exact mul_ne_zero hπ0 hs0
  · have : -(((Real.pi * s : ℝ)) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I) = ν := by
      rw [hν_def]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
    rw [this]
    exact hexpν

end DiazLeafSplit

namespace DiazLeafSplit

open DiazModulus

/-! ## 4. `π` is not a root of a non-zero rational quadratic with algebraic constant term -/

theorem pi_not_quadratic (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {r b : ℚ} (hr : r ≠ 0)
    (h : IsAlgebraic ℚ ((b : ℂ) * ((Real.pi : ℝ) : ℂ) + (r : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2)) :
    False := by
  obtain ⟨p, hp0, hpc⟩ := h
  set g : Polynomial ℚ := Polynomial.C b * Polynomial.X + Polynomial.C r * Polynomial.X ^ 2
    with hg
  have hgdeg : g.natDegree = 2 := by
    rw [hg]; compute_degree!
  have hgnc : g ≠ Polynomial.C (g.coeff 0) := by
    intro hcon
    have : g.natDegree = 0 := by rw [hcon]; exact Polynomial.natDegree_C _
    omega
  refine hpi ⟨p.comp g, ?_, ?_⟩
  · rw [Ne, Polynomial.comp_eq_zero_iff]
    rintro (h | ⟨-, h⟩)
    · exact hp0 h
    · exact hgnc h
  · rw [Polynomial.aeval_comp]
    have : (Polynomial.aeval (((Real.pi : ℝ) : ℂ)) g)
        = (b : ℂ) * ((Real.pi : ℝ) : ℂ) + (r : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by
      rw [hg]; simp
    rw [this, hpc]

/-! ## 5. The real branch: the split predicate holds there, and is void there -/

theorem im_mem_pi_int {u : ℂ} (hexp : (Complex.exp u).im = 0) :
    ∃ k : ℤ, u.im = (k : ℝ) * Real.pi := by
  have h := Complex.exp_im u
  rw [hexp] at h
  have hs : Real.sin u.im = 0 := by
    rcases mul_eq_zero.1 h.symm with h1 | h1
    · exact absurd h1 (Real.exp_ne_zero _)
    · exact h1
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  exact ⟨n, hn.symm⟩

/-- On leaf 1's ambient class the split predicate is **always true**: the witnessing
translate is the complex conjugate, and it contributes nothing. -/
theorem realBranch_periodAligned {u : ℂ} (hexp : (Complex.exp u).im = 0) (him : u.im ≠ 0) :
    PeriodAligned u := by
  obtain ⟨k, hk⟩ := im_mem_pi_int hexp
  have hk0 : (k : ℚ) ≠ 0 := by
    intro h
    apply him
    have : (k : ℝ) = 0 := by exact_mod_cast h
    rw [hk, this, zero_mul]
  refine ⟨-(k : ℚ), neg_ne_zero.2 hk0, ?_⟩
  have hz : (Real.pi * (u.im + ((-(k : ℚ) : ℚ) : ℝ) * Real.pi) : ℝ) = 0 := by
    push_cast
    rw [hk]; ring
  rw [hz]
  simpa using (isAlgebraic_zero (R := ℚ) (A := ℂ))

/-- **The degeneracy.**  On leaf 1's ambient class every witness `r` of the split predicate
has `Im u + r π = 0`, so the number `ν = i(Im u + rπ)` that carries the whole content of the
split on leaf 2 is identically zero on leaf 1. -/
theorem realBranch_period_degenerate (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {u : ℂ} (hexp : (Complex.exp u).im = 0) {r : ℚ}
    (halg : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    u.im + (r : ℝ) * Real.pi = 0 := by
  obtain ⟨k, hk⟩ := im_mem_pi_int hexp
  by_cases hkr : ((k : ℚ) + r) = 0
  · have : (k : ℝ) + (r : ℝ) = 0 := by exact_mod_cast hkr
    rw [hk]; linear_combination Real.pi * this
  · exfalso
    have heq : ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)
        = (0 : ℚ) * ((Real.pi : ℝ) : ℂ) + (((k : ℚ) + r : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by
      rw [hk]; push_cast; ring
    rw [heq] at halg
    exact pi_not_quadratic hpi hkr halg

end DiazLeafSplit


namespace DiazLeafSplit

open DiazModulus

/-! ## 6. Both halves of the split are non-empty, with explicit witnesses.

`wA = √(16 − yA²) + i·yA` with `yA = 1/π − π`: modulus `4`, and `‖wA + 2πi‖ = 2√5`.
`wB = √15 + i`: modulus `4`. -/

theorem exp_im_ne_zero_of_not_pi_rat {u : ℂ}
    (h : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) : (Complex.exp u).im ≠ 0 := by
  intro hc
  obtain ⟨k, hk⟩ := im_mem_pi_int hc
  exact h ⟨(k : ℚ), by push_cast; exact hk⟩

noncomputable def yA : ℝ := 1 / Real.pi - Real.pi

theorem pi_pos' : (0 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]

theorem yA_sq_lt : yA ^ 2 < 16 := by
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have h4 : Real.pi < 4 := Real.pi_lt_four
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  have ht : (1 / Real.pi) * Real.pi = 1 := by field_simp
  have ht0 : 0 < 1 / Real.pi := by positivity
  have ht3 : 1 / Real.pi < 1 / 3 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
  have hexp : yA ^ 2 = (1 / Real.pi) ^ 2 - 2 + Real.pi ^ 2 := by
    unfold yA; nlinarith [ht]
  nlinarith [hexp, ht0, ht3]

noncomputable def wA : ℂ := ⟨Real.sqrt (16 - yA ^ 2), yA⟩
noncomputable def wB : ℂ := ⟨Real.sqrt 15, 1⟩

theorem norm_wA : ‖wA‖ = 4 := by
  have h1 : (0 : ℝ) ≤ 16 - yA ^ 2 := by linarith [yA_sq_lt]
  have h2 : Complex.normSq wA = 16 := by
    rw [wA, Complex.normSq_mk, Real.mul_self_sqrt h1]; ring
  have h3 : ‖wA‖ ^ 2 = 16 := by rw [← Complex.normSq_eq_norm_sq, h2]
  nlinarith [norm_nonneg wA, h3]

theorem norm_wB : ‖wB‖ = 4 := by
  have h2 : Complex.normSq wB = 16 := by
    rw [wB, Complex.normSq_mk, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 15)]; ring
  have h3 : ‖wB‖ ^ 2 = 16 := by rw [← Complex.normSq_eq_norm_sq, h2]
  nlinarith [norm_nonneg wB, h3]

theorem wA_re_pos : 0 < wA.re := by
  have h1 : (0 : ℝ) < 16 - yA ^ 2 := by linarith [yA_sq_lt]
  simpa [wA] using Real.sqrt_pos.2 h1

theorem yA_neg : yA < 0 := by
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  have ht3 : 1 / Real.pi < 1 / 3 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
  unfold yA; linarith

theorem wA_not_pi_rat (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    ¬ ∃ q : ℚ, wA.im = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  have hy : (1 / Real.pi - Real.pi) = (q : ℝ) * Real.pi := hq
  have h1 : (1 / Real.pi) * Real.pi = 1 := by field_simp
  have hmul : (1 / Real.pi - Real.pi) * Real.pi = ((q : ℝ) * Real.pi) * Real.pi := by rw [hy]
  have hkey : ((q : ℝ) + 1) * Real.pi ^ 2 = 1 := by nlinarith [hmul, h1]
  by_cases hq1 : (q : ℚ) + 1 = 0
  · have hz : ((q : ℝ) + 1) = 0 := by exact_mod_cast hq1
    rw [hz] at hkey; norm_num at hkey
  · refine pi_not_quadratic hpi (r := q + 1) (b := 0) hq1 ?_
    have hval : ((0 : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ)
        + (((q + 1 : ℚ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 = 1 := by
      have hcast : ((((q : ℝ) + 1) * Real.pi ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hkey]
      push_cast at hcast ⊢
      linear_combination hcast
    rw [hval]
    simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))

theorem wB_not_pi_rat (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    ¬ ∃ q : ℚ, wB.im = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  have hy : (1 : ℝ) = (q : ℝ) * Real.pi := hq
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  have hq0 : (q : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hy; norm_num at hy
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq0
  have hval : Real.pi = ((1 / q : ℚ) : ℝ) := by
    push_cast
    field_simp
    linarith [hy]
  refine hpi ?_
  rw [hval]
  have : (((((1 / q : ℚ)) : ℝ)) : ℂ) = (((1 / q : ℚ)) : ℂ) := by push_cast; ring
  rw [this]
  exact alg_rat _

/-- The period-aligned half is non-empty. -/
theorem wA_mem_aligned (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wA ≠ 0 ∧ IsAlgebraic ℚ ((‖wA‖ : ℝ) : ℂ) ∧ (Complex.exp wA).im ≠ 0 ∧
      ¬ (wA.im = 0 ∨ wA.re = 0) ∧ (¬ ∃ q : ℚ, wA.im = (q : ℝ) * Real.pi) ∧
      PeriodAligned wA := by
  have hre : wA.re ≠ 0 := ne_of_gt wA_re_pos
  have him : wA.im ≠ 0 := ne_of_lt yA_neg
  refine ⟨?_, ?_, exp_im_ne_zero_of_not_pi_rat (wA_not_pi_rat hpi), ?_,
    wA_not_pi_rat hpi, ⟨1, one_ne_zero, ?_⟩⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rw [norm_wA]
    have : (((4 : ℝ)) : ℂ) = ((4 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  · rintro (h | h)
    · exact him h
    · exact hre h
  · have hpos : (0 : ℝ) < Real.pi := pi_pos'
    have hne : Real.pi ≠ 0 := ne_of_gt hpos
    have hz : (Real.pi * (wA.im + ((1 : ℚ) : ℝ) * Real.pi) : ℝ) = 1 := by
      have hw : wA.im = 1 / Real.pi - Real.pi := rfl
      rw [hw]
      have hsimp : (1 / Real.pi - Real.pi + ((1 : ℚ) : ℝ) * Real.pi) = 1 / Real.pi := by
        push_cast; ring
      rw [hsimp]
      field_simp
    rw [hz]
    have : (((1 : ℝ)) : ℂ) = ((1 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _

/-- The period-free half is non-empty. -/
theorem wB_mem_free (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wB ≠ 0 ∧ IsAlgebraic ℚ ((‖wB‖ : ℝ) : ℂ) ∧ (Complex.exp wB).im ≠ 0 ∧
      ¬ (wB.im = 0 ∨ wB.re = 0) ∧ (¬ ∃ q : ℚ, wB.im = (q : ℝ) * Real.pi) ∧
      ¬ PeriodAligned wB := by
  have hre : wB.re ≠ 0 := by
    have : wB.re = Real.sqrt 15 := rfl
    rw [this]
    exact ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have him : wB.im ≠ 0 := by
    have : wB.im = 1 := rfl
    rw [this]; norm_num
  refine ⟨?_, ?_, exp_im_ne_zero_of_not_pi_rat (wB_not_pi_rat hpi), ?_,
    wB_not_pi_rat hpi, ?_⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rw [norm_wB]
    have : (((4 : ℝ)) : ℂ) = ((4 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  · rintro (h | h)
    · exact him h
    · exact hre h
  · rintro ⟨r, hr0, halg⟩
    refine pi_not_quadratic hpi (r := r) (b := 1) hr0 ?_
    have hb : wB.im = 1 := rfl
    have hz : ((Real.pi * (wB.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)
        = ((1 : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) + ((r : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by
      rw [hb]; push_cast; ring
    rw [hz] at halg
    exact halg

end DiazLeafSplit

namespace DiazLeafSplit

open DiazModulus

/-! ## 7. Leaf 1 collapses, under rational scaling, to the single normalised line `Im u = π`. -/

theorem alg_of_zpow {z : ℂ} (_hz : z ≠ 0) {k : ℤ} (hk : k ≠ 0)
    (h : IsAlgebraic ℚ (z ^ k)) : IsAlgebraic ℚ z := by
  have hm : (0 : ℕ) < k.natAbs := Int.natAbs_pos.2 hk
  have hpow : IsAlgebraic ℚ (z ^ k.natAbs) := by
    rcases Int.natAbs_eq k with he | he
    · rw [he, zpow_natCast] at h; exact h
    · rw [he, zpow_neg, zpow_natCast] at h
      rw [alg_iff_mem] at h ⊢
      have := Subfield.inv_mem Qbar h
      rwa [inv_inv] at this
  exact IsAlgebraic.of_pow hm hpow

/-- Leaf 1 restricted to the line `Im u = π`. -/
def Leaf1Normalised : Prop :=
  ∀ u : ℂ, IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → u.im = Real.pi → u.re ≠ 0 →
    Transcendental ℚ (Complex.exp u)

theorem normalised_of_leaf1 (h : Leaf1) : Leaf1Normalised := by
  intro u hmod him hre
  refine h u ?_ hmod ?_ ?_ ?_ hre
  · intro hc; exact hre (by rw [hc]; rfl)
  · rw [Complex.exp_im, him, Real.sin_pi, mul_zero]
  · rw [him]; exact ne_of_gt pi_pos'
  · intro hc
    have h1 : (Complex.exp u).re = Real.exp u.re * Real.cos u.im := Complex.exp_re u
    rw [hc, him, Real.cos_pi] at h1
    have h2 : ((1 : ℂ)).re = 1 := Complex.one_re
    rw [h2] at h1
    nlinarith [Real.exp_pos u.re, h1]

theorem leaf1_of_normalised (h : Leaf1Normalised) : Leaf1 := by
  intro u hu0 hmod hexp him hne1 hre
  obtain ⟨k, hk⟩ := im_mem_pi_int hexp
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact him (by rw [hk]; norm_num)
  have hkR : ((k : ℝ)) ≠ 0 := Int.cast_ne_zero.2 hk0
  have hkQ : ((k : ℚ)) ≠ 0 := Int.cast_ne_zero.2 hk0
  set c : ℝ := ((k : ℝ))⁻¹ with hc
  set v : ℂ := (c : ℂ) * u with hvdef
  have hvim : v.im = Real.pi := by
    rw [hvdef, Complex.im_ofReal_mul, hk, hc]
    field_simp
  have hvre : v.re ≠ 0 := by
    rw [hvdef, Complex.re_ofReal_mul]
    exact mul_ne_zero (by rw [hc]; exact inv_ne_zero hkR) hre
  have hvmod : IsAlgebraic ℚ ((‖v‖ : ℝ) : ℂ) := by
    have h2 : ((|(1 / (k : ℚ))| : ℚ) : ℝ) = |c| := by
      rw [hc]; push_cast; rw [abs_inv, one_div, abs_inv]
    have h1 : ‖v‖ = ((|(1 / (k : ℚ))| : ℚ) : ℝ) * ‖u‖ := by
      rw [h2, hvdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hcc : ((((|(1 / (k : ℚ))| : ℚ) : ℝ)) : ℂ) = ((|(1 / (k : ℚ))| : ℚ) : ℂ) := by
      norm_cast
    rw [h1, Complex.ofReal_mul, hcc]
    exact alg_mul (alg_rat _) hmod
  intro halg
  refine h v hvmod hvim hvre ?_
  refine alg_of_zpow (Complex.exp_ne_zero v) hk0 ?_
  have hexpv : Complex.exp v ^ (k : ℤ) = Complex.exp u := by
    rw [← Complex.exp_int_mul]
    congr 1
    rw [hvdef, hc]
    push_cast
    field_simp
  rw [hexpv]
  exact halg

theorem leaf1_iff_normalised : Leaf1 ↔ Leaf1Normalised :=
  ⟨normalised_of_leaf1, leaf1_of_normalised⟩

end DiazLeafSplit

namespace DiazLeafSplit

open DiazModulus

/-! ## 8. The geometric reading of the split predicate.

`PeriodAligned u` says exactly that some non-zero rational multiple of `u` has a *second*
point of algebraic modulus in its exponential fibre — the configuration of
`Diaz.fibre_at_most_two` and `Diaz.nonreal_two_point_fibre_pi_sq`. -/

theorem alg_norm_iff_normSq (z : ℂ) :
    IsAlgebraic ℚ ((‖z‖ : ℝ) : ℂ) ↔ IsAlgebraic ℚ ((Complex.normSq z : ℝ) : ℂ) := by
  have hsq : ((Complex.normSq z : ℝ) : ℂ) = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  constructor
  · intro h; rw [hsq]; exact alg_pow h 2
  · intro h
    refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
    rw [← hsq]; exact h

theorem normSq_translate (u : ℂ) (q : ℚ) (n : ℤ) :
    Complex.normSq ((q : ℂ) * u + 2 * ((Real.pi : ℝ) : ℂ) * (n : ℂ) * Complex.I)
      = (q : ℝ) ^ 2 * Complex.normSq u
        + 4 * (n : ℝ) * (Real.pi * ((q : ℝ) * u.im + Real.pi * (n : ℝ))) := by
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

theorem periodAligned_iff_fibre {u : ℂ} (hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) :
    PeriodAligned u ↔
      ∃ (q : ℚ) (n : ℤ), q ≠ 0 ∧ n ≠ 0 ∧
        IsAlgebraic ℚ ((‖(q : ℂ) * u + 2 * ((Real.pi : ℝ) : ℂ) * (n : ℂ) * Complex.I‖ : ℝ) : ℂ) := by
  have hns : IsAlgebraic ℚ ((Complex.normSq u : ℝ) : ℂ) := (alg_norm_iff_normSq u).1 hmod
  constructor
  · rintro ⟨r, hr0, halg⟩
    refine ⟨(r.den : ℚ), r.num, by exact_mod_cast r.den_nz, Rat.num_ne_zero.2 hr0, ?_⟩
    rw [alg_norm_iff_normSq, normSq_translate]
    have hrd : ((r.den : ℚ) : ℝ) * (r : ℝ) = (r.num : ℝ) := by
      have h0 : (r * (r.den : ℚ) : ℚ) = (r.num : ℚ) := Rat.mul_den_eq_num r
      have h1 : ((r * (r.den : ℚ) : ℚ) : ℝ) = ((r.num : ℚ) : ℝ) := by rw [h0]
      push_cast at h1 ⊢
      linarith [h1]
    have hden : ((r.den : ℚ) : ℝ) * u.im + Real.pi * (r.num : ℝ)
        = ((r.den : ℚ) : ℝ) * (u.im + (r : ℝ) * Real.pi) := by
      rw [← hrd]; ring
    have hcast : (((((r.den : ℚ) : ℝ) ^ 2 * Complex.normSq u
          + 4 * (r.num : ℝ) * (Real.pi * (((r.den : ℚ) : ℝ) * u.im + Real.pi * (r.num : ℝ)))) : ℝ) : ℂ)
        = ((r.den : ℚ) : ℂ) ^ 2 * ((Complex.normSq u : ℝ) : ℂ)
          + ((4 * r.num * r.den : ℚ) : ℂ)
            * ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) := by
      rw [hden]
      push_cast
      ring
    rw [hcast]
    exact (alg_iff_mem).2 (Subfield.add_mem _
      (Subfield.mul_mem _ (Subfield.pow_mem _ ((alg_iff_mem).1 (alg_rat _)) 2)
        ((alg_iff_mem).1 hns))
      (Subfield.mul_mem _ ((alg_iff_mem).1 (alg_rat _)) ((alg_iff_mem).1 halg)))
  · rintro ⟨q, n, hq0, hn0, halg⟩
    refine ⟨(n : ℚ) / q, div_ne_zero (by exact_mod_cast hn0) hq0, ?_⟩
    rw [alg_norm_iff_normSq, normSq_translate] at halg
    have hqR : ((q : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hq0
    have hnR : ((n : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.2 hn0
    have hid : Real.pi * (u.im + (((n : ℚ) / q : ℚ) : ℝ) * Real.pi)
        = (1 / (4 * (n : ℝ) * (q : ℝ)))
          * ((((q : ℚ) : ℝ) ^ 2 * Complex.normSq u
              + 4 * (n : ℝ) * (Real.pi * (((q : ℚ) : ℝ) * u.im + Real.pi * (n : ℝ))))
            - ((q : ℚ) : ℝ) ^ 2 * Complex.normSq u) := by
      push_cast
      field_simp
      ring
    rw [hid]
    have hcast : (((1 / (4 * (n : ℝ) * (q : ℝ)))
          * ((((q : ℚ) : ℝ) ^ 2 * Complex.normSq u
              + 4 * (n : ℝ) * (Real.pi * (((q : ℚ) : ℝ) * u.im + Real.pi * (n : ℝ))))
            - ((q : ℚ) : ℝ) ^ 2 * Complex.normSq u) : ℝ) : ℂ)
        = ((1 / (4 * (n : ℚ) * q) : ℚ) : ℂ)
          * (((((q : ℚ) : ℝ) ^ 2 * Complex.normSq u
              + 4 * (n : ℝ) * (Real.pi * (((q : ℚ) : ℝ) * u.im + Real.pi * (n : ℝ)))) : ℝ) : ℂ)
            - ((1 / (4 * (n : ℚ) * q) : ℚ) : ℂ) * ((q : ℚ) : ℂ) ^ 2
              * ((Complex.normSq u : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast]
    exact (alg_iff_mem).2 (Subfield.sub_mem _
      (Subfield.mul_mem _ ((alg_iff_mem).1 (alg_rat _)) ((alg_iff_mem).1 halg))
      (Subfield.mul_mem _ (Subfield.mul_mem _ ((alg_iff_mem).1 (alg_rat _))
        (Subfield.pow_mem _ ((alg_iff_mem).1 (alg_rat _)) 2)) ((alg_iff_mem).1 hns)))

end DiazLeafSplit

namespace DiazLeafSplit

open DiazModulus

/-! ## 9. The split predicate is invariant under the rational-scaling action.

This is what distinguishes it from the naive integer-translate version of the same split,
whose residual half is carried back onto the whole leaf by `u ↦ u/p`. -/

theorem periodAligned_ratMul {u : ℂ} {q : ℚ} (hq : q ≠ 0) :
    PeriodAligned ((q : ℂ) * u) ↔ PeriodAligned u := by
  have hqR : ((q : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hq
  have him : ((q : ℂ) * u).im = ((q : ℚ) : ℝ) * u.im := by
    simp
  constructor
  · rintro ⟨r, hr0, halg⟩
    refine ⟨r / q, div_ne_zero hr0 hq, ?_⟩
    have hid : (Real.pi * (u.im + ((r / q : ℚ) : ℝ) * Real.pi) : ℝ)
        = ((1 / q : ℚ) : ℝ) * (Real.pi * (((q : ℂ) * u).im + (r : ℝ) * Real.pi)) := by
      rw [him]; push_cast; field_simp
    rw [hid, Complex.ofReal_mul]
    have hcc : ((((1 / q : ℚ) : ℝ)) : ℂ) = ((1 / q : ℚ) : ℂ) := by norm_cast
    rw [hcc]
    exact alg_mul (alg_rat _) halg
  · rintro ⟨r, hr0, halg⟩
    refine ⟨r * q, mul_ne_zero hr0 hq, ?_⟩
    have hid : (Real.pi * (((q : ℂ) * u).im + ((r * q : ℚ) : ℝ) * Real.pi) : ℝ)
        = ((q : ℚ) : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)) := by
      rw [him]; push_cast; ring
    rw [hid, Complex.ofReal_mul]
    have hcc : ((((q : ℚ) : ℝ)) : ℂ) = ((q : ℚ) : ℂ) := by norm_cast
    rw [hcc]
    exact alg_mul (alg_rat _) halg

end DiazLeafSplit

end

section
-- inlined from DZ_ALIGNED_core

/-!
# Splitting the period-aligned leaf at the four-exponentials boundary.

Ambient class of the leaf `DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned`:
`u ≠ 0`, `‖u‖ ∈ Q̄`, `(exp u).im ≠ 0`, `Im u ≠ 0 ≠ Re u`, `Im u ∉ πℚ`, and
`π (Im u + rπ) ∈ Q̄` for some `r ∈ ℚ^×`.  Write `s = Im u + rπ`, `β = π s`, `A = ‖u‖²`.

The split predicate is `A ∈ ℚ·β`.  On that half the leaf follows from the **theorem of the
four exponentials**, taken here as an explicit hypothesis `FourExpDet` (it is a theorem of
Siegel–Lang–Ramachandra, not of Mathlib).  No other transcendence input is used.
-/

open Complex ComplexConjugate

namespace DiazAligned

open DiazModulus DiazLeafSplit

/-! ## 1. The four exponentials theorem, determinant form, as an explicit hypothesis. -/

-- **Four exponentials conjecture, determinant form.**  A `2 × 2` matrix
-- `![![l₁, l₂], ![l₃, l₄]]` whose four entries are logarithms of algebraic numbers, whose two
-- rows are `ℚ`-linearly independent and whose two columns are `ℚ`-linearly independent, has
-- non-zero determinant.  This is **4EC**, still open in general; it is *known* when the four
-- entries generate a field of transcendence degree at most one (Roy–Waldschmidt, ported to
-- this mission as `Diaz.four_exp_trdeg_one`).  Strictly weaker than the *strong* four
-- exponentials conjecture, which is what the aligned leaf needs in full.
def FourExpDet : Prop :=
  ∀ l₁ l₂ l₃ l₄ : ℂ,
    IsAlgebraic ℚ (Complex.exp l₁) → IsAlgebraic ℚ (Complex.exp l₂) →
    IsAlgebraic ℚ (Complex.exp l₃) → IsAlgebraic ℚ (Complex.exp l₄) →
    (∀ a b : ℚ, (a : ℂ) * l₁ + (b : ℂ) * l₃ = 0 → (a : ℂ) * l₂ + (b : ℂ) * l₄ = 0 →
      a = 0 ∧ b = 0) →
    (∀ a b : ℚ, (a : ℂ) * l₁ + (b : ℂ) * l₂ = 0 → (a : ℂ) * l₃ + (b : ℂ) * l₄ = 0 →
      a = 0 ∧ b = 0) →
    l₁ * l₄ - l₂ * l₃ ≠ 0

/-! ## 2. The split predicate and the two halves. -/

/-- `‖u‖²` is a **rational** multiple of the aligned datum `π (Im u + rπ)`. -/
def NormRatMult (u : ℂ) : Prop :=
  ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
    ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))

/-- The published leaf, verbatim. -/
def Aligned : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    Transcendental ℚ (Complex.exp u)

/-- Half A: the norm is a rational multiple of the aligned datum. -/
def AlignedRatMult : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    NormRatMult u →
    Transcendental ℚ (Complex.exp u)

/-- Half B: it is not. -/
def AlignedNormFree : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    ¬ NormRatMult u →
    Transcendental ℚ (Complex.exp u)

theorem aligned_of_halves (hA : AlignedRatMult) (hB : AlignedNormFree) : Aligned := by
  intro u h0 hmod hnr hax hirr hal
  by_cases h : NormRatMult u
  · exact hA u h0 hmod hnr hax hirr hal h
  · exact hB u h0 hmod hnr hax hirr hal h

theorem ratMult_of_aligned (h : Aligned) : AlignedRatMult :=
  fun u a b c d e f _ => h u a b c d e f

theorem normFree_of_aligned (h : Aligned) : AlignedNormFree :=
  fun u a b c d e f _ => h u a b c d e f

theorem aligned_iff_halves : Aligned ↔ (AlignedRatMult ∧ AlignedNormFree) :=
  ⟨fun h => ⟨ratMult_of_aligned h, normFree_of_aligned h⟩,
   fun h => aligned_of_halves h.1 h.2⟩


/-! ## 3. The rational-multiple half follows from the four exponentials theorem. -/

/-- A rational multiple of `2πi` is a logarithm of a root of unity. -/
theorem alg_exp_rat_two_pi_I (c : ℚ) :
    IsAlgebraic ℚ (Complex.exp ((c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  refine IsAlgebraic.of_pow (n := c.den) c.pos ?_
  have hden : ((c.den : ℕ) : ℂ) * (c : ℂ) = ((c.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  have hstep : ((c.den : ℕ) : ℂ) * ((c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
      = ((c.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [← mul_assoc, hden]
  rw [← Complex.exp_nat_mul, hstep, Complex.exp_int_mul_two_pi_mul_I]
  simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))

/-- **The main route lemma.**  Under the theorem of the four exponentials, a point whose
norm-square is a rational multiple of the aligned datum `π (Im u + rπ)` cannot have an
algebraic exponential.

Load-bearing hypotheses: `Re u ≠ 0`, `Im u ∉ πℚ` (only through `Im u + rπ ≠ 0`), and the
rational-multiple relation.  `u ≠ 0`, `‖u‖ ∈ Q̄` and `(exp u).im ≠ 0` are **not** used. -/
theorem transcendental_of_fourExpDet (h4 : FourExpDet) (u : ℂ)
    (hre : u.re ≠ 0)
    (hirr : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi)
    {r c₀ : ℚ}
    (hc : (‖u‖ : ℝ) ^ 2 = (c₀ : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) :
    Transcendental ℚ (Complex.exp u) := by
  intro hexp
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπC : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ0
  set s : ℝ := u.im + (r : ℝ) * Real.pi with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    refine hirr ⟨-r, ?_⟩
    have : u.im = -((r : ℝ) * Real.pi) := by rw [hs_def] at h; linarith
    push_cast; linarith [this]
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hu0 : u ≠ 0 := by intro h; exact hre (by rw [h]; rfl)
  have hnorm_pos : (0 : ℝ) < (‖u‖ : ℝ) ^ 2 := by
    have : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
    positivity
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    rw [h] at hc
    have hz : (‖u‖ : ℝ) ^ 2 = 0 := by rw [hc]; push_cast; ring
    linarith [hnorm_pos, hz]
  set ν : ℂ := Complex.I * ((s : ℝ) : ℂ) with hν_def
  have hν0 : ν ≠ 0 := mul_ne_zero Complex.I_ne_zero hsC
  set c : ℚ := -c₀ / 2 with hc_def
  have hcne : c ≠ 0 := by
    rw [hc_def]; simpa using hc₀0
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  set l₃ : ℂ := (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) with hl3_def
  have hexpν : IsAlgebraic ℚ (Complex.exp ν) := by
    refine IsAlgebraic.of_pow (n := 2 * r.den) (by positivity) ?_
    have hmul : (((2 * r.den : ℕ)) : ℂ) * ν =
        ((r.den : ℕ) : ℂ) * (u - conj u)
          + ((r.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.sub_conj, hν_def, hs_def]
      push_cast [Rat.cast_def]
      field_simp
    have hkey : Complex.exp ν ^ (2 * r.den) =
        (Complex.exp u / conj (Complex.exp u)) ^ r.den := by
      rw [← Complex.exp_nat_mul, hmul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        mul_one, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_conj]
    rw [hkey]
    exact alg_pow (alg_div hexp (alg_conj hexp)) r.den
  have hexpconj : IsAlgebraic ℚ (Complex.exp (conj u)) := by
    rw [Complex.exp_conj]; exact alg_conj hexp
  have hexpl₃ : IsAlgebraic ℚ (Complex.exp l₃) := by
    rw [hl3_def]; exact alg_exp_rat_two_pi_I c
  have hrows : ∀ a b : ℚ, (a : ℂ) * u + (b : ℂ) * l₃ = 0 →
      (a : ℂ) * ν + (b : ℂ) * (conj u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 _
    have hre1 : ((a : ℂ) * u + (b : ℂ) * l₃).re = 0 := by rw [h1]; rfl
    have hz : ((a : ℂ) * u + (b : ℂ) * l₃).re = (a : ℝ) * u.re := by
      rw [hl3_def]; simp
    rw [hz] at hre1
    have ha : (a : ℝ) = 0 := by
      rcases mul_eq_zero.1 hre1 with h | h
      · exact h
      · exact absurd h hre
    have ha' : a = 0 := by exact_mod_cast ha
    refine ⟨ha', ?_⟩
    rw [ha'] at h1
    simp only [Rat.cast_zero, zero_mul, zero_add] at h1
    have : (b : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h (by rw [hl3_def]; exact mul_ne_zero hcC (by
          simp [hπC, Complex.I_ne_zero]))
    exact_mod_cast this
  have hcols : ∀ a b : ℚ, (a : ℂ) * u + (b : ℂ) * ν = 0 →
      (a : ℂ) * l₃ + (b : ℂ) * (conj u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 _
    have hre1 : ((a : ℂ) * u + (b : ℂ) * ν).re = 0 := by rw [h1]; rfl
    have hz : ((a : ℂ) * u + (b : ℂ) * ν).re = (a : ℝ) * u.re := by
      rw [hν_def]; simp
    rw [hz] at hre1
    have ha : (a : ℝ) = 0 := by
      rcases mul_eq_zero.1 hre1 with h | h
      · exact h
      · exact absurd h hre
    have ha' : a = 0 := by exact_mod_cast ha
    refine ⟨ha', ?_⟩
    rw [ha'] at h1
    simp only [Rat.cast_zero, zero_mul, zero_add] at h1
    have : (b : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hν0
    exact_mod_cast this
  have hdet : u * (conj u) - ν * l₃ = 0 := by
    have h1 : u * conj u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : ν * l₃ = -(2 * (c : ℂ) * ((Real.pi : ℝ) : ℂ) * ((s : ℝ) : ℂ)) := by
      rw [hν_def, hl3_def]
      have := Complex.I_sq
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h1, h2, hc]
    have : ((c : ℝ)) = -(c₀ : ℝ) / 2 := by rw [hc_def]; push_cast; ring
    push_cast
    rw [hc_def]
    push_cast
    ring
  exact h4 u ν l₃ (conj u) hexp hexpν hexpl₃ hexpconj hrows hcols hdet

/-- The rational-multiple half of the aligned leaf, from the four exponentials conjecture. -/
theorem alignedRatMult_of_fourExpDet (h4 : FourExpDet) : AlignedRatMult := by
  intro u _ _ _ hax hirr _ hnrm
  obtain ⟨r, _, _, c₀, hc⟩ := hnrm
  have hre : u.re ≠ 0 := fun h => hax (Or.inr h)
  exact transcendental_of_fourExpDet h4 u hre hirr (r := r) (c₀ := c₀) hc

/-! ## 4. Both halves of the split are non-empty.

Both witnesses use the same angle `yA = 1/π − π` (so `r = 1` and `β = π(yA+π) = 1`) and
differ only in the norm: `‖wA‖² = 16 ∈ ℚ·β` and `‖wC‖² = 16√2 ∉ ℚ·β`. -/

theorem beta_yA : (Real.pi * (yA + ((1 : ℚ) : ℝ) * Real.pi) : ℝ) = 1 := by
  have hne : Real.pi ≠ 0 := Real.pi_ne_zero
  have hw : yA = 1 / Real.pi - Real.pi := rfl
  rw [hw]
  have hsimp : (1 / Real.pi - Real.pi + ((1 : ℚ) : ℝ) * Real.pi) = 1 / Real.pi := by
    push_cast; ring
  rw [hsimp]; field_simp

/-- On the `yA` line the aligned witness is unique: `r = 1`. -/
theorem yA_witness_unique (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) {r : ℚ}
    (halg : IsAlgebraic ℚ ((Real.pi * (yA + (r : ℝ) * Real.pi) : ℝ) : ℂ)) : r = 1 := by
  by_contra hne
  have hr1 : r - 1 ≠ 0 := sub_ne_zero.2 hne
  refine pi_not_quadratic hpi (r := r - 1) (b := 0) hr1 ?_
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hval : (Real.pi * (yA + (r : ℝ) * Real.pi) : ℝ)
      = 1 + ((r : ℝ) - 1) * Real.pi ^ 2 := by
    have hw : yA = 1 / Real.pi - Real.pi := rfl
    rw [hw]; field_simp; ring
  rw [hval] at halg
  have hcast : (((1 + ((r : ℝ) - 1) * Real.pi ^ 2 : ℝ)) : ℂ)
      = 1 + (((r - 1 : ℚ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by push_cast; ring
  rw [hcast] at halg
  have h1 : IsAlgebraic ℚ ((1 : ℂ)) := by simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))
  have hsub : IsAlgebraic ℚ ((1 + (((r - 1 : ℚ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) - 1) := by
    rw [alg_iff_mem] at halg h1 ⊢
    exact Subfield.sub_mem _ halg h1
  have hfix : ((1 : ℂ) + (((r - 1 : ℚ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) - 1
      = ((0 : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ)
        + (((r - 1 : ℚ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 := by push_cast; ring
  rw [hfix] at hsub
  exact hsub

theorem wA_normRatMult : NormRatMult wA := by
  refine ⟨1, one_ne_zero, ?_, 16, ?_⟩
  · have : wA.im = yA := rfl
    rw [this, beta_yA]
    simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))
  · have him : wA.im = yA := rfl
    rw [him, beta_yA, norm_wA]; norm_num

/-! ### The `¬Φ` witness: same angle, norm `16√2`. -/

noncomputable def wC : ℂ := ⟨Real.sqrt (16 * Real.sqrt 2 - yA ^ 2), yA⟩

theorem sqrt2_gt_one : (1 : ℝ) < Real.sqrt 2 := by
  have : Real.sqrt 1 < Real.sqrt 2 := by
    apply Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  simpa using this

theorem yA_sq_lt' : yA ^ 2 < 16 * Real.sqrt 2 := by
  have h := yA_sq_lt
  have h2 := sqrt2_gt_one
  nlinarith [h, h2]

theorem normSq_wC : Complex.normSq wC = 16 * Real.sqrt 2 := by
  have h1 : (0 : ℝ) ≤ 16 * Real.sqrt 2 - yA ^ 2 := by linarith [yA_sq_lt']
  rw [wC, Complex.normSq_mk, Real.mul_self_sqrt h1]; ring

theorem norm_wC_sq : (‖wC‖ : ℝ) ^ 2 = 16 * Real.sqrt 2 := by
  rw [← Complex.normSq_eq_norm_sq, normSq_wC]

theorem norm_wC_alg : IsAlgebraic ℚ ((‖wC‖ : ℝ) : ℂ) := by
  refine IsAlgebraic.of_pow (n := 4) (by norm_num) ?_
  have h2 : ((‖wC‖ : ℝ) : ℂ) ^ 4 = (((‖wC‖ : ℝ) ^ 2 : ℝ) : ℂ) ^ 2 := by push_cast; ring
  have hs : ((16 : ℝ) * Real.sqrt 2) ^ 2 = 512 := by
    have : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    nlinarith [this]
  rw [h2, norm_wC_sq]
  have : ((((16 : ℝ) * Real.sqrt 2 : ℝ)) : ℂ) ^ 2 = ((512 : ℚ) : ℂ) := by
    have hc : (((((16 : ℝ) * Real.sqrt 2) ^ 2 : ℝ)) : ℂ) = ((512 : ℝ) : ℂ) := by rw [hs]
    push_cast at hc ⊢
    linear_combination hc
  rw [this]
  exact alg_rat _

theorem wC_re_pos : 0 < wC.re := by
  have h1 : (0 : ℝ) < 16 * Real.sqrt 2 - yA ^ 2 := by linarith [yA_sq_lt']
  simpa [wC] using Real.sqrt_pos.2 h1

/-- `wC` lies in the aligned class but **not** in the rational-multiple half. -/
theorem wC_mem_normFree (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wC ≠ 0 ∧ IsAlgebraic ℚ ((‖wC‖ : ℝ) : ℂ) ∧ (Complex.exp wC).im ≠ 0 ∧
      ¬ (wC.im = 0 ∨ wC.re = 0) ∧ (¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi) ∧
      PeriodAligned wC ∧ ¬ NormRatMult wC := by
  have him' : wC.im = yA := rfl
  have hre : wC.re ≠ 0 := ne_of_gt wC_re_pos
  have him : wC.im ≠ 0 := by rw [him']; exact ne_of_lt yA_neg
  have hnpr : ¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi := by
    rw [him']
    have := wA_not_pi_rat hpi
    have hA : wA.im = yA := rfl
    rw [hA] at this
    exact this
  refine ⟨?_, norm_wC_alg, exp_im_ne_zero_of_not_pi_rat hnpr, ?_, hnpr, ⟨1, one_ne_zero, ?_⟩, ?_⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rintro (h | h)
    · exact him h
    · exact hre h
  · rw [him', beta_yA]
    simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))
  · rintro ⟨r, _, halg, c, hc⟩
    rw [him'] at halg hc
    have hr1 : r = 1 := yA_witness_unique hpi halg
    rw [hr1, beta_yA, norm_wC_sq] at hc
    have hval : Real.sqrt 2 = ((c / 16 : ℚ) : ℝ) := by
      push_cast; linarith [hc]
    exact irrational_sqrt_two ⟨c / 16, hval.symm⟩

end DiazAligned


namespace DiazAligned

open DiazModulus DiazLeafSplit

/-! ## 5. The aligned class has transcendence degree one.

`t = Re u` is algebraic over `Q̄(π)`: eliminating `θ = Im u = β/π − rπ` from
`t² + θ² = A` gives a polynomial relation over `Q̄` between `t` and `π`.  This holds on the
**whole** aligned class, not just on the rational-multiple half, and it is what puts the
configuration inside the regime where the four exponentials conjecture is a theorem
(`Diaz.four_exp_trdeg_one`).  On the period-**free** half there is no such relation. -/

/-- **The transcendence-degree-one certificate.**  With `β = π (Im u + rπ)` and
`A = ‖u‖²`, the real part `t = Re u` satisfies
`t²π² + r²π⁴ − (A + 2rβ)π² + β² = 0`, a non-trivial polynomial over `ℚ(A, β, r)`. -/
theorem aligned_quartic_relation (u : ℂ) (r : ℚ)
    (A β : ℝ) (hA : (‖u‖ : ℝ) ^ 2 = A)
    (hβ : Real.pi * (u.im + (r : ℝ) * Real.pi) = β) :
    u.re ^ 2 * Real.pi ^ 2 + (r : ℝ) ^ 2 * Real.pi ^ 4
      - (A + 2 * (r : ℝ) * β) * Real.pi ^ 2 + β ^ 2 = 0 := by
  have hnorm : (‖u‖ : ℝ) ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hnorm] at hA
  linear_combination (Real.pi ^ 2) * hA
    + (-(2 * (β - (r : ℝ) * Real.pi ^ 2))
        - (Real.pi * (u.im + (r : ℝ) * Real.pi) - β)) * hβ

end DiazAligned

end

section
-- inlined from DZ_FREE_core

/-
# The period-aligned **norm-free** half: the four-exponentials route is unavailable

`DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_free`
(`1b43101e-b00e-4168-9769-ddd07242b0c6`).

Write `t = Re u`, `θ = Im u`, `β = π(θ + rπ)`, `A = ‖u‖²`.  On the sibling half `A = cβ` with
`c ∈ ℚ`, and the matrix `[[u, ν],[c·2πi, conj u]]` has vanishing determinant, `ℚ`-independent
rows and `ℚ`-independent columns, so the four exponentials statement applies.

**Here it does not, and no other matrix over the certified logarithm space does either.**
`no_admissible_matrix` below: every `2 × 2` matrix whose entries lie in
`span_ℚ {u, conj u, 2πi}` and whose determinant vanishes has `ℚ`-linearly dependent rows or
`ℚ`-linearly dependent columns.  Inputs: `Transcendental ℚ π`, `Re u ≠ 0`, `β ≠ 0`, `β` and
`‖u‖²` algebraic, and `‖u‖² ∉ ℚ·β`.
-/

open Complex ComplexConjugate

namespace DiazFree

open DiazModulus DiazLeafSplit DiazAligned

/-! ## 1. `π` admits no algebraic quartic relation in `π²`. -/

/-- If `c₂π⁴ + c₁π² + c₀ = 0` with `c₀, c₁, c₂` algebraic, then all three vanish.
Proof: completing the square exhibits `π² + c₁/(2c₂)` as a square root of an algebraic
number, hence algebraic, hence `π` algebraic. -/
theorem pi_no_alg_quartic (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {c₀ c₁ c₂ : ℂ} (h₀ : IsAlgebraic ℚ c₀) (h₁ : IsAlgebraic ℚ c₁) (h₂ : IsAlgebraic ℚ c₂)
    (h : c₂ * ((Real.pi : ℝ) : ℂ) ^ 4 + c₁ * ((Real.pi : ℝ) : ℂ) ^ 2 + c₀ = 0) :
    c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  set P : ℂ := ((Real.pi : ℝ) : ℂ) with hP
  -- `π²` algebraic is already a contradiction
  have hsq : ¬ IsAlgebraic ℚ (P ^ 2) := by
    intro hc
    exact hpi (IsAlgebraic.of_pow (n := 2) (by norm_num) hc)
  have hc2 : c₂ = 0 := by
    by_contra hne
    -- complete the square: `(P² + c₁/(2c₂))² = c₁²/(4c₂²) − c₀/c₂`
    set s : ℂ := c₁ / (2 * c₂) with hs
    set D : ℂ := c₁ ^ 2 / (4 * c₂ ^ 2) - c₀ / c₂ with hD
    have hsalg : IsAlgebraic ℚ s := by
      rw [hs]; exact alg_div h₁ (alg_mul (alg_rat 2) h₂)
    have hDalg : IsAlgebraic ℚ D := by
      rw [hD]
      rw [alg_iff_mem] at h₀ h₁ h₂ ⊢
      exact Subfield.sub_mem _
        (Subfield.div_mem _ (Subfield.pow_mem _ h₁ 2)
          (Subfield.mul_mem _ (by rw [← alg_iff_mem]; exact alg_rat 4)
            (Subfield.pow_mem _ h₂ 2)))
        (Subfield.div_mem _ h₀ h₂)
    have hkey : (P ^ 2 + s) ^ 2 = D := by
      have hstep : (P ^ 2 + s) ^ 2 - D = (c₂ * P ^ 4 + c₁ * P ^ 2 + c₀) / c₂ := by
        rw [hs, hD]; field_simp; ring
      rw [h, zero_div] at hstep
      linear_combination hstep
    have halg1 : IsAlgebraic ℚ (P ^ 2 + s) := by
      refine IsAlgebraic.of_pow (n := 2) (by norm_num) ?_
      rw [hkey]; exact hDalg
    have : IsAlgebraic ℚ (P ^ 2) := by
      have := halg1
      rw [alg_iff_mem] at this hsalg ⊢
      simpa using Subfield.sub_mem _ this hsalg
    exact hsq this
  subst hc2
  have h' : c₁ * P ^ 2 + c₀ = 0 := by linear_combination h
  have hc1 : c₁ = 0 := by
    by_contra hne
    have : P ^ 2 = -c₀ / c₁ := by field_simp; linear_combination h'
    refine hsq ?_
    rw [this]
    exact alg_div (alg_neg h₀) h₁
  subst hc1
  refine ⟨rfl, rfl, ?_⟩
  linear_combination h'


/-! ## 2.  Linear algebra over `ℚ`.

The transcendence input of §3 will say that the quadratic form `det` vanishes identically on
the rational subspace spanned by the three coefficient matrices of the entries.  Everything
after that is the following statement: a `2 × 2` array of vectors in `ℚ³` on which every
"evaluation determinant" vanishes has `ℚ`-dependent rows or `ℚ`-dependent columns. -/

theorem sumsq_ne_zero {p q r : ℚ} (h : ¬ (p = 0 ∧ q = 0 ∧ r = 0)) :
    p ^ 2 + q ^ 2 + r ^ 2 ≠ 0 := by
  have : p ≠ 0 ∨ q ≠ 0 ∨ r ≠ 0 := by tauto
  rcases this with h' | h' | h' <;>
    · intro hc
      have h1 := sq_nonneg p
      have h2 := sq_nonneg q
      have h3 := sq_nonneg r
      have : p = 0 ∧ q = 0 ∧ r = 0 := by
        refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg p, sq_nonneg q, sq_nonneg r]
      tauto

/-- Linear forms on `ℚ³` have no zero divisors: if the product of two of them vanishes
identically then one of the two vectors is `0`.  Three evaluations suffice. -/
theorem lin_nz {p q r p' q' r' : ℚ}
    (h : ∀ α γ δ : ℚ, (α * p + γ * q + δ * r) * (α * p' + γ * q' + δ * r') = 0) :
    (p = 0 ∧ q = 0 ∧ r = 0) ∨ (p' = 0 ∧ q' = 0 ∧ r' = 0) := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  have hn : p ^ 2 + q ^ 2 + r ^ 2 ≠ 0 := sumsq_ne_zero (by tauto)
  have hn' : p' ^ 2 + q' ^ 2 + r' ^ 2 ≠ 0 := sumsq_ne_zero (by tauto)
  have e1 := h p q r
  have hcross : p * p' + q * q' + r * r' = 0 := by
    rcases mul_eq_zero.1 e1 with hz | hz
    · exact absurd (by linear_combination hz) hn
    · linear_combination hz
  have e3 := h (p + p') (q + q') (r + r')
  have : (p ^ 2 + q ^ 2 + r ^ 2) * (p' ^ 2 + q' ^ 2 + r' ^ 2) = 0 := by
    linear_combination e3 - (p ^ 2 + q ^ 2 + r ^ 2 + p' ^ 2 + q' ^ 2 + r' ^ 2 +
      (p * p' + q * q' + r * r')) * hcross
  rcases mul_eq_zero.1 this with hz | hz
  · exact hn hz
  · exact hn' hz

/-- The small generic step: two independent kernel directions are impossible. -/
theorem no_two_kernels
    {p₁ e₁ f₁ p₂ e₂ f₂ p₃ e₃ f₃ p₄ e₄ f₄ : ℚ}
    (hid : ∀ α γ δ : ℚ,
      (α * p₁ + γ * e₁ + δ * f₁) * (α * p₄ + γ * e₄ + δ * f₄)
        = (α * p₂ + γ * e₂ + δ * f₂) * (α * p₃ + γ * e₃ + δ * f₃))
    {α₀ γ₀ δ₀ α₁ γ₁ δ₁ : ℚ}
    (h1a : α₀ * p₁ + γ₀ * e₁ + δ₀ * f₁ = 0)
    (h2a : α₀ * p₂ + γ₀ * e₂ + δ₀ * f₂ ≠ 0)
    (h1b : α₁ * p₁ + γ₁ * e₁ + δ₁ * f₁ = 0)
    (h3b : α₁ * p₃ + γ₁ * e₃ + δ₁ * f₃ ≠ 0) : False := by
  have e1 := hid α₀ γ₀ δ₀
  have h3a : α₀ * p₃ + γ₀ * e₃ + δ₀ * f₃ = 0 := by
    have hz : (α₀ * p₂ + γ₀ * e₂ + δ₀ * f₂) * (α₀ * p₃ + γ₀ * e₃ + δ₀ * f₃) = 0 := by
      linear_combination -e1 + (α₀ * p₄ + γ₀ * e₄ + δ₀ * f₄) * h1a
    rcases mul_eq_zero.1 hz with hz' | hz'
    · exact absurd hz' h2a
    · exact hz'
  have e2 := hid α₁ γ₁ δ₁
  have h2b : α₁ * p₂ + γ₁ * e₂ + δ₁ * f₂ = 0 := by
    have hz : (α₁ * p₂ + γ₁ * e₂ + δ₁ * f₂) * (α₁ * p₃ + γ₁ * e₃ + δ₁ * f₃) = 0 := by
      linear_combination -e2 + (α₁ * p₄ + γ₁ * e₄ + δ₁ * f₄) * h1b
    rcases mul_eq_zero.1 hz with hz' | hz'
    · exact hz'
    · exact absurd hz' h3b
  have e3 := hid (α₀ + α₁) (γ₀ + γ₁) (δ₀ + δ₁)
  have hprod : (α₀ * p₂ + γ₀ * e₂ + δ₀ * f₂) * (α₁ * p₃ + γ₁ * e₃ + δ₁ * f₃) = 0 := by
    linear_combination -e3 + ((α₀ + α₁) * p₄ + (γ₀ + γ₁) * e₄ + (δ₀ + δ₁) * f₄) * h1a
      + ((α₀ + α₁) * p₄ + (γ₀ + γ₁) * e₄ + (δ₀ + δ₁) * f₄) * h1b
      - (α₁ * p₃ + γ₁ * e₃ + δ₁ * f₃) * h2b
      - ((α₀ * p₂ + γ₀ * e₂ + δ₀ * f₂) + (α₁ * p₂ + γ₁ * e₂ + δ₁ * f₂)) * h3a
  rcases mul_eq_zero.1 hprod with hz | hz
  · exact h2a hz
  · exact h3b hz

/-- **The rank-one dichotomy over `ℚ`.**  Four vectors `v₁ v₂ v₃ v₄ ∈ ℚ³` arranged as a
`2 × 2` array, such that for *every* `v ∈ ℚ³` the numerical determinant
`⟨v,v₁⟩⟨v,v₄⟩ − ⟨v,v₂⟩⟨v,v₃⟩` vanishes, have `ℚ`-dependent columns or `ℚ`-dependent rows. -/
theorem rank_one_dichotomy
    {p₁ e₁ f₁ p₂ e₂ f₂ p₃ e₃ f₃ p₄ e₄ f₄ : ℚ}
    (hid : ∀ α γ δ : ℚ,
      (α * p₁ + γ * e₁ + δ * f₁) * (α * p₄ + γ * e₄ + δ * f₄)
        = (α * p₂ + γ * e₂ + δ * f₂) * (α * p₃ + γ * e₃ + δ * f₃)) :
    (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        a * p₁ + b * p₂ = 0 ∧ a * e₁ + b * e₂ = 0 ∧ a * f₁ + b * f₂ = 0 ∧
        a * p₃ + b * p₄ = 0 ∧ a * e₃ + b * e₄ = 0 ∧ a * f₃ + b * f₄ = 0)
  ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        a * p₁ + b * p₃ = 0 ∧ a * e₁ + b * e₃ = 0 ∧ a * f₁ + b * f₃ = 0 ∧
        a * p₂ + b * p₄ = 0 ∧ a * e₂ + b * e₄ = 0 ∧ a * f₂ + b * f₄ = 0) := by
  by_cases hv1 : p₁ = 0 ∧ e₁ = 0 ∧ f₁ = 0
  · obtain ⟨hp, he, hf⟩ := hv1
    have h23 : ∀ α γ δ : ℚ,
        (α * p₂ + γ * e₂ + δ * f₂) * (α * p₃ + γ * e₃ + δ * f₃) = 0 := by
      intro α γ δ
      rw [← hid α γ δ, hp, he, hf]; ring
    rcases lin_nz h23 with ⟨q1, q2, q3⟩ | ⟨q1, q2, q3⟩
    · exact Or.inr ⟨1, 0, Or.inl one_ne_zero, by rw [hp]; ring, by rw [he]; ring,
        by rw [hf]; ring, by rw [q1]; ring, by rw [q2]; ring, by rw [q3]; ring⟩
    · exact Or.inl ⟨1, 0, Or.inl one_ne_zero, by rw [hp]; ring, by rw [he]; ring,
        by rw [hf]; ring, by rw [q1]; ring, by rw [q2]; ring, by rw [q3]; ring⟩
  · have hn1 : p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2 ≠ 0 := sumsq_ne_zero hv1
    by_cases hc12 : e₁ * f₂ - f₁ * e₂ = 0 ∧ f₁ * p₂ - p₁ * f₂ = 0 ∧ p₁ * e₂ - e₁ * p₂ = 0
    · obtain ⟨c1, c2, c3⟩ := hc12
      have hp2 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * p₂ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * p₁ = 0 := by
        linear_combination (-e₁) * c3 + f₁ * c2
      have he2 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * e₂ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * e₁ = 0 := by
        linear_combination p₁ * c3 - f₁ * c1
      have hf2 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * f₂ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * f₁ = 0 := by
        linear_combination (-p₁) * c2 + e₁ * c1
      have hkey : ∀ α γ δ : ℚ,
          (α * p₁ + γ * e₁ + δ * f₁) *
            (α * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * p₄ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * p₃)
              + γ * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * e₄ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * e₃)
              + δ * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * f₄ - (p₁ * p₂ + e₁ * e₂ + f₁ * f₂) * f₃)) = 0 := by
        intro α γ δ
        linear_combination (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * hid α γ δ
          + ((α * p₃ + γ * e₃ + δ * f₃) * α) * hp2
          + ((α * p₃ + γ * e₃ + δ * f₃) * γ) * he2
          + ((α * p₃ + γ * e₃ + δ * f₃) * δ) * hf2
      rcases lin_nz hkey with h | ⟨q1, q2, q3⟩
      · exact absurd h hv1
      · refine Or.inl ⟨p₁ * p₂ + e₁ * e₂ + f₁ * f₂, -(p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2),
          Or.inr (neg_ne_zero.2 hn1), by linear_combination -hp2, by linear_combination -he2,
          by linear_combination -hf2, by linear_combination -q1, by linear_combination -q2,
          by linear_combination -q3⟩
    · by_cases hc13 : e₁ * f₃ - f₁ * e₃ = 0 ∧ f₁ * p₃ - p₁ * f₃ = 0 ∧ p₁ * e₃ - e₁ * p₃ = 0
      · obtain ⟨c1, c2, c3⟩ := hc13
        have hp3 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * p₃ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * p₁ = 0 := by
          linear_combination (-e₁) * c3 + f₁ * c2
        have he3 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * e₃ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * e₁ = 0 := by
          linear_combination p₁ * c3 - f₁ * c1
        have hf3 : (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * f₃ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * f₁ = 0 := by
          linear_combination (-p₁) * c2 + e₁ * c1
        have hkey : ∀ α γ δ : ℚ,
            (α * p₁ + γ * e₁ + δ * f₁) *
              (α * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * p₄ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * p₂)
                + γ * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * e₄ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * e₂)
                + δ * ((p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * f₄ - (p₁ * p₃ + e₁ * e₃ + f₁ * f₃) * f₂)) = 0 := by
          intro α γ δ
          linear_combination (p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2) * hid α γ δ
            + ((α * p₂ + γ * e₂ + δ * f₂) * α) * hp3
            + ((α * p₂ + γ * e₂ + δ * f₂) * γ) * he3
            + ((α * p₂ + γ * e₂ + δ * f₂) * δ) * hf3
        rcases lin_nz hkey with h | ⟨q1, q2, q3⟩
        · exact absurd h hv1
        · refine Or.inr ⟨p₁ * p₃ + e₁ * e₃ + f₁ * f₃, -(p₁ ^ 2 + e₁ ^ 2 + f₁ ^ 2),
            Or.inr (neg_ne_zero.2 hn1), by linear_combination -hp3, by linear_combination -he3,
            by linear_combination -hf3, by linear_combination -q1, by linear_combination -q2,
            by linear_combination -q3⟩
      · exfalso
        have hA : ∃ α γ δ : ℚ, α * p₁ + γ * e₁ + δ * f₁ = 0 ∧ α * p₂ + γ * e₂ + δ * f₂ ≠ 0 := by
          have : e₁ * f₂ - f₁ * e₂ ≠ 0 ∨ f₁ * p₂ - p₁ * f₂ ≠ 0 ∨ p₁ * e₂ - e₁ * p₂ ≠ 0 := by
            tauto
          rcases this with h | h | h
          · exact ⟨0, f₁, -e₁, by ring, fun hz => h (by linear_combination -hz)⟩
          · exact ⟨f₁, 0, -p₁, by ring, fun hz => h (by linear_combination hz)⟩
          · exact ⟨e₁, -p₁, 0, by ring, fun hz => h (by linear_combination -hz)⟩
        have hB : ∃ α γ δ : ℚ, α * p₁ + γ * e₁ + δ * f₁ = 0 ∧ α * p₃ + γ * e₃ + δ * f₃ ≠ 0 := by
          have : e₁ * f₃ - f₁ * e₃ ≠ 0 ∨ f₁ * p₃ - p₁ * f₃ ≠ 0 ∨ p₁ * e₃ - e₁ * p₃ ≠ 0 := by
            tauto
          rcases this with h | h | h
          · exact ⟨0, f₁, -e₁, by ring, fun hz => h (by linear_combination -hz)⟩
          · exact ⟨f₁, 0, -p₁, by ring, fun hz => h (by linear_combination hz)⟩
          · exact ⟨e₁, -p₁, 0, by ring, fun hz => h (by linear_combination -hz)⟩
        obtain ⟨α₀, γ₀, δ₀, h1a, h2a⟩ := hA
        obtain ⟨α₁, γ₁, δ₁, h1b, h3b⟩ := hB
        exact no_two_kernels hid h1a h2a h1b h3b

/-! ## 3.  The certified logarithm space, and its normal form. -/

/-- The `ℚ`-span of `u`, `conj u` and `2πi` — every logarithm of an algebraic number that the
class data certifies once `exp u` is assumed algebraic. -/
def MemL3 (u z : ℂ) : Prop :=
  ∃ a b c : ℚ, z = (a : ℂ) * u + (b : ℂ) * (starRingEnd ℂ) u
    + (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)

theorem alg_add {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z + w) := by
  rw [alg_iff_mem] at *; exact Subfield.add_mem _ hz hw

theorem alg_sub {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z - w) := by
  rw [alg_iff_mem] at *; exact Subfield.sub_mem _ hz hw

/-- **Normal form on `L₃`.**  Adapted to the quartic relation: `z = p·Re u + i·m` with `p`
rational and `π m = e·β + f·π²` with `e, f` rational.  The basis is `Re u`, `β/(πi)`, `πi`. -/
theorem memL3_normal (u z : ℂ) (r : ℚ) (h : MemL3 u z) :
    ∃ p e f : ℚ, ∃ m : ℝ,
      z = (((p : ℝ) * u.re : ℝ) : ℂ) + ((m : ℝ) : ℂ) * Complex.I ∧
      Real.pi * m
        = (e : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)) + (f : ℝ) * Real.pi ^ 2 := by
  obtain ⟨a, b, c, hz⟩ := h
  refine ⟨a + b, a - b, 2 * c - (a - b) * r,
    ((a : ℝ) - (b : ℝ)) * u.im + 2 * (c : ℝ) * Real.pi, ?_, ?_⟩
  · rw [hz]
    apply Complex.ext <;> simp <;> ring
  · push_cast; ring

/-! ## 4.  The no-go. -/

/-- **No admissible matrix.**  On the period-aligned, norm-**free** half, every `2 × 2` matrix
with entries in `span_ℚ {u, conj u, 2πi}` and vanishing determinant has `ℚ`-linearly dependent
rows or `ℚ`-linearly dependent columns.  Hence the hypotheses of the four exponentials
statement (`DiazAligned.FourExpDet`) can never be met from the certified data on this half. -/
theorem no_admissible_matrix
    (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    (u : ℂ) (r : ℚ)
    (hre : u.re ≠ 0)
    (hβ0 : Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0)
    (hβalg : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ))
    (hAalg : IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ))
    (hfree : ¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)))
    {l₁ l₂ l₃ l₄ : ℂ}
    (hm₁ : MemL3 u l₁) (hm₂ : MemL3 u l₂) (hm₃ : MemL3 u l₃) (hm₄ : MemL3 u l₄)
    (hdet : l₁ * l₄ - l₂ * l₃ = 0) :
    (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        (a : ℂ) * l₁ + (b : ℂ) * l₃ = 0 ∧ (a : ℂ) * l₂ + (b : ℂ) * l₄ = 0)
  ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        (a : ℂ) * l₁ + (b : ℂ) * l₂ = 0 ∧ (a : ℂ) * l₃ + (b : ℂ) * l₄ = 0) := by
  obtain ⟨p₁, e₁, f₁, n₁, hl₁, hn₁⟩ := memL3_normal u l₁ r hm₁
  obtain ⟨p₂, e₂, f₂, n₂, hl₂, hn₂⟩ := memL3_normal u l₂ r hm₂
  obtain ⟨p₃, e₃, f₃, n₃, hl₃, hn₃⟩ := memL3_normal u l₃ r hm₃
  obtain ⟨p₄, e₄, f₄, n₄, hl₄, hn₄⟩ := memL3_normal u l₄ r hm₄
  set t : ℝ := u.re with ht
  set β : ℝ := Real.pi * (u.im + (r : ℝ) * Real.pi) with hβ
  set A : ℝ := (‖u‖ : ℝ) ^ 2 with hA
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  -- the two real equations coming from `det = 0`
  have hz0 : l₁ * l₄ - l₂ * l₃
      = ((((p₁ : ℝ) * t) * ((p₄ : ℝ) * t) - n₁ * n₄
        - (((p₂ : ℝ) * t) * ((p₃ : ℝ) * t) - n₂ * n₃) : ℝ) : ℂ)
      + ((((p₁ : ℝ) * t) * n₄ + n₁ * ((p₄ : ℝ) * t)
        - (((p₂ : ℝ) * t) * n₃ + n₂ * ((p₃ : ℝ) * t)) : ℝ) : ℂ) * Complex.I := by
    rw [hl₁, hl₂, hl₃, hl₄]; push_cast
    linear_combination (((n₁ : ℝ) : ℂ) * ((n₄ : ℝ) : ℂ) - ((n₂ : ℝ) : ℂ) * ((n₃ : ℝ) : ℂ)) * Complex.I_sq
  have hz : ((((p₁ : ℝ) * t) * ((p₄ : ℝ) * t) - n₁ * n₄
        - (((p₂ : ℝ) * t) * ((p₃ : ℝ) * t) - n₂ * n₃) : ℝ) : ℂ)
      + ((((p₁ : ℝ) * t) * n₄ + n₁ * ((p₄ : ℝ) * t)
        - (((p₂ : ℝ) * t) * n₃ + n₂ * ((p₃ : ℝ) * t)) : ℝ) : ℂ) * Complex.I = 0 := by
    rw [← hz0]; exact hdet
  have hR : ((p₁ : ℝ) * t) * ((p₄ : ℝ) * t) - n₁ * n₄
      - (((p₂ : ℝ) * t) * ((p₃ : ℝ) * t) - n₂ * n₃) = 0 := by
    have := congrArg Complex.re hz; simpa using this
  have hI : ((p₁ : ℝ) * t) * n₄ + n₁ * ((p₄ : ℝ) * t)
      - (((p₂ : ℝ) * t) * n₃ + n₂ * ((p₃ : ℝ) * t)) = 0 := by
    have := congrArg Complex.im hz; simpa using this
  -- the six rational forms
  set P : ℚ := p₁ * p₄ - p₂ * p₃ with hP
  set E : ℚ := e₁ * e₄ - e₂ * e₃ with hE
  set F : ℚ := f₁ * f₄ - f₂ * f₃ with hF
  set G : ℚ := p₁ * e₄ + e₁ * p₄ - p₂ * e₃ - e₂ * p₃ with hG
  set H : ℚ := p₁ * f₄ + f₁ * p₄ - p₂ * f₃ - f₂ * p₃ with hH
  set J : ℚ := e₁ * f₄ + f₁ * e₄ - e₂ * f₃ - f₂ * e₃ with hJ
  have hPR : (P : ℝ) = (p₁ : ℝ) * (p₄ : ℝ) - (p₂ : ℝ) * (p₃ : ℝ) := by
    rw [hP]; push_cast; ring
  -- imaginary part: `β G + π² H = 0`
  have hY : (p₁ : ℝ) * n₄ + n₁ * (p₄ : ℝ) - ((p₂ : ℝ) * n₃ + n₂ * (p₃ : ℝ)) = 0 := by
    have hmul : t * ((p₁ : ℝ) * n₄ + n₁ * (p₄ : ℝ) - ((p₂ : ℝ) * n₃ + n₂ * (p₃ : ℝ))) = 0 := by
      linear_combination hI
    rcases mul_eq_zero.1 hmul with h | h
    · exact absurd h hre
    · exact h
  have hGH : β * (G : ℝ) + Real.pi ^ 2 * (H : ℝ) = 0 := by
    have : Real.pi * ((p₁ : ℝ) * n₄ + n₁ * (p₄ : ℝ) - ((p₂ : ℝ) * n₃ + n₂ * (p₃ : ℝ))) = 0 := by
      rw [hY]; ring
    rw [hG, hH]; push_cast
    linear_combination this - (p₁ : ℝ) * hn₄ - (p₄ : ℝ) * hn₁ + (p₂ : ℝ) * hn₃ + (p₃ : ℝ) * hn₂
  have hHz : H = 0 := by
    by_contra hne
    have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hne
    have hval : Real.pi ^ 2 = -(β * (G : ℝ)) / (H : ℝ) := by field_simp; linarith [hGH]
    have halg : IsAlgebraic ℚ (((Real.pi ^ 2 : ℝ)) : ℂ) := by
      rw [hval]; push_cast
      exact alg_div (alg_neg (alg_mul hβalg (alg_rat G))) (alg_rat H)
    refine hpi (IsAlgebraic.of_pow (n := 2) (by norm_num) ?_)
    push_cast at halg; exact halg
  have hGz : G = 0 := by
    have : β * (G : ℝ) = 0 := by rw [hHz] at hGH; push_cast at hGH; linarith [hGH]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ0
    · exact_mod_cast h
  -- real part: the algebraic quartic in `π`
  have hquart : t ^ 2 * Real.pi ^ 2 + (r : ℝ) ^ 2 * Real.pi ^ 4
      - (A + 2 * (r : ℝ) * β) * Real.pi ^ 2 + β ^ 2 = 0 :=
    DiazAligned.aligned_quartic_relation u r A β rfl rfl
  have hN : Real.pi ^ 2 * (n₁ * n₄ - n₂ * n₃)
      = β ^ 2 * (E : ℝ) + β * Real.pi ^ 2 * (J : ℝ) + Real.pi ^ 4 * (F : ℝ) := by
    rw [hE, hJ, hF]; push_cast
    linear_combination (Real.pi * n₄) * hn₁
      + ((e₁ : ℝ) * β + (f₁ : ℝ) * Real.pi ^ 2) * hn₄
      - (Real.pi * n₃) * hn₂ - ((e₂ : ℝ) * β + (f₂ : ℝ) * Real.pi ^ 2) * hn₃
  have hquartic : Real.pi ^ 4 * ((-(P * r ^ 2 + F) : ℚ) : ℝ)
      + Real.pi ^ 2 * ((P : ℝ) * (A + 2 * (r : ℝ) * β) - β * (J : ℝ))
      + (-(β ^ 2 * ((P : ℝ) + (E : ℝ)))) = 0 := by
    push_cast
    linear_combination (-(P : ℝ)) * hquart + Real.pi ^ 2 * hR + hN
      + t ^ 2 * Real.pi ^ 2 * hPR
  -- transcendence: all three coefficients vanish
  have hCplx : (((-(P * r ^ 2 + F) : ℚ) : ℂ)) * ((Real.pi : ℝ) : ℂ) ^ 4
      + ((((P : ℝ) * (A + 2 * (r : ℝ) * β) - β * (J : ℝ) : ℝ)) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2
      + ((((-(β ^ 2 * ((P : ℝ) + (E : ℝ)))) : ℝ)) : ℂ) = 0 := by
    have h := congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) hquartic
    push_cast at h ⊢
    linear_combination h
  have hAlg2 : IsAlgebraic ℚ (((-(P * r ^ 2 + F) : ℚ) : ℂ)) := alg_rat _
  have hAlg1 : IsAlgebraic ℚ ((((P : ℝ) * (A + 2 * (r : ℝ) * β) - β * (J : ℝ) : ℝ)) : ℂ) := by
    have e : ((((P : ℝ) * (A + 2 * (r : ℝ) * β) - β * (J : ℝ) : ℝ)) : ℂ)
        = ((P : ℚ) : ℂ) * (((A : ℝ) : ℂ) + 2 * ((r : ℚ) : ℂ) * ((β : ℝ) : ℂ))
          - ((β : ℝ) : ℂ) * ((J : ℚ) : ℂ) := by push_cast; ring
    rw [e]
    exact alg_sub (alg_mul (alg_rat P) (alg_add hAalg
      (alg_mul (alg_mul (alg_rat 2) (alg_rat r)) hβalg))) (alg_mul hβalg (alg_rat J))
  have hAlg0 : IsAlgebraic ℚ ((((-(β ^ 2 * ((P : ℝ) + (E : ℝ)))) : ℝ)) : ℂ) := by
    have e : ((((-(β ^ 2 * ((P : ℝ) + (E : ℝ)))) : ℝ)) : ℂ)
        = -(((β : ℝ) : ℂ) ^ 2 * (((P : ℚ) : ℂ) + ((E : ℚ) : ℂ))) := by push_cast; ring
    rw [e]
    exact alg_neg (alg_mul (alg_pow hβalg 2) (alg_add (alg_rat P) (alg_rat E)))
  obtain ⟨z2, z1, z0⟩ := pi_no_alg_quartic hpi hAlg0 hAlg1 hAlg2 hCplx
  have hF' : -(P * r ^ 2 + F) = 0 := by exact_mod_cast z2
  have hC1 : (P : ℝ) * (A + 2 * (r : ℝ) * β) - β * (J : ℝ) = 0 := by
    exact_mod_cast z1
  have hC0 : -(β ^ 2 * ((P : ℝ) + (E : ℝ))) = 0 := by exact_mod_cast z0
  -- `P = 0` is exactly where the norm-free hypothesis bites
  have hPz : P = 0 := by
    by_contra hne
    have hPR : (P : ℝ) ≠ 0 := by exact_mod_cast hne
    refine hfree ⟨(J - 2 * r * P) / P, ?_⟩
    have : (P : ℝ) * A = β * ((J : ℝ) - 2 * (r : ℝ) * (P : ℝ)) := by linarith [hC1]
    push_cast
    field_simp
    linear_combination this
  have hEz : E = 0 := by
    rw [hPz] at hC0
    have hβ2 : β ^ 2 ≠ 0 := pow_ne_zero 2 hβ0
    have : β ^ 2 * ((E : ℝ)) = 0 := by push_cast at hC0 ⊢; linarith [hC0]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ2
    · exact_mod_cast h
  have hFz : F = 0 := by rw [hPz] at hF'; linarith [hF']
  have hJz : J = 0 := by
    rw [hPz] at hC1
    have : β * (J : ℝ) = 0 := by push_cast at hC1 ⊢; linarith [hC1]
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hβ0
    · exact_mod_cast h
  -- the determinant form vanishes identically on the rational span
  have hid : ∀ α γ δ : ℚ,
      (α * p₁ + γ * e₁ + δ * f₁) * (α * p₄ + γ * e₄ + δ * f₄)
        = (α * p₂ + γ * e₂ + δ * f₂) * (α * p₃ + γ * e₃ + δ * f₃) := by
    intro α γ δ
    have hP' : p₁ * p₄ - p₂ * p₃ = 0 := by rw [← hP]; exact hPz
    have hE' : e₁ * e₄ - e₂ * e₃ = 0 := by rw [← hE]; exact hEz
    have hF'' : f₁ * f₄ - f₂ * f₃ = 0 := by rw [← hF]; exact hFz
    have hG' : p₁ * e₄ + e₁ * p₄ - p₂ * e₃ - e₂ * p₃ = 0 := by rw [← hG]; exact hGz
    have hH' : p₁ * f₄ + f₁ * p₄ - p₂ * f₃ - f₂ * p₃ = 0 := by rw [← hH]; exact hHz
    have hJ' : e₁ * f₄ + f₁ * e₄ - e₂ * f₃ - f₂ * e₃ = 0 := by rw [← hJ]; exact hJz
    linear_combination α ^ 2 * hP' + γ ^ 2 * hE' + δ ^ 2 * hF''
      + α * γ * hG' + α * δ * hH' + γ * δ * hJ'
  -- transport back to the entries
  have combine : ∀ (a b pk ek fk pj ej fj : ℚ) (mk mj : ℝ) (lk lj : ℂ),
      Real.pi * mk = (ek : ℝ) * β + (fk : ℝ) * Real.pi ^ 2 →
      Real.pi * mj = (ej : ℝ) * β + (fj : ℝ) * Real.pi ^ 2 →
      lk = (((pk : ℝ) * t : ℝ) : ℂ) + ((mk : ℝ) : ℂ) * Complex.I →
      lj = (((pj : ℝ) * t : ℝ) : ℂ) + ((mj : ℝ) : ℂ) * Complex.I →
      a * pk + b * pj = 0 → a * ek + b * ej = 0 → a * fk + b * fj = 0 →
      (a : ℂ) * lk + (b : ℂ) * lj = 0 := by
    intro a b pk ek fk pj ej fj mk mj lk lj hk hj hlk hlj q1 q2 q3
    have q1' : (a : ℝ) * (pk : ℝ) + (b : ℝ) * (pj : ℝ) = 0 := by exact_mod_cast q1
    have q2' : (a : ℝ) * (ek : ℝ) + (b : ℝ) * (ej : ℝ) = 0 := by exact_mod_cast q2
    have q3' : (a : ℝ) * (fk : ℝ) + (b : ℝ) * (fj : ℝ) = 0 := by exact_mod_cast q3
    have hmm : (a : ℝ) * mk + (b : ℝ) * mj = 0 := by
      have hmul : Real.pi * ((a : ℝ) * mk + (b : ℝ) * mj) = 0 := by
        linear_combination (a : ℝ) * hk + (b : ℝ) * hj + β * q2' + Real.pi ^ 2 * q3'
      rcases mul_eq_zero.1 hmul with h | h
      · exact absurd h hπ
      · exact h
    have hpp : (a : ℝ) * ((pk : ℝ) * t) + (b : ℝ) * ((pj : ℝ) * t) = 0 := by
      linear_combination t * q1'
    rw [hlk, hlj]
    have hshape : (a : ℂ) * ((((pk : ℝ) * t : ℝ) : ℂ) + ((mk : ℝ) : ℂ) * Complex.I)
        + (b : ℂ) * ((((pj : ℝ) * t : ℝ) : ℂ) + ((mj : ℝ) : ℂ) * Complex.I)
        = ((((a : ℝ) * ((pk : ℝ) * t) + (b : ℝ) * ((pj : ℝ) * t)) : ℝ) : ℂ)
          + ((((a : ℝ) * mk + (b : ℝ) * mj) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hshape, hpp, hmm]; simp
  rcases rank_one_dichotomy hid with ⟨a, b, hab, k1, k2, k3, k4, k5, k6⟩
    | ⟨a, b, hab, k1, k2, k3, k4, k5, k6⟩
  · exact Or.inr ⟨a, b, hab,
      combine a b p₁ e₁ f₁ p₂ e₂ f₂ n₁ n₂ l₁ l₂ hn₁ hn₂ hl₁ hl₂ k1 k2 k3,
      combine a b p₃ e₃ f₃ p₄ e₄ f₄ n₃ n₄ l₃ l₄ hn₃ hn₄ hl₃ hl₄ k4 k5 k6⟩
  · exact Or.inl ⟨a, b, hab,
      combine a b p₁ e₁ f₁ p₃ e₃ f₃ n₁ n₃ l₁ l₃ hn₁ hn₃ hl₁ hl₃ k1 k2 k3,
      combine a b p₂ e₂ f₂ p₄ e₄ f₄ n₂ n₄ l₂ l₄ hn₂ hn₄ hl₂ hl₄ k4 k5 k6⟩

/-! ## 5.  Two corollaries.

The first says what the no-go is for: on this half the hypothesis package of the four
exponentials statement is *unsatisfiable* over the certified logarithm space.  The second
checks that the no-go is not vacuous, on the machine-checked witness `wC` of
`DZ_ALIGNED_core.lean` (`‖wC‖² = 16√2`, `β = 1`, so `‖wC‖² ∉ ℚ·β`). -/

/-- The hypotheses of `DiazAligned.FourExpDet` cannot be met by a determinant-zero matrix over
`span_ℚ {u, conj u, 2πi}` on the norm-free half. -/
theorem fourExp_hypotheses_unsatisfiable
    (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    (u : ℂ) (r : ℚ)
    (hre : u.re ≠ 0)
    (hβ0 : Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0)
    (hβalg : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ))
    (hAalg : IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ))
    (hfree : ¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi)))
    {l₁ l₂ l₃ l₄ : ℂ}
    (hm₁ : MemL3 u l₁) (hm₂ : MemL3 u l₂) (hm₃ : MemL3 u l₃) (hm₄ : MemL3 u l₄)
    (hrows : ∀ a b : ℚ, (a : ℂ) * l₁ + (b : ℂ) * l₃ = 0 → (a : ℂ) * l₂ + (b : ℂ) * l₄ = 0 →
      a = 0 ∧ b = 0)
    (hcols : ∀ a b : ℚ, (a : ℂ) * l₁ + (b : ℂ) * l₂ = 0 → (a : ℂ) * l₃ + (b : ℂ) * l₄ = 0 →
      a = 0 ∧ b = 0)
    (hdet : l₁ * l₄ - l₂ * l₃ = 0) : False := by
  rcases no_admissible_matrix hpi u r hre hβ0 hβalg hAalg hfree hm₁ hm₂ hm₃ hm₄ hdet with
    ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
  · obtain ⟨ha, hb⟩ := hrows a b h1 h2
    rcases hab with h | h
    · exact h ha
    · exact h hb
  · obtain ⟨ha, hb⟩ := hcols a b h1 h2
    rcases hab with h | h
    · exact h ha
    · exact h hb

/-- The witness `wC` of `DZ_ALIGNED_core.lean` really does satisfy every hypothesis of
`no_admissible_matrix`, with `r = 1`, `β = 1`, `‖wC‖² = 16√2`. -/
theorem wC_no_admissible_matrix (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {l₁ l₂ l₃ l₄ : ℂ}
    (hm₁ : MemL3 DiazAligned.wC l₁) (hm₂ : MemL3 DiazAligned.wC l₂)
    (hm₃ : MemL3 DiazAligned.wC l₃) (hm₄ : MemL3 DiazAligned.wC l₄)
    (hdet : l₁ * l₄ - l₂ * l₃ = 0) :
    (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        (a : ℂ) * l₁ + (b : ℂ) * l₃ = 0 ∧ (a : ℂ) * l₂ + (b : ℂ) * l₄ = 0)
  ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
        (a : ℂ) * l₁ + (b : ℂ) * l₂ = 0 ∧ (a : ℂ) * l₃ + (b : ℂ) * l₄ = 0) := by
  have him : DiazAligned.wC.im = DiazLeafSplit.yA := rfl
  have hb1 : Real.pi * (DiazAligned.wC.im + ((1 : ℚ) : ℝ) * Real.pi) = 1 := by
    rw [him]; exact DiazAligned.beta_yA
  refine no_admissible_matrix hpi DiazAligned.wC 1 (ne_of_gt DiazAligned.wC_re_pos)
    (by rw [hb1]; exact one_ne_zero) ?_ ?_ ?_ hm₁ hm₂ hm₃ hm₄ hdet
  · rw [hb1]; simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))
  · have h := DiazAligned.norm_wC_alg
    have := alg_pow h 2
    have e : ((((‖DiazAligned.wC‖ : ℝ)) ^ 2 : ℝ) : ℂ) = (((‖DiazAligned.wC‖ : ℝ)) : ℂ) ^ 2 := by
      push_cast; ring
    rw [e]; exact this
  · rintro ⟨c, hc⟩
    rw [hb1, DiazAligned.norm_wC_sq] at hc
    exact irrational_sqrt_two ⟨c / 16, by push_cast; linarith [hc]⟩

end DiazFree

end

open Complex ComplexConjugate

open DiazModulus in
theorem solution :
    ∀ (u : ℂ) (r : ℚ),
      Transcendental ℚ ((Real.pi : ℝ) : ℂ) →
      u.re ≠ 0 →
      Real.pi * (u.im + (r : ℝ) * Real.pi) ≠ 0 →
      IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) →
      IsAlgebraic ℚ ((((‖u‖ : ℝ)) ^ 2 : ℝ) : ℂ) →
      (¬ ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      ∀ l : Fin 2 → Fin 2 → ℂ,
        (∀ i j, ∃ a b c : ℚ, l i j = (a : ℂ) * u + (b : ℂ) * (starRingEnd ℂ) u
          + (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I)) →
        l 0 0 * l 1 1 - l 0 1 * l 1 0 = 0 →
        (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 1 0 = 0 ∧
            (a : ℂ) * l 0 1 + (b : ℂ) * l 1 1 = 0)
      ∨ (∃ a b : ℚ, (a ≠ 0 ∨ b ≠ 0) ∧
            (a : ℂ) * l 0 0 + (b : ℂ) * l 0 1 = 0 ∧
            (a : ℂ) * l 1 0 + (b : ℂ) * l 1 1 = 0) := by
  intro u r hpi hre hβ0 hβalg hAalg hfree l hl hdet
  exact DiazFree.no_admissible_matrix hpi u r hre hβ0 hβalg hAalg hfree
    (hl 0 0) (hl 0 1) (hl 1 0) (hl 1 1) hdet
