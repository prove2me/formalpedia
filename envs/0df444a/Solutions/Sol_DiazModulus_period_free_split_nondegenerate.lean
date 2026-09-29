-- Prove2me | solution 1 for DiazModulus.period_free_split_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-13T10:46:08.633659+00:00
-- url     : https://prove2.me/submissions/f0bd0fab-28a2-4850-84dd-e34319d289bc

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_pi_transcendental

section

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

/-!
# One more generation under leaf 2's period-free child

`DiazModulus.diaz_of_exp_not_real_irrational_angle` was split on

```
PeriodAligned u  :⟺  ∃ r ∈ ℚ, r ≠ 0 ∧ π (Im u + r π) ∈ Q̄
```

into `..._period_aligned` and `..._period_free`.  The clause `r ≠ 0` is there for the
*geometric* reading of the predicate (`r = n/q` with `n` the index of the period translate,
so `n = 0` is not a second fibre point).  It is **not** needed for the arithmetic that makes
the aligned half tractable: the published route lemma
`DiazModulus.recip_pi_log_of_period_aligned` never uses `r ≠ 0`, and its `r = 0` instance is
even shorter.

Consequence: the *degenerate* case `r = 0`, i.e. `π · Im u ∈ Q̄`, was left on the **free**
side of the split, although it behaves exactly like the aligned side.  This file splits the
period-free child on that predicate and proves the resulting halves honest.

Everything here is `sorry`-free.  `Transcendental ℚ π` is taken as an explicit hypothesis
wherever it is needed; nothing is imported from the platform.
-/

open Complex ComplexConjugate

namespace DiazLeaf2Free

open DiazModulus DiazLeafSplit

/-! ## 1.  The predicate, and the two new children -/

/-- **The new split predicate**: `π · Im u` is algebraic.

This is exactly the `r = 0` instance of the parent split's arithmetic condition
`π (Im u + r π) ∈ Q̄`, which `DiazLeafSplit.PeriodAligned` excludes by requiring `r ≠ 0`. -/
def PiImAlg (u : ℂ) : Prop := IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)

/-- **The saturated predicate**: `π (Im u + r π) ∈ Q̄` for some rational `r`, zero allowed.
`RatAligned u ↔ PeriodAligned u ∨ PiImAlg u` (`ratAligned_iff` below). -/
def RatAligned (u : ℂ) : Prop :=
  ∃ r : ℚ, IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)

/-- The period-free child restricted to `π · Im u ∈ Q̄`. -/
def Leaf2FreePiAlg : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (¬ ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ) →
    Transcendental ℚ (Complex.exp u)

/-- The period-free child restricted to `π · Im u ∉ Q̄`.  This is the residual. -/
def Leaf2FreePiTrans : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    (¬ ∃ r : ℚ, r ≠ 0 ∧ IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
    (¬ IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)) →
    Transcendental ℚ (Complex.exp u)

/-! ## 2.  The reduction: the two new halves are exactly the period-free child -/

theorem leaf2free_of_halves (hA : Leaf2FreePiAlg) (hB : Leaf2FreePiTrans) : Leaf2Free := by
  intro u hu0 hmod hnr hax hirr hfree
  by_cases h : IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)
  · exact hA u hu0 hmod hnr hax hirr hfree h
  · exact hB u hu0 hmod hnr hax hirr hfree h

theorem piAlg_of_leaf2free (h : Leaf2Free) : Leaf2FreePiAlg :=
  fun u a b c d e f _ => h u a b c d e f

theorem piTrans_of_leaf2free (h : Leaf2Free) : Leaf2FreePiTrans :=
  fun u a b c d e f _ => h u a b c d e f

theorem leaf2free_iff_halves : Leaf2Free ↔ (Leaf2FreePiAlg ∧ Leaf2FreePiTrans) :=
  ⟨fun h => ⟨piAlg_of_leaf2free h, piTrans_of_leaf2free h⟩,
   fun h => leaf2free_of_halves h.1 h.2⟩

/-- Leaf 2 from the three leaves of the two-generation tree. -/
theorem leaf2_of_three (hAl : Leaf2Aligned) (hA : Leaf2FreePiAlg) (hB : Leaf2FreePiTrans) :
    Leaf2 :=
  leaf2_of_halves hAl (leaf2free_of_halves hA hB)

end DiazLeaf2Free

namespace DiazLeaf2Free

open DiazModulus DiazLeafSplit

/-! ## 3.  The route lemma, with the `r ≠ 0` clause removed

`DiazLeafSplit.recip_pi_of_aligned_candidate` is stated with `r ≠ 0`, and the published node
`DiazModulus.recip_pi_log_of_period_aligned` carries the same clause, but neither proof uses
it.  Here is the version that does not assume it; the `r = 0` instance is what the new
`PiImAlg` half needs. -/

theorem recip_pi_of_ratAligned_candidate (u : ℂ)
    (hirr : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi)
    (hal : RatAligned u)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) :
    ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ γ ≠ 0 ∧
      IsAlgebraic ℚ (Complex.exp (γ / ((Real.pi : ℂ) * Complex.I))) := by
  obtain ⟨r, halg⟩ := hal
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
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
  have hexpν : IsAlgebraic ℚ (Complex.exp ν) := by
    refine IsAlgebraic.of_pow (n := 2 * r.den) (by positivity) ?_
    rw [hkey]
    exact alg_pow (alg_div hexp (alg_conj hexp)) r.den
  refine ⟨-(((Real.pi * s : ℝ)) : ℂ), alg_neg (by rw [hs_def] at halg ⊢; exact halg), ?_, ?_⟩
  · simp only [neg_ne_zero, Complex.ofReal_ne_zero]
    exact mul_ne_zero hπ0 hs0
  · have hid : -(((Real.pi * s : ℝ)) : ℂ) / (((Real.pi : ℝ) : ℂ) * Complex.I) = ν := by
      rw [hν_def]
      push_cast
      field_simp
      ring_nf
      rw [Complex.I_sq]
    rw [hid]
    exact hexpν

/-- The `r = 0` instance: `π · Im u ∈ Q̄` already forces an algebraic multiple of `1/(iπ)`
into `ℒ`.  This is the route lemma for the new `Leaf2FreePiAlg` half, and it is *shorter*
than the aligned one — no period translate is involved, `ν` is literally `(u − ū)/2`. -/
theorem recip_pi_of_piImAlg_candidate (u : ℂ)
    (hirr : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi)
    (hpa : PiImAlg u)
    (hexp : IsAlgebraic ℚ (Complex.exp u)) :
    ∃ γ : ℂ, IsAlgebraic ℚ γ ∧ γ ≠ 0 ∧
      IsAlgebraic ℚ (Complex.exp (γ / ((Real.pi : ℂ) * Complex.I))) := by
  refine recip_pi_of_ratAligned_candidate u hirr ⟨0, ?_⟩ hexp
  have : (Real.pi * (u.im + ((0 : ℚ) : ℝ) * Real.pi) : ℝ) = (Real.pi * u.im : ℝ) := by
    push_cast; ring
  rw [this]
  exact hpa

end DiazLeaf2Free

namespace DiazLeaf2Free

open DiazModulus DiazLeafSplit

/-! ## 4.  The two predicates are complementary where it matters

`PiImAlg` and `PeriodAligned` are **mutually exclusive** (given `π` transcendental), so the
free-child hypothesis `¬ PeriodAligned u` is redundant on the `PiImAlg` half, and the union
of the aligned child with the new `PiImAlg` child is exactly the saturated region
`RatAligned`. -/

theorem ratAligned_iff {u : ℂ} : RatAligned u ↔ (PeriodAligned u ∨ PiImAlg u) := by
  constructor
  · rintro ⟨r, halg⟩
    by_cases hr : r = 0
    · right
      subst hr
      have hz : (Real.pi * (u.im + ((0 : ℚ) : ℝ) * Real.pi) : ℝ) = (Real.pi * u.im : ℝ) := by
        push_cast; ring
      rw [hz] at halg
      exact halg
    · exact Or.inl ⟨r, hr, halg⟩
  · rintro (⟨r, _, halg⟩ | hpa)
    · exact ⟨r, halg⟩
    · refine ⟨0, ?_⟩
      have hz : (Real.pi * (u.im + ((0 : ℚ) : ℝ) * Real.pi) : ℝ) = (Real.pi * u.im : ℝ) := by
        push_cast; ring
      rw [hz]
      exact hpa

/-- `π · Im u ∈ Q̄` forces `¬ PeriodAligned u`: the free-child hypothesis carried by the new
`PiImAlg` child is **redundant**, not load-bearing. -/
theorem not_periodAligned_of_piImAlg (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {u : ℂ} (hpa : PiImAlg u) : ¬ PeriodAligned u := by
  rintro ⟨r, hr0, halg⟩
  refine pi_not_quadratic hpi (r := r) (b := 0) hr0 ?_
  have hsplit : ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)
      = ((Real.pi * u.im : ℝ) : ℂ)
        + (((0 : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) + ((r : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2) := by
    push_cast; ring
  rw [hsplit] at halg
  have := (alg_iff_mem).1 halg
  have hbase := (alg_iff_mem).1 hpa
  exact (alg_iff_mem).2 (by simpa using Subfield.sub_mem _ this hbase)

/-- Conversely `PeriodAligned u` forces `¬ PiImAlg u`: the two children below the parent's
aligned/free split are disjoint, and their union is `RatAligned`. -/
theorem not_piImAlg_of_periodAligned (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ))
    {u : ℂ} (hal : PeriodAligned u) : ¬ PiImAlg u :=
  fun hpa => not_periodAligned_of_piImAlg hpi hpa hal

end DiazLeaf2Free

namespace DiazLeaf2Free

open DiazModulus DiazLeafSplit

/-! ## 5.  Both new halves are non-empty, with explicit witnesses

`wC = √(16 − 1/π²) + i/π`: modulus `4`, `π · Im wC = 1`.
`wB = √15 + i` (the sibling file's period-free witness): modulus `4`, `π · Im wB = π`. -/

noncomputable def yC : ℝ := 1 / Real.pi

noncomputable def wC : ℂ := ⟨Real.sqrt (16 - yC ^ 2), yC⟩

theorem yC_pos : 0 < yC := by
  have := pi_pos'
  unfold yC; positivity

theorem yC_lt : yC < 1 / 3 := by
  have h3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  unfold yC
  rw [div_lt_div_iff₀ hpos (by norm_num)]
  linarith

theorem yC_sq_lt : yC ^ 2 < 16 := by
  nlinarith [yC_pos, yC_lt]

theorem norm_wC : ‖wC‖ = 4 := by
  have h1 : (0 : ℝ) ≤ 16 - yC ^ 2 := by linarith [yC_sq_lt]
  have h2 : Complex.normSq wC = 16 := by
    rw [wC, Complex.normSq_mk, Real.mul_self_sqrt h1]; ring
  have h3 : ‖wC‖ ^ 2 = 16 := by rw [← Complex.normSq_eq_norm_sq, h2]
  nlinarith [norm_nonneg wC, h3]

theorem wC_re_pos : 0 < wC.re := by
  have h1 : (0 : ℝ) < 16 - yC ^ 2 := by linarith [yC_sq_lt]
  simpa [wC] using Real.sqrt_pos.2 h1

theorem wC_im : wC.im = 1 / Real.pi := rfl

theorem pi_mul_wC_im : (Real.pi * wC.im : ℝ) = 1 := by
  rw [wC_im]
  field_simp

theorem wC_not_pi_rat (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    ¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi := by
  rintro ⟨q, hq⟩
  have hpos : (0 : ℝ) < Real.pi := pi_pos'
  have hy : (1 / Real.pi : ℝ) = (q : ℝ) * Real.pi := by rw [← wC_im]; exact hq
  have h1 : (1 / Real.pi) * Real.pi = 1 := by field_simp
  have hmul : (1 / Real.pi) * Real.pi = ((q : ℝ) * Real.pi) * Real.pi := by rw [hy]
  have hkey : (q : ℝ) * Real.pi ^ 2 = 1 := by nlinarith [hmul, h1]
  by_cases hq0 : (q : ℚ) = 0
  · have hz : ((q : ℚ) : ℝ) = 0 := by exact_mod_cast hq0
    rw [hz] at hkey; norm_num at hkey
  · refine pi_not_quadratic hpi (r := q) (b := 0) hq0 ?_
    have hval : ((0 : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ)
        + ((q : ℚ) : ℂ) * ((Real.pi : ℝ) : ℂ) ^ 2 = 1 := by
      have hcast : ((((q : ℝ)) * Real.pi ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by rw [hkey]
      push_cast at hcast ⊢
      linear_combination hcast
    rw [hval]
    simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))

/-- The new `PiImAlg` half of the period-free child is non-empty. -/
theorem wC_mem_free_piAlg (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wC ≠ 0 ∧ IsAlgebraic ℚ ((‖wC‖ : ℝ) : ℂ) ∧ (Complex.exp wC).im ≠ 0 ∧
      ¬ (wC.im = 0 ∨ wC.re = 0) ∧ (¬ ∃ q : ℚ, wC.im = (q : ℝ) * Real.pi) ∧
      ¬ PeriodAligned wC ∧ PiImAlg wC := by
  have hre : wC.re ≠ 0 := ne_of_gt wC_re_pos
  have him : wC.im ≠ 0 := by rw [wC_im]; positivity
  have hpiim : PiImAlg wC := by
    unfold PiImAlg
    rw [pi_mul_wC_im]
    have : (((1 : ℝ)) : ℂ) = ((1 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  refine ⟨?_, ?_, exp_im_ne_zero_of_not_pi_rat (wC_not_pi_rat hpi), ?_,
    wC_not_pi_rat hpi, not_periodAligned_of_piImAlg hpi hpiim, hpiim⟩
  · intro h; exact hre (by rw [h]; rfl)
  · rw [norm_wC]
    have : (((4 : ℝ)) : ℂ) = ((4 : ℚ) : ℂ) := by push_cast; ring
    rw [this]; exact alg_rat _
  · rintro (h | h)
    · exact him h
    · exact hre h

/-- The residual half of the period-free child is non-empty: the sibling file's witness
`wB = √15 + i` has `π · Im wB = π ∉ Q̄`. -/
theorem wB_mem_free_piTrans (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) :
    wB ≠ 0 ∧ IsAlgebraic ℚ ((‖wB‖ : ℝ) : ℂ) ∧ (Complex.exp wB).im ≠ 0 ∧
      ¬ (wB.im = 0 ∨ wB.re = 0) ∧ (¬ ∃ q : ℚ, wB.im = (q : ℝ) * Real.pi) ∧
      ¬ PeriodAligned wB ∧ ¬ PiImAlg wB := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := wB_mem_free hpi
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  intro hpa
  unfold PiImAlg at hpa
  refine hpi ?_
  have hb : wB.im = 1 := rfl
  have hz : ((Real.pi * wB.im : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := by
    rw [hb]; push_cast; ring
  rw [hz] at hpa
  exact hpa

end DiazLeaf2Free

namespace DiazLeaf2Free

open DiazModulus DiazLeafSplit

/-! ## 6.  The new predicate is invariant under the rational-scaling action

Same check as for `PeriodAligned`: the mechanism that collapses a split on this mission —
carry a counterexample back onto the parent by `u ↦ q u` (`Diaz.locus_stable`) — does not
apply.  This does not prove strictness; it only removes the known collapse. -/

theorem piImAlg_ratMul {u : ℂ} {q : ℚ} (hq : q ≠ 0) :
    PiImAlg ((q : ℂ) * u) ↔ PiImAlg u := by
  have him : ((q : ℂ) * u).im = ((q : ℚ) : ℝ) * u.im := by simp
  constructor
  · intro h
    unfold PiImAlg at h ⊢
    have hid : (Real.pi * u.im : ℝ)
        = ((1 / q : ℚ) : ℝ) * (Real.pi * ((q : ℂ) * u).im) := by
      rw [him]
      have hqR : ((q : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.2 hq
      push_cast
      field_simp
    rw [hid, Complex.ofReal_mul]
    have hcc : ((((1 / q : ℚ) : ℝ)) : ℂ) = ((1 / q : ℚ) : ℂ) := by norm_cast
    rw [hcc]
    exact alg_mul (alg_rat _) h
  · intro h
    unfold PiImAlg at h ⊢
    have hid : (Real.pi * ((q : ℂ) * u).im : ℝ) = ((q : ℚ) : ℝ) * (Real.pi * u.im) := by
      rw [him]; ring
    rw [hid, Complex.ofReal_mul]
    have hcc : ((((q : ℚ) : ℝ)) : ℂ) = ((q : ℚ) : ℂ) := by norm_cast
    rw [hcc]
    exact alg_mul (alg_rat _) h

end DiazLeaf2Free

end

open Complex ComplexConjugate in
theorem solution :
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        IsAlgebraic ℚ ((Real.pi * u.im : ℝ) : ℂ)) ∧
    (∃ u : ℂ, u ≠ 0 ∧ IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) ∧ (Complex.exp u).im ≠ 0 ∧
        ¬ (u.im = 0 ∨ u.re = 0) ∧ (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ∧
        (¬ ∃ r : ℚ, r ≠ 0 ∧
          IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) ∧
        Transcendental ℚ ((Real.pi * u.im : ℝ) : ℂ)) := by
  have hpi := DiazModulus.pi_transcendental
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := DiazLeaf2Free.wC_mem_free_piAlg hpi
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := DiazLeaf2Free.wB_mem_free_piTrans hpi
  exact ⟨⟨_, a1, a2, a3, a4, a5, a6, a7⟩, ⟨_, b1, b2, b3, b4, b5, b6, b7⟩⟩
