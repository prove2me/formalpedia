-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_off_axes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T05:27:46.185287+00:00
-- url     : https://prove2.me/submissions/28a2ad46-7d95-451e-bcbe-5edd5f8a138c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_diaz_of_exp_real_generic
import Theorems.Thm_DiazModulus_diaz_of_exp_not_real_irrational_angle

/-!
# The off-axes leaf, split on the rationality of `Im u / π`

`DiazModulus.diaz_of_exp_not_real_off_axes` is the leaf

    u ≠ 0, ‖u‖ algebraic, (exp u).im ≠ 0, ¬(u.im = 0 ∨ u.re = 0) → Transcendental ℚ (exp u).

Writing `u = x + i y` with `x, y ≠ 0`, this file splits it on whether `y / π` is rational,
and proves that the rational half is **logically equivalent** to the sibling leaf
`DiazModulus.diaz_of_exp_real_generic`.  Nothing here is a transcendence result: the two
implications are elementary scaling arguments (multiply by the denominator; divide by an
integer that is not a divisor of the numerator).

Consequence: the whole of the off-axes leaf with `y ∈ πℚ` is *already* the sibling leaf, and
the residual content of the off-axes leaf is exactly the region `y ∉ πℚ`.

Nothing in this file is published.
-/

open Complex ComplexConjugate

namespace DiazModulus

/-! ## The four propositions -/

/-- The sibling leaf `DiazModulus.diaz_of_exp_real_generic`, verbatim, as a `Prop`. -/
def DiazRealGeneric : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im = 0 →
    u.im ≠ 0 → Complex.exp u ≠ 1 → u.re ≠ 0 → Transcendental ℚ (Complex.exp u)

/-- The leaf `DiazModulus.diaz_of_exp_not_real_off_axes`, verbatim, as a `Prop`. -/
def DiazOffAxes : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → Transcendental ℚ (Complex.exp u)

/-- The off-axes leaf restricted to `u.im ∈ π · ℚ`. -/
def DiazOffAxesRatPi : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    Transcendental ℚ (Complex.exp u)

/-- The off-axes leaf restricted to `u.im ∉ π · ℚ`. -/
def DiazOffAxesIrrPi : Prop :=
  ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
    ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
    Transcendental ℚ (Complex.exp u)

/-! ## Algebraicity bookkeeping, through the mission's `Qbar` -/

private theorem alg_natCast_mul {r : ℝ} (n : ℕ) (h : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    IsAlgebraic ℚ (((n * r : ℝ)) : ℂ) := by
  have hcast : (((n * r : ℝ)) : ℂ) = (n : ℂ) * ((r : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ← mem_Qbar_iff]
  exact mul_mem (natCast_mem Qbar n) (mem_Qbar_iff.mpr h)

private theorem alg_div_natCast {r : ℝ} (n : ℕ) (h : IsAlgebraic ℚ ((r : ℝ) : ℂ)) :
    IsAlgebraic ℚ (((r / n : ℝ)) : ℂ) := by
  have hcast : (((r / n : ℝ)) : ℂ) = ((r : ℝ) : ℂ) / (n : ℂ) := by push_cast; ring
  rw [hcast, ← mem_Qbar_iff]
  exact div_mem (mem_Qbar_iff.mpr h) (natCast_mem Qbar n)

private theorem alg_pow {z : ℂ} (n : ℕ) (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (z ^ n) := by
  rw [← mem_Qbar_iff] at *
  exact pow_mem h n

/-! ## The case split itself -/

/-- The two halves recombine to the leaf.  Pure `by_cases`; no content. -/
theorem offAxes_of_ratPi_and_irrPi (h1 : DiazOffAxesRatPi) (h2 : DiazOffAxesIrrPi) :
    DiazOffAxes := by
  intro u hu hnorm him hax
  by_cases hq : ∃ q : ℚ, u.im = (q : ℝ) * Real.pi
  · exact h1 u hu hnorm him hax hq
  · exact h2 u hu hnorm him hax hq

/-! ## The rational half is the sibling leaf -/

/-- **Scaling up.**  If `u` is off the axes with `u.im = q π`, `q ∈ ℚ`, then `q.den • u`
satisfies every hypothesis of the *real* leaf, and its exponential is a power of `exp u`. -/
theorem ratPi_of_realGeneric (h : DiazRealGeneric) : DiazOffAxesRatPi := by
  rintro u hu0 hnorm _him hax ⟨q, hq⟩
  have hre : u.re ≠ 0 := fun hc => hax (Or.inr hc)
  have him0 : u.im ≠ 0 := fun hc => hax (Or.inl hc)
  set s : ℕ := q.den with hs_def
  have hspos : 0 < s := q.pos
  have hsR : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hspos.ne'
  -- the scaled point
  set u' : ℂ := (s : ℂ) * u with hu'_def
  have hu're : u'.re = (s : ℝ) * u.re := by simp [hu'_def]
  have hu'im : u'.im = (s : ℝ) * u.im := by simp [hu'_def]
  -- `s * u.im = q.num * π`
  have hkey : (s : ℝ) * u.im = (q.num : ℝ) * Real.pi := by
    rw [hq, hs_def, Rat.cast_def]
    field_simp
  have hu'im_eq : u'.im = (q.num : ℝ) * Real.pi := by rw [hu'im, hkey]
  -- hypotheses of the real leaf
  have hre' : u'.re ≠ 0 := by
    rw [hu're]; exact mul_ne_zero hsR hre
  have him' : u'.im ≠ 0 := by
    rw [hu'im]; exact mul_ne_zero hsR him0
  have hu'0 : u' ≠ 0 := by
    intro hc; exact hre' (by rw [hc]; simp)
  have hexpim : (Complex.exp u').im = 0 := by
    rw [Complex.exp_im, hu'im_eq, Real.sin_int_mul_pi]; ring
  have hne1 : Complex.exp u' ≠ 1 := by
    intro hc
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hc
    apply hre'
    rw [hn]; simp
  have hnorm' : IsAlgebraic ℚ ((‖u'‖ : ℝ) : ℂ) := by
    have : ‖u'‖ = (s : ℝ) * ‖u‖ := by
      rw [hu'_def, norm_mul]; simp
    rw [this]
    exact alg_natCast_mul s hnorm
  -- conclude
  have htr := h u' hu'0 hnorm' hexpim him' hne1 hre'
  have hpow : Complex.exp u' = Complex.exp u ^ s := by
    rw [hu'_def, Complex.exp_nat_mul]
  intro halg
  exact htr (by rw [hpow]; exact alg_pow s halg)

/-- **Scaling down.**  Conversely, a point of the real leaf becomes an off-axes point with
rational angle after dividing by `|n| + 1`, where `u.im = n π`.  So the rational half is not
merely implied by the sibling leaf — it is equivalent to it. -/
theorem realGeneric_of_ratPi (h : DiazOffAxesRatPi) : DiazRealGeneric := by
  intro u0 hu00 hnorm hreal him0 _hne1 hre0
  -- `u0.im = n π` with `n ≠ 0`
  have hsin : Real.sin u0.im = 0 := by
    have := hreal
    rw [Complex.exp_im] at this
    rcases mul_eq_zero.mp this with hc | hc
    · exact absurd hc (Real.exp_ne_zero _)
    · exact hc
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp hsin
  have hn0 : n ≠ 0 := by
    intro hc; apply him0; rw [← hn, hc]; simp
  -- the divisor
  set k : ℕ := n.natAbs + 1 with hk_def
  have hkpos : 0 < k := Nat.succ_pos _
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hkpos.ne'
  have hknd : ¬ (k : ℤ) ∣ n := by
    intro ⟨m, hm⟩
    have hm0 : m ≠ 0 := by
      intro hc; apply hn0; rw [hm, hc, mul_zero]
    have h1 : (k : ℤ) ≤ (k : ℤ) * |m| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs (by simpa using hm0)
      nlinarith [Int.natCast_nonneg k]
    have h2 : |n| = (k : ℤ) * |m| := by rw [hm, abs_mul]; simp [abs_of_nonneg]
    have h3 : |n| < (k : ℤ) := by
      rw [hk_def]
      have : |n| = (n.natAbs : ℤ) := (Int.abs_eq_natAbs n)
      omega
    omega
  -- the scaled-down point
  set u : ℂ := u0 / (k : ℂ) with hu_def
  have hure : u.re = u0.re / (k : ℝ) := by simp [hu_def]
  have huim : u.im = u0.im / (k : ℝ) := by simp [hu_def]
  have hre : u.re ≠ 0 := by rw [hure]; exact div_ne_zero hre0 hkR
  have him : u.im ≠ 0 := by rw [huim]; exact div_ne_zero him0 hkR
  have hu0' : u ≠ 0 := by intro hc; exact hre (by rw [hc]; simp)
  -- the angle is `n/k` times `π`, and its sine is non-zero
  have huim_eq : u.im = ((n : ℝ) * Real.pi) / (k : ℝ) := by rw [huim, ← hn]
  have hsin' : Real.sin u.im ≠ 0 := by
    intro hc
    obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hc
    rw [huim_eq] at hm
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have : (m : ℝ) * (k : ℝ) = (n : ℝ) := by
      field_simp at hm
      nlinarith [hm, Real.pi_pos]
    have : (m : ℤ) * (k : ℤ) = n := by exact_mod_cast this
    exact hknd ⟨m, by linarith [this]⟩
  have hexpim : (Complex.exp u).im ≠ 0 := by
    rw [Complex.exp_im]
    exact mul_ne_zero (Real.exp_ne_zero _) hsin'
  have hax : ¬ (u.im = 0 ∨ u.re = 0) := by
    rintro (hc | hc)
    · exact him hc
    · exact hre hc
  have hrat : ∃ q : ℚ, u.im = (q : ℝ) * Real.pi := by
    refine ⟨(n : ℚ) / (k : ℚ), ?_⟩
    rw [huim_eq]
    push_cast
    field_simp
  have hnorm' : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) := by
    have : ‖u‖ = ‖u0‖ / (k : ℝ) := by rw [hu_def, norm_div]; simp
    rw [this]
    exact alg_div_natCast k hnorm
  -- conclude
  have htr := h u hu0' hnorm' hexpim hax hrat
  have hpow : Complex.exp u0 = Complex.exp u ^ k := by
    rw [← Complex.exp_nat_mul, hu_def, mul_div_cancel₀ _ hkC]
  intro halg
  exact htr (IsAlgebraic.of_pow hkpos (by rw [← hpow]; exact halg))

/-! ## Headline -/

/-- **The off-axes leaf follows from the sibling leaf together with the irrational-angle
half.**  Combined with `realGeneric_of_ratPi`, this says the off-axes leaf's content beyond
the sibling's is exactly `DiazOffAxesIrrPi`. -/
theorem offAxes_of_realGeneric_and_irrPi (hR : DiazRealGeneric) (hI : DiazOffAxesIrrPi) :
    DiazOffAxes :=
  offAxes_of_ratPi_and_irrPi (ratPi_of_realGeneric hR) hI

/-- The rational-angle half of the off-axes leaf is *equivalent* to the sibling leaf. -/
theorem ratPi_iff_realGeneric : DiazOffAxesRatPi ↔ DiazRealGeneric :=
  ⟨realGeneric_of_ratPi, ratPi_of_realGeneric⟩

/-! ## What the rational-angle condition is, structurally

Off the imaginary axis, `u.im ∈ π·ℚ` is exactly the `ℚ`-linear dependence of the triple
`(u, conj u, 2πi)` — the three elements of `ℒ` that a candidate hands you.  So the split
above is the split on whether that triple is `ℚ`-free, and the residual half
`DiazOffAxesIrrPi` is precisely the half where it is free: the half in which the mission's
free-ring model of the certificate space (`DZ_Sol_freering.lean`, `A = K[X,T]`) has no
relations beyond `u · conj u = ‖u‖²`. -/

/-- Dependence of `(u, conj u, 2πi)` over `ℚ`, spelled out with explicit coefficients so
that no `LinearIndependent` API is involved. -/
def DepTriple (u : ℂ) : Prop :=
  ∃ a b c : ℚ, ¬ (a = 0 ∧ b = 0 ∧ c = 0) ∧
    (a : ℂ) * u + (b : ℂ) * (starRingEnd ℂ) u + (c : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0

theorem ratPi_iff_depTriple {u : ℂ} (hre : u.re ≠ 0) :
    (∃ q : ℚ, u.im = (q : ℝ) * Real.pi) ↔ DepTriple u := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨1, -1, -q, by simp, ?_⟩
    apply Complex.ext <;> simp [hq]
    ring
  · rintro ⟨a, b, c, hne, heq⟩
    rw [Complex.ext_iff] at heq
    obtain ⟨h1, h2⟩ := heq
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ratCast_re, Complex.ratCast_im, Complex.conj_re, Complex.conj_im,
      Complex.zero_re, Complex.zero_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat] at h1 h2
    -- real part: `(a + b) * u.re = 0`
    have hab : (a : ℝ) + (b : ℝ) = 0 := by
      have : ((a : ℝ) + (b : ℝ)) * u.re = 0 := by linarith [h1]
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hre
    have hb : (b : ℝ) = -(a : ℝ) := by linarith
    -- imaginary part: `2 * a * u.im + 2 * π * c = 0`
    have h2' : 2 * (a : ℝ) * u.im + 2 * Real.pi * (c : ℝ) = 0 := by
      rw [hb] at h2; linarith [h2]
    have ha : (a : ℝ) ≠ 0 := by
      intro hazero
      have hbzero : (b : ℝ) = 0 := by rw [hb, hazero]; ring
      have hczero : (c : ℝ) = 0 := by
        have : 2 * Real.pi * (c : ℝ) = 0 := by rw [hazero] at h2'; linarith
        rcases mul_eq_zero.mp this with h | h
        · exact absurd h (by positivity)
        · exact h
      exact hne ⟨by exact_mod_cast hazero, by exact_mod_cast hbzero,
        by exact_mod_cast hczero⟩
    refine ⟨-c / a, ?_⟩
    have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha
    push_cast
    field_simp
    linarith [h2']

/-! ## The leaf is not a fragment: it is the whole conjecture

`DiazOffAxes` has *fewer* hypotheses than `DiazOffAxesRatPi`, so it implies it, and hence —
by `realGeneric_of_ratPi` — implies the sibling leaf.  Since the mission's remaining branches
are proved, the off-axes leaf is therefore equivalent to `DiazModulusConjecture` itself. -/

/-- The off-axes leaf implies the sibling leaf. -/
theorem realGeneric_of_offAxes (h : DiazOffAxes) : DiazRealGeneric :=
  realGeneric_of_ratPi (fun u h1 h2 h3 h4 _ => h u h1 h2 h3 h4)

/-- On either coordinate axis, an algebraic modulus forces `u` itself to be algebraic.
This is the argument of the mission's proved node
`DiazModulus.diaz_on_axes_of_hermite_lindemann`, re-run here so that this file imports only
the definitions. -/
private theorem alg_of_axis {u : ℂ} (hax : u.im = 0 ∨ u.re = 0)
    (hmod : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ)) : IsAlgebraic ℚ u := by
  have key : ((‖u‖ : ℝ) : ℂ) ^ 2 = u * (starRingEnd ℂ) u := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hq : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hmod
  have hsq : u ^ 2 ∈ Qbar := by
    rcases hax with h | h
    · have hc : (starRingEnd ℂ) u = u := Complex.conj_eq_iff_im.mpr h
      have h2 : u ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 := by rw [key, hc]; ring
      rw [h2]; exact pow_mem hq 2
    · have hc : (starRingEnd ℂ) u = -u := by apply Complex.ext <;> simp [h]
      have h2 : u ^ 2 = -(((‖u‖ : ℝ) : ℂ) ^ 2) := by rw [key, hc]; ring
      rw [h2]; exact neg_mem (pow_mem hq 2)
  exact IsAlgebraic.of_pow two_pos (mem_Qbar_iff.mp hsq)

/-- **The off-axes leaf is equivalent to Diaz's modulus conjecture.**  The two inputs are the
mission's own `DiazModulus.hermite_lindemann_holds` and `DiazModulus.pi_transcendental`, both
Proved; they are taken as explicit hypotheses so that nothing is assumed silently. -/
theorem diaz_of_offAxes (hHL : HermiteLindemann)
    (hpi : Transcendental ℚ ((Real.pi : ℝ) : ℂ)) (h : DiazOffAxes) :
    DiazModulusConjecture := by
  have hRG : DiazRealGeneric := realGeneric_of_offAxes h
  intro u hu hmod
  by_cases hax : u.im = 0 ∨ u.re = 0
  · exact hHL u hu (alg_of_axis hax hmod)
  by_cases himexp : (Complex.exp u).im = 0
  · have him : u.im ≠ 0 := fun hc => hax (Or.inl hc)
    have hre : u.re ≠ 0 := fun hc => hax (Or.inr hc)
    by_cases h1 : Complex.exp u = 1
    · exfalso
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have hn0 : n ≠ 0 := by
        intro hc; apply hu; rw [hn, hc]; simp
      have hnR : |(n : ℝ)| ≠ 0 := by
        simpa using (Int.cast_ne_zero (α := ℝ)).mpr hn0
      have hnorm : ‖u‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [hn]
        simp [abs_of_pos Real.pi_pos]
      apply hpi
      have hq : ((‖u‖ : ℝ) : ℂ) ∈ Qbar := mem_Qbar_iff.mpr hmod
      have hc : ((|(n : ℝ)| * 2 : ℝ) : ℂ) ∈ Qbar := by
        have hcast : ((|(n : ℝ)| * 2 : ℝ) : ℂ) = ((|n| * 2 : ℤ) : ℂ) := by
          push_cast [← Int.cast_abs]; ring
        rw [hcast]; exact intCast_mem Qbar _
      have hB : ((|(n : ℝ)| * 2 : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero, mul_eq_zero, not_or]
        exact ⟨hnR, by norm_num⟩
      refine mem_Qbar_iff.mp ?_
      have hpieq : ((Real.pi : ℝ) : ℂ) = ((‖u‖ : ℝ) : ℂ) / ((|(n : ℝ)| * 2 : ℝ) : ℂ) := by
        rw [hnorm, eq_div_iff hB]
        push_cast
        ring
      rw [hpieq]
      exact div_mem hq hc
    · exact hRG u hu hmod himexp him h1 hre
  · exact h u hu hmod himexp hax

/-- The converse is immediate: the conjecture implies the leaf. -/
theorem offAxes_of_diaz (h : DiazModulusConjecture) : DiazOffAxes :=
  fun u hu hmod _ _ => h u hu hmod

end DiazModulus

open DiazModulus in
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → Transcendental ℚ (Complex.exp u) :=
  DiazModulus.offAxes_of_realGeneric_and_irrPi
    (fun u h1 h2 h3 h4 h5 h6 => DiazModulus.diaz_of_exp_real_generic u h1 h2 h3 h4 h5 h6)
    (fun u h1 h2 h3 h4 h5 => DiazModulus.diaz_of_exp_not_real_irrational_angle u h1 h2 h3 h4 h5)
