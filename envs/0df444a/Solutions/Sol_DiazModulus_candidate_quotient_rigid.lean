-- Prove2me | solution 1 for DiazModulus.candidate_quotient_rigid
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:37:40.522826+00:00
-- url     : https://prove2.me/submissions/403a02f8-6ab7-42d8-a3dc-379bbad66632

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_candidate_conj_product_rational
import Theorems.Thm_DiazModulus_conj_ratio_multiplier_relation
import Theorems.Thm_DiazModulus_log_ratio_multipliers

open Complex ComplexConjugate

namespace QuotRigid

/-- `ℒ` is a `ℚ`-vector space: rational multiples of logarithms are logarithms. -/
theorem exp_rat_mul_alg (q : ℚ) {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * w)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  have hden : ((q.den : ℕ) : ℂ) * (q : ℂ) = ((q.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  rw [← Complex.exp_nat_mul, ← mul_assoc, hden, Complex.exp_int_mul]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg q.num
  · rw [hm, zpow_natCast]; exact hw.pow m
  · rw [hm, zpow_neg, zpow_natCast]; exact (hw.pow m).inv

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

end QuotRigid

open QuotRigid in
/-- Three cases. `v ∈ ℚu`: done. `v = a ū`: then `uw/ū = a·(uw/v) ∈ ℒ`, the multiplier relation
makes `Re(uw)` algebraic, and `w ∈ ℚū` by the conjugate-product lemma. Otherwise
`w = a v + b ū`; expanding `|w|²` gives `2ab Re(uv)` algebraic, and `ab ≠ 0` would put
`v ∈ ℚū`. -/
theorem solution (u v w : ℂ) (hu : DiazModulus.IsCandidate u) (hv : DiazModulus.IsCandidate v)
    (hw : DiazModulus.IsCandidate w) (c : ℚ) (hc : u * conj u = (c : ℂ) * (v * conj v))
    (hz : IsAlgebraic ℚ (Complex.exp (u * w / v))) :
    (∃ r : ℚ, v = (r : ℂ) * u) ∨ (∃ r : ℚ, w = (r : ℂ) * v) ∨
      (∃ r : ℚ, w = (r : ℂ) * conj u) := by
  have hu0 := hu.1
  have hv0 := hv.1
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  by_cases h1 : ∃ r : ℚ, v = (r : ℂ) * u
  · exact Or.inl h1
  by_cases h2 : ∃ r : ℚ, v = (r : ℂ) * conj u
  · -- `v = a ū`
    obtain ⟨a, ha⟩ := h2
    have ha0 : (a : ℂ) ≠ 0 := by
      intro h; rw [h, zero_mul] at ha; exact hv0 ha
    -- `u w / ū = a · (u w / v) ∈ ℒ`
    have hsw : IsAlgebraic ℚ (Complex.exp (u * w / conj u)) := by
      have e : u * w / conj u = (a : ℂ) * (u * w / v) := by
        rw [ha]; field_simp
      rw [e]; exact exp_rat_mul_alg a hz
    obtain ⟨a', b, c', hne, hrel⟩ := DiazModulus.conj_ratio_multiplier_relation u w
      (re_ne_zero hu) (im_ne_zero hu) hu.2.2 hw.2.2 hsw
    -- `Re(uw)` is algebraic
    have hX : IsAlgebraic ℚ (((u * w).re : ℝ) : ℂ) := by
      by_cases hY : (u * w).im = 0
      · -- `uw` real: `X² = |u|²|w|²`
        have hsq : (u * w).re ^ 2 = ‖u‖ ^ 2 * ‖w‖ ^ 2 := by
          rw [← mul_pow, ← Complex.norm_mul, ← Complex.normSq_eq_norm_sq,
            Complex.normSq_apply, hY]
          ring
        have hsqC : (((u * w).re : ℝ) : ℂ) ^ 2 = ((‖u‖ : ℝ) : ℂ) ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ 2 := by
          have h := congrArg (fun x : ℝ => (x : ℂ)) hsq
          push_cast at h
          linear_combination h
        exact IsAlgebraic.of_pow two_pos (by rw [hsqC]; exact (hu.2.1.pow 2).mul (hw.2.1.pow 2))
      · obtain ⟨hb0, hXeq⟩ := rel_re hu0 hne hrel hY
        have hb2 : ((2 * b : ℚ) : ℂ) ≠ 0 := by
          push_cast; exact mul_ne_zero two_ne_zero (by exact_mod_cast hb0)
        have hX' : (((u * w).re : ℝ) : ℂ) = -((a' : ℂ) * (u * conj u)) / ((2 * b : ℚ) : ℂ) := by
          rw [eq_div_iff hb2]; push_cast; linear_combination hXeq
        rw [hX', div_eq_mul_inv]
        exact ((ratAlg a').mul (mul_conj_alg hu)).neg.mul (ratAlg (2 * b)).inv
    obtain ⟨r, hr⟩ := DiazModulus.candidate_conj_product_rational u w hu hw hX
    exact Or.inr (Or.inr ⟨r, hr⟩)
  · -- generic case: `w = a v + b ū`
    push Not at h1 h2
    obtain ⟨a, b, hab⟩ := DiazModulus.log_ratio_multipliers u v w hu0 hv0 hu.2.2 hv.2.2 hw.2.2
      c hc h1 h2 hz
    by_cases ha : a = 0
    · right; right
      refine ⟨b, ?_⟩
      rw [hab, ha]; simp
    by_cases hb : b = 0
    · right; left
      refine ⟨a, ?_⟩
      rw [hab, hb]; simp
    exfalso
    have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
    -- `|w|² = a²|v|² + b²|u|² + 2ab Re(uv)`
    have hcw : conj w = (a : ℂ) * conj v + (b : ℂ) * u := by
      rw [hab, map_add, map_mul, map_mul, map_ratCast, map_ratCast, Complex.conj_conj]
    have h2re : u * v + conj u * conj v = 2 * (((u * v).re : ℝ) : ℂ) := by
      have e : conj u * conj v = conj (u * v) := (map_mul _ _ _).symm
      rw [e, Complex.add_conj]; simp
    have key : 2 * (a : ℂ) * (b : ℂ) * (((u * v).re : ℝ) : ℂ)
        = w * conj w - (a : ℂ) ^ 2 * (v * conj v) - (b : ℂ) ^ 2 * (u * conj u) := by
      rw [hcw, hab]
      linear_combination (-(a : ℂ) * (b : ℂ)) * h2re
    have hab2 : ((2 * a * b : ℚ) : ℂ) ≠ 0 := by
      push_cast; exact mul_ne_zero (mul_ne_zero two_ne_zero ha') hb'
    have hX' : (((u * v).re : ℝ) : ℂ)
        = (w * conj w - (a : ℂ) ^ 2 * (v * conj v) - (b : ℂ) ^ 2 * (u * conj u)) /
          ((2 * a * b : ℚ) : ℂ) := by
      rw [eq_div_iff hab2, ← key]; push_cast; ring
    have hX : IsAlgebraic ℚ (((u * v).re : ℝ) : ℂ) := by
      rw [hX', div_eq_mul_inv]
      exact (((mul_conj_alg hw).sub (((ratAlg a).pow 2).mul (mul_conj_alg hv))).sub
        (((ratAlg b).pow 2).mul (mul_conj_alg hu))).mul (ratAlg (2 * a * b)).inv
    obtain ⟨r, hr⟩ := DiazModulus.candidate_conj_product_rational u v hu hv hX
    exact h2 r hr

#print axioms solution
