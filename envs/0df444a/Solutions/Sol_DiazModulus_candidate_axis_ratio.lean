-- Prove2me | solution 1 for DiazModulus.candidate_axis_ratio
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-04T18:33:57.288167+00:00
-- url     : https://prove2.me/submissions/1365509e-89be-40a4-8252-a5c633272290

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_candidate_pair_dichotomy
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_DiazModulus_diaz_on_axes_of_hermite_lindemann

open Complex ComplexConjugate

namespace R4_candidate_axis_ratio

/-- A root `v` of `X² - b X + c`, with `b` and `c` algebraic over a domain `R`, is algebraic
over `R`, because `(2v - b)² = b² - 4c`. -/
theorem alg_of_quadratic {R : Type*} [CommRing R] [IsDomain R] [Algebra R ℂ] {v b c : ℂ}
    (hb : IsAlgebraic R b) (hc : IsAlgebraic R c) (h : v ^ 2 - b * v + c = 0) :
    IsAlgebraic R v := by
  have h2 : (2 * v - b) ^ 2 = b ^ 2 - 4 • c := by
    rw [nsmul_eq_mul]; push_cast; linear_combination 4 * h
  have h3 : IsAlgebraic R ((2 * v - b) ^ 2) := by rw [h2]; exact (hb.pow 2).sub (hc.nsmul 4)
  have h4 := (h3.of_pow two_pos).add hb
  rw [sub_add_cancel] at h4
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero two_ne_zero)
    (by simpa using isAlgebraic_natCast (R := R) (A := ℂ) 2) h4

end R4_candidate_axis_ratio

/- (ii) ⇒ (i) with `m = 1`. (ii) ⇔ (iii) is plane geometry: with `Re v = Re u` (resp.
`Im v = Im u`), `|v| = |u|` leaves `Im v = ± Im u` (resp. `Re v = ± Re u`), and the sign `+` would
give `v = u`. (i) ⇒ (ii): `v - v̄ = u - ū` (resp. `v + v̄ = u + ū`) with `v̄ = |v|²/v` makes `v` a
root of a quadratic over the algebraic closure of `ℚ[u]`, so `u, v` are algebraically dependent and
`candidate_pair_dichotomy` gives `v = c u` or `v = c ū` with `c ∈ ℚ^×`. A candidate lies on neither
axis (Hermite–Lindemann), so comparing real or imaginary parts gives `c = 1` in the first case,
i.e. `v = u`, which is excluded, and `c = ± 1` in the second, hence `|v| = |u|`. -/
open DiazModulus R4_candidate_axis_ratio in
theorem solution (u v : ℂ) (hu : IsCandidate u) (hv : IsCandidate v)
    (huv : u ≠ v) (hτ : (v - u).im = 0 ∨ (v - u).re = 0) :
    ((∃ m : ℚ, v * conj v = (m : ℂ) * (u * conj u)) ↔ ‖v‖ = ‖u‖) ∧
      (‖v‖ = ‖u‖ ↔ (((v - u).re = 0 → v = conj u) ∧ ((v - u).im = 0 → v = -conj u))) := by
  obtain ⟨hu0, hun, hue⟩ := id hu
  obtain ⟨hv0, hvn, hve⟩ := id hv
  have hsq : ∀ w : ℂ, w * conj w = ((‖w‖ : ℝ) : ℂ) ^ 2 := fun w => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  refine ⟨⟨fun ⟨m, hm⟩ => ?_, fun h => ⟨1, by rw [hsq, hsq, h, Rat.cast_one, one_mul]⟩⟩, ?_⟩
  · -- (i) ⇒ (ii). First, `v` is algebraic over `ℚ[u]`.
    have hext : ∀ z : ℂ, IsAlgebraic ℚ z → IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) z :=
      fun z hz => hz.extendScalars (algebraMap ℚ _).injective
    have huu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) u :=
      isAlgebraic_algebraMap (⟨u, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin ℚ ({u} : Set ℂ))
    have hρv := hext (v * conj v) (by rw [hsq]; exact hvn.pow 2)
    have hcu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) (conj u) :=
      IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero hu0) huu
        (hext (u * conj u) (by rw [hsq]; exact hun.pow 2))
    have hvu : IsAlgebraic (Algebra.adjoin ℚ ({u} : Set ℂ)) v := by
      rcases hτ with him | hre
      · rw [Complex.sub_im, sub_eq_zero] at him
        have hvv : v - conj v = u - conj u := Complex.ext (by simp) (by simp [him])
        exact alg_of_quadratic (huu.sub hcu) hρv.neg (by linear_combination v * hvv)
      · rw [Complex.sub_re, sub_eq_zero] at hre
        have hvv : v + conj v = u + conj u := Complex.ext (by simp [hre]) (by simp)
        exact alg_of_quadratic (huu.add hcu) hρv (by linear_combination v * hvv)
    have hdep : ¬ AlgebraicIndependent ℚ ![u, v] := fun h => by
      have himg : ![u, v] '' {0} = {u} := by simp
      have := h.transcendental_adjoin (s := {0}) (i := 1) (by simp)
      rw [himg] at this
      exact this hvu
    -- `u` lies on neither axis
    have hre0 : u.re ≠ 0 := fun h =>
      diaz_on_axes_of_hermite_lindemann hermite_lindemann_holds u hu0 (Or.inr h) hun hue
    have him0 : u.im ≠ 0 := fun h =>
      diaz_on_axes_of_hermite_lindemann hermite_lindemann_holds u hu0 (Or.inl h) hun hue
    rcases (candidate_pair_dichotomy u v hu hv m hm).2 hdep with ⟨c, -, hc⟩ | ⟨c, -, hc⟩
    · -- `v = c u` forces `c = 1`, that is `v = u`
      have hc1 : (c : ℝ) = 1 := by
        rcases hτ with him | hre
        · rw [Complex.sub_im, sub_eq_zero] at him
          have h1 : v.im = (c : ℝ) * u.im := by rw [hc]; simp
          apply mul_right_cancel₀ him0; linarith
        · rw [Complex.sub_re, sub_eq_zero] at hre
          have h1 : v.re = (c : ℝ) * u.re := by rw [hc]; simp
          apply mul_right_cancel₀ hre0; linarith
      exact absurd (by rw [hc, show (c : ℂ) = 1 by exact_mod_cast hc1, one_mul]) huv
    · -- `v = c ū` forces `c = ± 1`
      have hc1 : (c : ℝ) = 1 ∨ (c : ℝ) = -1 := by
        rcases hτ with him | hre
        · rw [Complex.sub_im, sub_eq_zero] at him
          have h1 : v.im = -((c : ℝ) * u.im) := by rw [hc]; simp
          right; apply mul_right_cancel₀ him0; linarith
        · rw [Complex.sub_re, sub_eq_zero] at hre
          have h1 : v.re = (c : ℝ) * u.re := by rw [hc]; simp
          left; apply mul_right_cancel₀ hre0; linarith
      rw [hc, norm_mul, Complex.norm_conj]
      rcases hc1 with h | h
      · rw [show (c : ℂ) = 1 by exact_mod_cast h, norm_one, one_mul]
      · rw [show (c : ℂ) = -1 by exact_mod_cast h, norm_neg, norm_one, one_mul]
  · -- (ii) ⇔ (iii)
    constructor
    · intro h
      have h2 : v.re * v.re + v.im * v.im = u.re * u.re + u.im * u.im := by
        rw [← Complex.normSq_apply, ← Complex.normSq_apply, ← Complex.sq_norm,
          ← Complex.sq_norm, h]
      refine ⟨fun hre => ?_, fun him => ?_⟩
      · rw [Complex.sub_re, sub_eq_zero] at hre
        have h3 : (v.im - u.im) * (v.im + u.im) = 0 := by
          rw [hre] at h2; linear_combination h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (Complex.ext hre.symm (by linarith)) huv
        · exact Complex.ext (by simp [hre]) (by simp; linarith)
      · rw [Complex.sub_im, sub_eq_zero] at him
        have h3 : (v.re - u.re) * (v.re + u.re) = 0 := by
          rw [him] at h2; linear_combination h2
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (Complex.ext (by linarith) him.symm) huv
        · exact Complex.ext (by simp; linarith) (by simp [him])
    · rintro ⟨h1, h2⟩
      rcases hτ with him | hre
      · rw [h2 him, norm_neg, Complex.norm_conj]
      · rw [h1 hre, Complex.norm_conj]

#print axioms solution
