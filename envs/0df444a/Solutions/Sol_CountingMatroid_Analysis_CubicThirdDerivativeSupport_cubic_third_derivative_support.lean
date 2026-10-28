-- Prove2me | solution 1 for CountingMatroid.Analysis.CubicThirdDerivativeSupport.cubic_third_derivative_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:47:39.882417+00:00
-- url     : https://prove2.me/submissions/3aee1a14-5f24-47ce-aa47-45987cd9e345

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Count
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Positivity

namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
section


set_option autoImplicit false

/-!
The nonzero entries of the third-derivative tensor of a homogeneous cubic
record exactly its monomial support, including repeated indices. This is a
polynomial-calculus bridge; it asserts no spectral closure property.
-/

namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport

/-- INTERNAL: Three formal derivatives detect exactly the coefficient of the
corresponding degree-three monomial, with a positive multiplicity factor.
TEXLINE: main.tex:340-348 -/
theorem third_derivative_ne_zero_iff {σ : Type} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (s i j : σ) :
    MvPolynomial.constantCoeff (MvPolynomial.pderiv i
      (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) ≠ 0 ↔
    p.coeff (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1) ≠ 0 := by
  simp only [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
    zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
  have h₁ : (0 : ℚ) < ((Finsupp.single i 1 : σ →₀ ℕ) j : ℚ) + 1 := by positivity
  have h₂ : (0 : ℚ) <
      (((Finsupp.single i 1 + Finsupp.single j 1 : σ →₀ ℕ) s : ℕ) : ℚ) + 1 := by
    positivity
  simp only [mul_ne_zero_iff, ne_eq, h₁.ne', h₂.ne', not_false_eq_true, and_true]



end CountingMatroid.Analysis.CubicThirdDerivativeSupport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · identified cubic support with the nonzero third-derivative tensor using degree-three multiset decomposition and positive derivative multiplicities.
-/

end
set_option autoImplicit false

/-!
The nonzero entries of the third-derivative tensor of a homogeneous cubic
record exactly its monomial support, including repeated indices. This is a
polynomial-calculus bridge; it asserts no spectral closure property.
-/

namespace CountingMatroid.Analysis.CubicThirdDerivativeSupport
end CountingMatroid.Analysis.CubicThirdDerivativeSupport
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.CubicThirdDerivativeSupport

/-- INTERNAL: Homogeneous cubic support is exactly the support of its
symmetric third-derivative tensor, read as unordered triples of indices.
TEXLINE: main.tex:340-348 -/
theorem solution {σ : Type} [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (hhom : p.IsHomogeneous 3) (m : σ →₀ ℕ) :
    m ∈ p.support ↔ ∃ s i j,
      MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) ≠ 0 ∧
      m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1 := by
  constructor
  · intro hm
    have hdegree : m.degree = 3 := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hm) (hhom.coeff_eq_zero h)
    have hcard : m.toMultiset.card = 3 := by
      simpa only [Finsupp.card_toMultiset, Finsupp.degree_apply, Finsupp.sum, id_eq] using hdegree
    obtain ⟨i, j, s, htriple⟩ := Multiset.card_eq_three.mp hcard
    have hmtriple : m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1 := by
      rw [Finsupp.toMultiset_eq_iff] at htriple
      rw [htriple]
      ext t
      simp [Multiset.toFinsupp_apply, Finsupp.add_apply, Finsupp.single_apply,
        Multiset.count_cons, Multiset.count_singleton, eq_comm, add_comm, add_left_comm]
    exact ⟨s, i, j, (third_derivative_ne_zero_iff p s i j).mpr
      (by simpa only [← hmtriple] using MvPolynomial.mem_support_iff.mp hm), hmtriple⟩
  · rintro ⟨s, i, j, hnonzero, rfl⟩
    exact MvPolynomial.mem_support_iff.mpr ((third_derivative_ne_zero_iff p s i j).mp hnonzero)
