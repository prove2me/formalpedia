-- Prove2me | solution 1 for DiazModulus.torusVanishing_torusZero
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T10:06:33.545986+00:00
-- url     : https://prove2.me/submissions/8840f97b-5eeb-4c3b-addd-20cdf5fec50f

import Mathlib
import Definitions.Def_DiazMultiplicity

open Complex ComplexConjugate

/-! # The Nullstellensatz on the torus: `I(Z_G(𝔟)) = √𝔟` for `J₀ ≤ 𝔟`

Write `R = K[X, Y, Z]` and let `𝔟 ⊇ J₀ = (Y_iZ_i − 1)_i`. A point `x` of the affine zero locus of `𝔟` satisfies
`x(Y_i) x(Z_i) = 1`, so `x(Y_i)` is a unit with inverse `x(Z_i)` and `x = torusPt g` for
`g = (x|_X, (x(Y_i))_i)`; conversely every `torusPt g` with `g ∈ Z_G(𝔟)` lies in the affine zero locus. Hence the
affine zero locus of `𝔟` is the image `torusPt '' Z_G(𝔟)`, and `I(Z_G(𝔟))` is its vanishing ideal. Mathlib's
Nullstellensatz `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical` (finitely many variables, `K` algebraically
closed) gives `I(Z_G(𝔟)) = √𝔟`. If `Z_G(𝔟) = ∅`, then `I(∅) = ⊤ = √𝔟`, so `𝔟 = ⊤` (`Ideal.radical_eq_top`). -/

namespace C13_V1
open DiazModulus MvPolynomial

/-- A point with `x(Y_i) x(Z_i) = 1` for all `i` is a torus point. -/
theorem exists_torusPt_eq {K A₀ A₁ : Type*} [Field K] (x : A₀ ⊕ (A₁ × Bool) → K)
    (hx : ∀ i, x (Sum.inr (i, true)) * x (Sum.inr (i, false)) = 1) :
    ∃ g : TorusGroup K A₀ A₁, torusPt g = x := by
  refine ⟨(Multiplicative.ofAdd (fun h => x (Sum.inl h)),
    fun i => ⟨x (Sum.inr (i, true)), x (Sum.inr (i, false)), hx i, by rw [mul_comm]; exact hx i⟩), ?_⟩
  funext v
  rcases v with h | ⟨i, b⟩
  · rfl
  · cases b <;> rfl

/-- The affine zero locus of `𝔟 ⊇ J₀` is the image of `Z_G(𝔟)` under `torusPt`. -/
theorem zeroLocus_eq_image {K A₀ A₁ : Type*} [Field K]
    (𝔟 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) (h𝔟 : torusIdeal K A₀ A₁ ≤ 𝔟) :
    zeroLocus K 𝔟 = torusPt '' torusZero 𝔟 := by
  ext x
  simp only [mem_zeroLocus_iff, Set.mem_image]
  constructor
  · intro hx
    have hu : ∀ i, x (Sum.inr (i, true)) * x (Sum.inr (i, false)) = 1 := by
      intro i
      have hmem : (X (Sum.inr (i, true)) * X (Sum.inr (i, false)) - 1 :
          MvPolynomial (A₀ ⊕ (A₁ × Bool)) K) ∈ 𝔟 :=
        h𝔟 (Ideal.subset_span ⟨i, rfl⟩)
      have := hx _ hmem
      simpa [sub_eq_zero] using this
    obtain ⟨g, hg⟩ := exists_torusPt_eq x hu
    refine ⟨g, fun f hf => ?_, hg⟩
    rw [hg]
    exact hx f hf
  · rintro ⟨g, hg, rfl⟩ f hf
    exact hg f hf

/-- `I(S)` is the vanishing ideal of the image of `S` under `torusPt`. -/
theorem torusVanishing_eq_vanishingIdeal {K A₀ A₁ : Type*} [Field K] (S : Set (TorusGroup K A₀ A₁)) :
    torusVanishing S = vanishingIdeal K (torusPt '' S) := by
  ext f
  simp only [torusVanishing, Ideal.mem_iInf, RingHom.mem_ker, mem_vanishingIdeal_iff,
    Set.forall_mem_image]
  rfl

end C13_V1

open DiazModulus C13_V1 in
theorem solution {K A₀ A₁ : Type*} [Field K] [IsAlgClosed K] [Fintype A₀] [Fintype A₁]
    (𝔟 : Ideal (MvPolynomial (A₀ ⊕ (A₁ × Bool)) K)) (h𝔟 : torusIdeal K A₀ A₁ ≤ 𝔟) :
    torusVanishing (torusZero 𝔟) = 𝔟.radical ∧ (torusZero 𝔟 = ∅ → 𝔟 = ⊤) := by
  have hV : torusVanishing (torusZero 𝔟) = 𝔟.radical := by
    rw [torusVanishing_eq_vanishingIdeal, ← zeroLocus_eq_image 𝔟 h𝔟,
      MvPolynomial.vanishingIdeal_zeroLocus_eq_radical]
  refine ⟨hV, fun h => ?_⟩
  rw [← Ideal.radical_eq_top, ← hV, h, torusVanishing_eq_vanishingIdeal, Set.image_empty,
    MvPolynomial.vanishingIdeal_empty]
