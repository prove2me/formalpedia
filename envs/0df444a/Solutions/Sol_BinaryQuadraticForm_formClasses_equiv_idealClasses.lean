-- Prove2me | solution 1 for BinaryQuadraticForm.formClasses_equiv_idealClasses
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-24T22:47:00.645154+00:00
-- url     : https://prove2.me/submissions/325ded7d-d12a-4fc8-959e-6b6247359b62

import Mathlib
import Definitions.Def_RPLib_S3_DWSTateQ6

set_option autoImplicit false

theorem solution (a b : ℤ) (hD : b ^ 2 + 4 * a < 0)
    (I : ℤ → ℤ → Ideal (QuadraticAlgebra ℤ a b))
    (hI : ∀ A B : ℤ, I A B = Ideal.span {(A : QuadraticAlgebra ℤ a b), ⟨-((b + B) / 2), 1⟩}) :
    (∀ A B C : ℤ, B ^ 2 - 4 * A * C = b ^ 2 + 4 * a → 0 < A → Int.gcd A (Int.gcd B C) = 1 →
      ∃ J : Ideal (QuadraticAlgebra ℤ a b), ∃ ν : QuadraticAlgebra ℤ a b,
        ν ≠ 0 ∧ I A B * J = Ideal.span {ν}) ∧
    (∀ A B C A' B' C' : ℤ,
      B ^ 2 - 4 * A * C = b ^ 2 + 4 * a → 0 < A → Int.gcd A (Int.gcd B C) = 1 →
      B' ^ 2 - 4 * A' * C' = b ^ 2 + 4 * a → 0 < A' → Int.gcd A' (Int.gcd B' C') = 1 →
      ((∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, ∀ x y : ℤ,
          A' * x ^ 2 + B' * x * y + C' * y ^ 2 =
            A * (γ 0 0 * x + γ 0 1 * y) ^ 2 +
              B * (γ 0 0 * x + γ 0 1 * y) * (γ 1 0 * x + γ 1 1 * y) +
              C * (γ 1 0 * x + γ 1 1 * y) ^ 2) ↔
        ∃ α β : QuadraticAlgebra ℤ a b, α ≠ 0 ∧ β ≠ 0 ∧
          Ideal.span {α} * I A B = Ideal.span {β} * I A' B')) ∧
    (∀ J : Ideal (QuadraticAlgebra ℤ a b),
      (∃ K : Ideal (QuadraticAlgebra ℤ a b), ∃ ν : QuadraticAlgebra ℤ a b,
        ν ≠ 0 ∧ J * K = Ideal.span {ν}) →
      ∃ A B C : ℤ, B ^ 2 - 4 * A * C = b ^ 2 + 4 * a ∧ 0 < A ∧ Int.gcd A (Int.gcd B C) = 1 ∧
        ∃ α β : QuadraticAlgebra ℤ a b, α ≠ 0 ∧ β ≠ 0 ∧
          Ideal.span {α} * J = Ideal.span {β} * I A B) := by
  have hIf : ∀ A B C : ℤ, I A B = RPLib.DWS.QA.formIdeal (⟨A, B, C⟩ : RamanujanPetersson.Hurwitz.BQF) :=
    fun A B C => by rw [hI]; rfl
  have hmem : ∀ A B C : ℤ, B ^ 2 - 4 * A * C = b ^ 2 + 4 * a → 0 < A → Int.gcd A (Int.gcd B C) = 1 →
      (⟨A, B, C⟩ : RamanujanPetersson.Hurwitz.BQF) ∈ RamanujanPetersson.Hurwitz.primForms (b ^ 2 + 4 * a) :=
    fun A B C h1 h2 h3 => ⟨h1, ⟨h2, h1.trans_lt hD⟩, h3⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A B C h1 h2 h3
    rw [hIf A B C]
    exact RPLib.DWS.QA.formIdeal_inv (hmem A B C h1 h2 h3)
  · intro A B C A' B' C' h1 h2 h3 h1' h2' h3'
    rw [hIf A B C, hIf A' B' C']
    have key := RPLib.DWS.QA.idealRel_iff hD (hmem A B C h1 h2 h3) (hmem A' B' C' h1' h2' h3')
    refine Iff.trans ?_ key.symm
    refine exists_congr (fun γ => ?_)
    constructor
    · intro h
      have e10 := h 1 0
      have e01 := h 0 1
      have e11 := h 1 1
      simp only [RamanujanPetersson.Hurwitz.act, RamanujanPetersson.Hurwitz.BQF.subst,
        RamanujanPetersson.Hurwitz.BQF.mk.injEq]
      refine ⟨by linear_combination -e10, ?_, by linear_combination -e01⟩
      linear_combination e10 + e01 - e11
    · intro h x y
      have ha := congrArg RamanujanPetersson.Hurwitz.BQF.a h
      have hb := congrArg RamanujanPetersson.Hurwitz.BQF.b h
      have hc := congrArg RamanujanPetersson.Hurwitz.BQF.c h
      simp only [RamanujanPetersson.Hurwitz.act, RamanujanPetersson.Hurwitz.BQF.subst] at ha hb hc
      linear_combination (-x ^ 2) * ha - x * y * hb - y ^ 2 * hc
  · rintro J ⟨K, ν, hν, hJK⟩
    obtain ⟨f, hf, hrel⟩ := RPLib.DWS.QA.exists_formIdeal_rel hD hν hJK
    refine ⟨f.a, f.b, f.c, hf.1, hf.2.1.1, hf.2.2, ?_⟩
    rw [hIf f.a f.b f.c]
    exact hrel
