-- Prove2me | solution 2 for FourExp.trdeg_one_presentation
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-27T07:59:28.239735+00:00
-- url     : https://prove2.me/submissions/9541d31c-d280-470e-83a5-281a3daf0f03

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_exists_monic_integral_model_presentation

/-!
# The four exponentials data in transcendence degree one

Put `ω = x₁ y₁`. It is non-zero, since `x₁` and `y₁` belong to linearly independent pairs, and
`e^ω` is algebraic; by Hermite–Lindemann `ω` is therefore transcendental. It lies in
`ℚ[x₁, x₂, y₁, y₂]`, whose transcendence degree is at most one, so every element of that ring is
algebraic over `ℚ(ω)`: an element transcendental over `ℚ[ω]` would form with `ω` an algebraically
independent pair. The four exponentials `e^(xᵢ yⱼ)` are algebraic over `ℚ`, hence over `ℚ(ω)`.
The eight numbers `xᵢ`, `yⱼ`, `e^(xᵢ yⱼ)` then have a common presentation
`z · D(ω, ω₁) = E(ω, ω₁)` over one monic integral model `Q(ω, ω₁) = 0`.
-/

namespace TrdegOnePresentation

/-- In `ℚ[S] ⊆ ℂ` of transcendence degree at most one, every element is algebraic over `ℚ(ω)`,
for any transcendental `ω ∈ ℚ[S]`. -/
lemma isAlgebraic_of_trdeg_le_one (S : Set ℂ) (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ S) ≤ 1)
    {ω z : ℂ} (hωS : ω ∈ Algebra.adjoin ℚ S) (hzS : z ∈ Algebra.adjoin ℚ S)
    (hω : Transcendental ℚ ω) :
    IsAlgebraic (IntermediateField.adjoin ℚ ({ω} : Set ℂ)) z := by
  rw [IntermediateField.isAlgebraic_adjoin_iff]
  by_contra hz
  have hind : AlgebraicIndependent ℚ (fun _ : Unit => ω) :=
    (algebraicIndependent_singleton_iff ()).2 hω
  have htrans : Transcendental (Algebra.adjoin ℚ (Set.range fun _ : Unit => ω)) z := by
    rw [Set.range_const]
    exact hz
  have hopt := (hind.option_iff_transcendental z).2 htrans
  let v : Option Unit → Algebra.adjoin ℚ S := fun o => o.elim ⟨z, hzS⟩ (fun _ => ⟨ω, hωS⟩)
  have hv : AlgebraicIndependent ℚ v := by
    refine AlgebraicIndependent.of_comp (Algebra.adjoin ℚ S).val ?_
    convert hopt using 1
    funext o
    cases o <;> rfl
  have hcard := hv.cardinalMk_le_trdeg
  rw [show Cardinal.mk (Option Unit) = 2 by simp] at hcard
  have := hcard.trans htr
  norm_num at this

end TrdegOnePresentation

open TrdegOnePresentation in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp : ∀ i j : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * ![y₁, y₂] j)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ)) ≤ 1) :
    ∃ ω ω₁ : ℂ, Transcendental ℚ ω ∧ ∃ Q : Polynomial (Polynomial ℤ),
        Q.Monic ∧ 0 < Q.natDegree ∧ Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
        (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
        ∃ (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ)),
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧ (∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i)) ∧
          (∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) ∧
          (∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) := by
  -- `ω = x₁ y₁` is transcendental, by Hermite–Lindemann
  have hx1 : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hy1 : y₁ ≠ 0 := by simpa using hy.ne_zero 0
  have hω : Transcendental ℚ (x₁ * y₁) := fun ha =>
    DiazModulus.hermite_lindemann_holds (x₁ * y₁) (mul_ne_zero hx1 hy1) ha (by simpa using hexp 0 0)
  -- the eight numbers are algebraic over `ℚ(ω)`
  have hS : ∀ z ∈ ({x₁, x₂, y₁, y₂} : Set ℂ), z ∈ Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ) :=
    fun z hz => Algebra.subset_adjoin hz
  have hωS : x₁ * y₁ ∈ Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂} : Set ℂ) :=
    mul_mem (hS _ (by simp)) (hS _ (by simp))
  let f : Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 × Fin 2)) → ℂ := Sum.elim (fun i => ![x₁, x₂] i)
    (Sum.elim (fun j => ![y₁, y₂] j) (fun p => Complex.exp (![x₁, x₂] p.1 * ![y₁, y₂] p.2)))
  have hf : ∀ o, IsAlgebraic (IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ)) (f o) := by
    rintro (i | j | p)
    · exact isAlgebraic_of_trdeg_le_one _ htr hωS (hS (![x₁, x₂] i) (by fin_cases i <;> simp)) hω
    · exact isAlgebraic_of_trdeg_le_one _ htr hωS (hS (![y₁, y₂] j) (by fin_cases j <;> simp)) hω
    · exact IsAlgebraic.tower_top (L := IntermediateField.adjoin ℚ ({x₁ * y₁} : Set ℂ)) (hexp p.1 p.2)
  -- one integral model presents them all
  obtain ⟨ω₁, Q, hQm, hQd, hQroot, hQmin, D, E, hD, hE⟩ :=
    Transcendence.exists_monic_integral_model_presentation (x₁ * y₁) hω f hf
  exact ⟨x₁ * y₁, ω₁, hω, Q, hQm, hQd, hQroot, hQmin, D, fun i => E (.inl i),
    fun j => E (.inr (.inl j)), fun i j => E (.inr (.inr (i, j))), hD, fun i => hE (.inl i),
    fun j => hE (.inr (.inl j)), fun i j => hE (.inr (.inr (i, j)))⟩

#print axioms solution
