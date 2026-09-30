-- Prove2me | solution 1 for FourExp.trdeg_one_presentation_column
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-30T08:36:24.316392+00:00
-- url     : https://prove2.me/submissions/a34676a8-f216-4fda-8634-27905c70e21a

import Mathlib
import Theorems.Thm_DiazModulus_hermite_lindemann_holds
import Theorems.Thm_Transcendence_exists_monic_integral_model_presentation

/-!
# The column data in transcendence degree one

As in `FourExp.trdeg_one_presentation`, with the column hypothesis in place of the four algebraic
exponentials. Put `ω = x₁ y₂`. It is non-zero, since `x₁` and `y₂` belong to linearly independent
pairs, and `e^ω` is algebraic; by Hermite–Lindemann `ω` is therefore transcendental. It lies in
`ℚ[six] = ℚ[x₁, x₂, y₁, y₂, e^{x₁y₁}, e^{x₂y₁}]`, whose transcendence degree is at most one, so
every element of that ring is algebraic over `ℚ(ω)`: an element transcendental over `ℚ[ω]` would
form with `ω` an algebraically independent pair. This covers `xᵢ`, `yⱼ` and the row `e^{xᵢy₁}`.
The column `e^{xᵢy₂}` is algebraic over `ℚ`, hence over `ℚ(ω)`. The eight numbers `xᵢ`, `yⱼ`,
`e^{xᵢyⱼ}` then have a common presentation `z · D(ω, ω₁) = E(ω, ω₁)` over one monic integral
model `Q(ω, ω₁) = 0`, by `Transcendence.exists_monic_integral_model_presentation`.
-/

namespace T2_trdeg_one_presentation_column

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

end T2_trdeg_one_presentation_column

open T2_trdeg_one_presentation_column in
theorem solution
    (x₁ x₂ y₁ y₂ : ℂ) (hx : LinearIndependent ℚ ![x₁, x₂]) (hy : LinearIndependent ℚ ![y₁, y₂])
    (hexp₂ : ∀ i : Fin 2, IsAlgebraic ℚ (Complex.exp (![x₁, x₂] i * y₂)))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁),
      Complex.exp (x₂ * y₁)} : Set ℂ)) ≤ 1) :
    ∃ ω ω₁ : ℂ, Transcendental ℚ ω ∧ ∃ Q : Polynomial (Polynomial ℤ),
        Q.Monic ∧ 0 < Q.natDegree ∧ Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ Q = 0 ∧
        (∀ A : Polynomial (Polynomial ℤ), A.natDegree < Q.natDegree → Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ A = 0 → A = 0) ∧
        ∃ (D : Polynomial (Polynomial ℤ)) (E G : Fin 2 → Polynomial (Polynomial ℤ)) (H : Fin 2 → Fin 2 → Polynomial (Polynomial ℤ)),
          Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D ≠ 0 ∧ (∀ i, ![x₁, x₂] i * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (E i)) ∧
          (∀ j, ![y₁, y₂] j * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (G j)) ∧
          (∀ i j, Complex.exp (![x₁, x₂] i * ![y₁, y₂] j) * Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ D = Polynomial.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℂ) ω) ω₁ (H i j)) := by
  -- `ω = x₁ y₂` is transcendental, by Hermite–Lindemann applied to the column
  have hx1 : x₁ ≠ 0 := by simpa using hx.ne_zero 0
  have hy2 : y₂ ≠ 0 := by simpa using hy.ne_zero 1
  have hω : Transcendental ℚ (x₁ * y₂) := fun ha =>
    DiazModulus.hermite_lindemann_holds (x₁ * y₂) (mul_ne_zero hx1 hy2) ha (by simpa using hexp₂ 0)
  -- `ω` and the six generators lie in `ℚ[six]`
  set six : Set ℂ := {x₁, x₂, y₁, y₂, Complex.exp (x₁ * y₁), Complex.exp (x₂ * y₁)} with hsix
  have hS : ∀ z ∈ six, z ∈ Algebra.adjoin ℚ six := fun z hz => Algebra.subset_adjoin hz
  have hωS : x₁ * y₂ ∈ Algebra.adjoin ℚ six :=
    mul_mem (hS _ (by simp [hsix])) (hS _ (by simp [hsix]))
  -- the eight numbers are algebraic over `ℚ(ω)`
  let f : Fin 2 ⊕ (Fin 2 ⊕ (Fin 2 × Fin 2)) → ℂ := Sum.elim (fun i => ![x₁, x₂] i)
    (Sum.elim (fun j => ![y₁, y₂] j) (fun p => Complex.exp (![x₁, x₂] p.1 * ![y₁, y₂] p.2)))
  have hf : ∀ o, IsAlgebraic (IntermediateField.adjoin ℚ ({x₁ * y₂} : Set ℂ)) (f o) := by
    rintro (i | j | ⟨p, q⟩)
    · exact isAlgebraic_of_trdeg_le_one _ htr hωS
        (hS (![x₁, x₂] i) (by fin_cases i <;> simp [hsix])) hω
    · exact isAlgebraic_of_trdeg_le_one _ htr hωS
        (hS (![y₁, y₂] j) (by fin_cases j <;> simp [hsix])) hω
    · fin_cases q
      · -- the row `e^{x_p y₁}` is one of the six generators
        exact isAlgebraic_of_trdeg_le_one _ htr hωS
          (hS (Complex.exp (![x₁, x₂] p * y₁)) (by fin_cases p <;> simp [hsix])) hω
      · -- the column `e^{x_p y₂}` is algebraic over `ℚ`
        exact IsAlgebraic.tower_top (L := IntermediateField.adjoin ℚ ({x₁ * y₂} : Set ℂ))
          (hexp₂ p)
  -- one integral model presents them all
  obtain ⟨ω₁, Q, hQm, hQd, hQroot, hQmin, D, E, hD, hE⟩ :=
    Transcendence.exists_monic_integral_model_presentation (x₁ * y₂) hω f hf
  exact ⟨x₁ * y₂, ω₁, hω, Q, hQm, hQd, hQroot, hQmin, D, fun i => E (.inl i),
    fun j => E (.inr (.inl j)), fun i j => E (.inr (.inr (i, j))), hD, fun i => hE (.inl i),
    fun j => hE (.inr (.inl j)), fun i j => hE (.inr (.inr (i, j)))⟩
