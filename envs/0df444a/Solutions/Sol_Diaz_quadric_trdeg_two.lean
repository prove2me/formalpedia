-- Prove2me | solution 1 for Diaz.quadric_trdeg_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T09:30:09.580976+00:00
-- url     : https://prove2.me/submissions/f3bad266-34dc-4d66-b8aa-58465ae58863

import Mathlib

open ComplexConjugate

theorem solution {K : Subfield ℂ}
    (hIU : ∀ (n : ℕ) (l : Fin n → ℂ) (P : MvPolynomial (Fin n) ℚ),
      (∀ i, Complex.exp (l i) ∈ K) →
      (∀ c : Fin n → ℚ, (∑ i, (c i : ℂ) * l i = 0) → c = 0) →
      P ≠ 0 → (∃ d, d ≤ 2 ∧ P.IsHomogeneous d) →
      MvPolynomial.aeval l P = 0 →
      2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ (Set.range l)))
    {u v : ℂ} {m : ℚ}
    (hu : Complex.exp u ∈ K) (huc : Complex.exp (conj u) ∈ K)
    (hv : Complex.exp v ∈ K) (hvc : Complex.exp (conj v) ∈ K)
    (hm : m ≠ 0) (hquad : v * conj v = (m : ℂ) * (u * conj u))
    (hindep : ∀ a b c d : ℚ,
      (a : ℂ) * u + (b : ℂ) * conj u + (c : ℂ) * v + (d : ℂ) * conj v = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    2 ≤ Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, conj u, v, conj v} : Set ℂ)) := by
  classical
  set l : Fin 4 → ℂ := ![u, conj u, v, conj v] with hl
  set P : MvPolynomial (Fin 4) ℚ :=
    MvPolynomial.C m * MvPolynomial.X 0 * MvPolynomial.X 1
      - MvPolynomial.X 2 * MvPolynomial.X 3 with hP
  have hmem : ∀ i, Complex.exp (l i) ∈ K := by
    intro i
    fin_cases i
    · show Complex.exp u ∈ K; exact hu
    · show Complex.exp (conj u) ∈ K; exact huc
    · show Complex.exp v ∈ K; exact hv
    · show Complex.exp (conj v) ∈ K; exact hvc
  have hfree : ∀ c : Fin 4 → ℚ, (∑ i, (c i : ℂ) * l i = 0) → c = 0 := by
    intro c hc
    rw [Fin.sum_univ_four] at hc
    obtain ⟨h0, h1, h2, h3⟩ := hindep (c 0) (c 1) (c 2) (c 3) (by simpa [hl] using hc)
    funext i
    fin_cases i
    · show c 0 = 0; exact h0
    · show c 1 = 0; exact h1
    · show c 2 = 0; exact h2
    · show c 3 = 0; exact h3
  have hP0 : P ≠ 0 := by
    intro h
    apply hm
    have := congrArg (MvPolynomial.eval (![1, 1, 0, 0] : Fin 4 → ℚ)) h
    simpa [hP] using this
  have hPh : ∃ d, d ≤ 2 ∧ P.IsHomogeneous d := by
    refine ⟨2, le_refl _, ?_⟩
    rw [hP]
    have h1 : ((MvPolynomial.C m : MvPolynomial (Fin 4) ℚ)
        * MvPolynomial.X 0 * MvPolynomial.X 1).IsHomogeneous 2 := by
      have := ((MvPolynomial.isHomogeneous_C _ m).mul
        (MvPolynomial.isHomogeneous_X ℚ (0 : Fin 4))).mul
        (MvPolynomial.isHomogeneous_X ℚ (1 : Fin 4))
      simpa using this
    have h2 : ((MvPolynomial.X 2 : MvPolynomial (Fin 4) ℚ)
        * MvPolynomial.X 3).IsHomogeneous 2 := by
      have := (MvPolynomial.isHomogeneous_X ℚ (2 : Fin 4)).mul
        (MvPolynomial.isHomogeneous_X ℚ (3 : Fin 4))
      simpa using this
    exact h1.sub h2
  have hval : MvPolynomial.aeval l P = 0 := by
    rw [hP, hl]
    simp
    linear_combination -hquad
  have hrange : Set.range l = ({u, conj u, v, conj v} : Set ℂ) := by
    rw [hl]; ext x; simp; tauto
  have := hIU 4 l P hmem hfree hP0 hPh hval
  rwa [hrange] at this
