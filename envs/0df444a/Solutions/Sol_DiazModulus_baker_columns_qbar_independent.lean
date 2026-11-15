-- Prove2me | solution 1 for DiazModulus.baker_columns_qbar_independent
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T10:34:38.266653+00:00
-- url     : https://prove2.me/submissions/f3ccc016-7713-4e80-b9c3-aa374b3510a2

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms

open Complex ComplexConjugate

/-! # Baker's theorem in column form

Let `M` be an `m × ℓ` matrix with entries in `ℒ` whose columns are `ℚ`-free. Among the entries choose
`λ₁, …, λ_r` forming a `ℚ`-basis of the `ℚ`-span of all entries; each `λ_s` is an entry, hence lies in `ℒ`,
and `M_{ij} = Σ_s a_{ijs} λ_s` with `a_{ijs} ∈ ℚ`. Suppose `Σ_i α_i e_i + Σ_j β_j M_{·j} = 0` with
`α, β` algebraic. Row `i` reads `α_i + Σ_s (Σ_j β_j a_{ijs}) λ_s = 0`, a linear form in the `ℚ`-free
logarithms `λ_s` with algebraic coefficients, so Baker's theorem gives `α_i = 0` and
`Σ_j β_j a_{ijs} = 0` for all `i, s`. The rational arrays `A_j = (a_{ijs})_{i,s}` are `ℚ`-free, because a
rational relation among them is a rational relation among the columns of `M`. Rationally independent
vectors of `ℚ^N` stay independent over `Q̄`, so `β = 0`, and the `m + ℓ` columns of `(I_m, M)` are
`Q̄`-free. -/

namespace RC2_BC
open DiazModulus

/-- The entries of `M` are `ℚ`-combinations of a `ℚ`-free family of entries. -/
theorem exists_entry_basis {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ) (hM : ∀ i j, M i j ∈ LogAlg) :
    ∃ (r : ℕ) (lam : Fin r → ℂ) (a : Fin m → Fin ℓ → Fin r → ℚ),
      LinearIndependent ℚ lam ∧ (∀ s, IsAlgebraic ℚ (Complex.exp (lam s))) ∧
      ∀ i j, M i j = ∑ s, (a i j s : ℂ) * lam s := by
  classical
  let E : Set ℂ := Set.range (fun p : Fin m × Fin ℓ => M p.1 p.2)
  obtain ⟨B, hBE, hBspan, hBind⟩ := exists_linearIndependent ℚ E
  have hBfin : B.Finite := (Set.finite_range _).subset hBE
  let F := hBfin.toFinset
  let e : Fin F.card ≃ B :=
    F.equivFin.symm.trans (Equiv.subtypeEquivRight (fun x => hBfin.mem_toFinset))
  let lam : Fin F.card → ℂ := fun s => ((e s : B) : ℂ)
  have hlamL : ∀ s, IsAlgebraic ℚ (Complex.exp (lam s)) := by
    intro s
    obtain ⟨p, hp⟩ := hBE (e s).2
    have := hM p.1 p.2
    simp only [lam, ← hp]
    exact this
  have hrange : Set.range lam = B := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩; exact (e s).2
    · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp [lam]⟩
  have hmem : ∀ i j, M i j ∈ Submodule.span ℚ (Set.range lam) := by
    intro i j
    rw [hrange, hBspan]
    exact Submodule.subset_span ⟨(i, j), rfl⟩
  choose a ha using fun i j => (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hmem i j)
  refine ⟨F.card, lam, a, hBind.comp e e.injective, hlamL, fun i j => ?_⟩
  rw [← ha i j]
  exact Finset.sum_congr rfl fun s _ => by rw [Rat.smul_def]

end RC2_BC

open DiazModulus RC2_BC in
theorem solution {m ℓ : ℕ} (M : Matrix (Fin m) (Fin ℓ) ℂ)
    (hM : ∀ i j, M i j ∈ LogAlg) (hcol : LinearIndependent ℚ M.col) :
    LinearIndependent (↥Qbar) (Matrix.fromCols (1 : Matrix (Fin m) (Fin m) ℂ) M).col := by
  classical
  obtain ⟨r, lam, a, hlamind, hlamL, ha'⟩ := exists_entry_basis M hM
  rw [Fintype.linearIndependent_iff]
  intro g hg
  -- row `i` of the relation, then Baker's theorem
  have hrow : ∀ i, (g (Sum.inl i) : ℂ) + ∑ j, (g (Sum.inr j) : ℂ) * M i j = 0 := by
    intro i
    have := congrFun hg i
    simp [Fintype.sum_sum_type, Matrix.col_apply, Matrix.one_apply, Subfield.smul_def] at this
    linear_combination this
  have hBK : ∀ i, (g (Sum.inl i) : ℂ) = 0 ∧
      ∀ s, ∑ j, (g (Sum.inr j) : ℂ) * (a i j s : ℂ) = 0 := by
    intro i
    by_contra hne
    have hnz : (g (Sum.inl i) : ℂ) ≠ 0 ∨ ∃ s, ∑ j, (g (Sum.inr j) : ℂ) * (a i j s : ℂ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hne h
    have halg : ∀ s, IsAlgebraic ℚ (∑ j, (g (Sum.inr j) : ℂ) * (a i j s : ℂ)) := by
      intro s
      apply mem_Qbar_iff.mp
      exact Qbar.sum_mem fun j _ => Qbar.mul_mem (g (Sum.inr j)).2 (SubfieldClass.ratCast_mem Qbar _)
    apply Schanuel.baker_linear_forms_in_logarithms r lam hlamind hlamL (g (Sum.inl i)) _
      (mem_Qbar_iff.mp (g (Sum.inl i)).2) halg hnz
    rw [← hrow i]
    congr 1
    simp_rw [ha' i, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring
  -- the rational arrays `A_j` are `ℚ`-free
  let A : Fin ℓ → Fin m × Fin r → ℚ := fun j p => a p.1 j p.2
  have hA : LinearIndependent ℚ A := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    apply (Fintype.linearIndependent_iff.mp hcol) c
    funext i
    have hci : ∀ s, ∑ j, c j * a i j s = 0 := by
      intro s
      have := congrFun hc (i, s)
      simpa [A] using this
    simp only [Finset.sum_apply, Pi.smul_apply, Matrix.col_apply, Pi.zero_apply, Rat.smul_def]
    simp_rw [ha' i, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    have := congrArg (fun q : ℚ => (q : ℂ) * lam s) (hci s)
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul, Rat.cast_zero, zero_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => by ring
  -- base change `ℚ → Q̄`
  have hAQ : LinearIndependent (↥Qbar) (fun j => algebraMap ℚ (↥Qbar) ∘ A j) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ↥Qbar)).mpr hA
  have hβ : ∀ j, g (Sum.inr j) = 0 := by
    apply (Fintype.linearIndependent_iff.mp hAQ) (fun j => g (Sum.inr j))
    funext p
    apply Subtype.ext
    have h := (hBK p.1).2 p.2
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply,
      ZeroMemClass.coe_zero]
    rw [← h]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [A]
  intro x
  rcases x with i | j
  · exact_mod_cast (hBK i).1
  · exact hβ j
