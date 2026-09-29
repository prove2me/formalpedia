-- Prove2me | solution 1 for DiazModulus.candidate_nongeneric_four_exp_barrier
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T20:38:21.566991+00:00
-- url     : https://prove2.me/submissions/371c34ee-cbea-4545-a35e-358aa180181d

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open Complex ComplexConjugate

namespace NongenericBarrier

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ DiazModulus.Qbar :=
  DiazModulus.mem_Qbar_iff.symm

noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

/-- `ℒ` is stable under conjugation. -/
theorem exp_conj_alg {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp (conj w)) := by
  rw [Complex.exp_conj]; exact alg_conj hw

/-- `ℒ` is stable under rational multiples. -/
theorem exp_rat_mul_alg (q : ℚ) {w : ℂ} (hw : IsAlgebraic ℚ (Complex.exp w)) :
    IsAlgebraic ℚ (Complex.exp ((q : ℂ) * w)) := by
  refine IsAlgebraic.of_pow (n := q.den) q.pos ?_
  have hden : ((q.den : ℕ) : ℂ) * (q : ℂ) = ((q.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  rw [← Complex.exp_nat_mul, ← mul_assoc, hden, Complex.exp_int_mul]
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg q.num
  · rw [hm, zpow_natCast]; exact hw.pow m
  · rw [hm, zpow_neg, zpow_natCast]; exact (hw.pow m).inv

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`. -/
theorem trdeg_le_one_of_adjoin_singleton
    {B : Subalgebra ℚ ℂ} {x : ℂ} (hxB : x ∈ B)
    (halg : ∀ y ∈ B, IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) y) :
    Algebra.trdeg ℚ ↥B ≤ 1 := by
  set x' : (↥B) := ⟨x, hxB⟩ with hx'
  have hmap : Subalgebra.map B.val (Algebra.adjoin ℚ ({x'} : Set ↥B))
      = Algebra.adjoin ℚ ({x} : Set ℂ) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp [hx']
  let e : ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ≃ₐ[ℚ] ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) :=
    (Subalgebra.equivMapOfInjective _ B.val Subtype.val_injective).trans
      (Subalgebra.equivOfEq _ _ hmap)
  have : Algebra.IsAlgebraic ↥(Algebra.adjoin ℚ ({x'} : Set ↥B)) ↥B := by
    constructor
    intro y
    refine IsAlgebraic.of_ringHom_of_comp_eq (f := (e : _ →+* _))
      (g := (B.val : ↥B →+* ℂ)) (halg y y.2) e.surjective Subtype.val_injective ?_
    ext c
    rfl
  simpa using Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ ({x'} : Set ↥B)

/-- The complex numbers algebraic over `ℚ[x]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (x : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {x z : ℂ} : z ∈ E x ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {x z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E x :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({x} : Set ℂ))).injective

theorem self_mem_E (x : ℂ) : x ∈ E x := by
  rw [mem_E_iff]
  have h : x = algebraMap ↥(Algebra.adjoin ℚ ({x} : Set ℂ)) ℂ
      ⟨x, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem mem_E_of_mul {x a z : ℂ} (ha0 : a ≠ 0) (ha : a ∈ E x) (h : a * z ∈ E x) :
    z ∈ E x := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ha0) (mem_E_iff.1 ha) h

end NongenericBarrier

open NongenericBarrier in
/-- Zero entries force a zero row or column (via `det M = 0`); otherwise four exponentials
(trdeg ≤ 1 form) applies to `M`, whose entries lie in `ℚu + ℚū + ℚπi`: their exponentials are
algebraic, and all entries are algebraic over `ℚ[πi]` because `u` is and `ū = ρ / u`. -/
theorem solution (u : ℂ) (hu : DiazModulus.IsCandidate u)
    (halg : IsAlgebraic (↥(Algebra.adjoin ℚ ({((Real.pi : ℝ) : ℂ) * Complex.I} : Set ℂ))) u)
    (A : Fin 2 → Fin 2 → Fin 3 → ℚ) (M : Fin 2 → Fin 2 → ℂ)
    (hM : ∀ i j, M i j = ∑ k, (A i j k : ℂ) * ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] k)
    (hdet : M 0 0 * M 1 1 = M 0 1 * M 1 0) :
    (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ j, (p : ℂ) * M 0 j + (q : ℂ) * M 1 j = 0) ∨
      (∃ p q : ℚ, ¬(p = 0 ∧ q = 0) ∧ ∀ i, (p : ℂ) * M i 0 + (q : ℂ) * M i 1 = 0) := by
  -- a zero entry gives a zero row or a zero column
  by_cases h00 : M 0 0 = 0
  · have h : M 0 1 * M 1 0 = 0 := by rw [← hdet, h00, zero_mul]
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl ⟨1, 0, by norm_num, by rw [Fin.forall_fin_two]; simp [h00, h]⟩
    · exact Or.inr ⟨1, 0, by norm_num, by rw [Fin.forall_fin_two]; simp [h00, h]⟩
  by_cases h01 : M 0 1 = 0
  · have h : M 0 0 * M 1 1 = 0 := by rw [hdet, h01, zero_mul]
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h00
    · exact Or.inr ⟨0, 1, by norm_num, by rw [Fin.forall_fin_two]; simp [h01, h]⟩
  by_cases h10 : M 1 0 = 0
  · have h : M 0 0 * M 1 1 = 0 := by rw [hdet, h10, mul_zero]
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h00
    · exact Or.inl ⟨0, 1, by norm_num, by rw [Fin.forall_fin_two]; simp [h10, h]⟩
  by_cases h11 : M 1 1 = 0
  · have h : M 0 1 * M 1 0 = 0 := by rw [← hdet, h11, mul_zero]
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h01
    · exact absurd h h10
  -- every entry is non-zero: four exponentials
  obtain ⟨hu0, hnorm, hexp⟩ := hu
  set x : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I with hx_def
  have hρ : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hρalg : IsAlgebraic ℚ (u * conj u) := by rw [hρ]; exact hnorm.pow 2
  have hexpx : IsAlgebraic ℚ (Complex.exp x) := by
    rw [hx_def, Complex.exp_pi_mul_I]
    exact (isAlgebraic_one (R := ℚ) (A := ℂ)).neg
  have hM' : ∀ i j,
      M i j = (A i j 0 : ℂ) * u + (A i j 1 : ℂ) * conj u + (A i j 2 : ℂ) * x := by
    intro i j
    rw [hM i j, Fin.sum_univ_three]
    rfl
  -- the four exponentials are algebraic
  have hexpM : ∀ i j, IsAlgebraic ℚ (Complex.exp (M i j)) := by
    intro i j
    rw [hM' i j, Complex.exp_add, Complex.exp_add, alg_iff_mem]
    refine Subfield.mul_mem _ (Subfield.mul_mem _ ?_ ?_) ?_
    · exact alg_iff_mem.1 (exp_rat_mul_alg _ hexp)
    · exact alg_iff_mem.1 (exp_rat_mul_alg _ (exp_conj_alg hexp))
    · exact alg_iff_mem.1 (exp_rat_mul_alg _ hexpx)
  -- transcendence degree at most one: `u`, `ū`, `πi` are algebraic over `ℚ[πi]`
  have huE : u ∈ E x := mem_E_iff.2 halg
  have hxE : x ∈ E x := self_mem_E x
  have hcuE : conj u ∈ E x := mem_E_of_mul hu0 huE (mem_E_of_alg hρalg)
  have htrB : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, conj u, x} : Set ℂ)) ≤ 1 := by
    refine trdeg_le_one_of_adjoin_singleton (x := x) (Algebra.subset_adjoin (by simp)) ?_
    have hle : Algebra.adjoin ℚ ({u, conj u, x} : Set ℂ) ≤ E x := by
      refine Algebra.adjoin_le ?_
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h <;> rw [h, SetLike.mem_coe]
      exacts [huE, hcuE, hxE]
    intro y hy
    exact mem_E_iff.1 (hle hy)
  have hsub : Algebra.adjoin ℚ ({M 0 0, M 0 1, M 1 0, M 1 1} : Set ℂ) ≤
      Algebra.adjoin ℚ ({u, conj u, x} : Set ℂ) := by
    have hmem : ∀ i j, M i j ∈ Algebra.adjoin ℚ ({u, conj u, x} : Set ℂ) := by
      intro i j
      rw [hM' i j]
      refine add_mem (add_mem ?_ ?_) ?_
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (A i j 0))
          (Algebra.subset_adjoin (by simp))
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (A i j 1))
          (Algebra.subset_adjoin (by simp))
      · exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ (A i j 2))
          (Algebra.subset_adjoin (by simp))
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl | rfl | rfl) <;> exact hmem _ _
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({M 0 0, M 0 1, M 1 0, M 1 1} : Set ℂ)) ≤ 1 :=
    (trdeg_le_of_injective (Subalgebra.inclusion hsub)
      (Subalgebra.inclusion_injective hsub)).trans htrB
  -- `l₁₁ = M 0 0`, `l₁₂ = M 0 1`, `l₂₁ = M 1 0`, `l₂₂ = M 1 1`
  rcases DiazModulus.four_exponentials_trdeg_one (M 0 0) (M 0 1) (M 1 0) (M 1 1)
      (hexpM 0 0) (hexpM 0 1) (hexpM 1 0) (hexpM 1 1) h00 h01 h10 h11 hdet htr with
    ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
  · -- rows: `a·(row 0) + b·(row 1) = 0`
    exact Or.inl ⟨a, b, hab, by rw [Fin.forall_fin_two]; exact ⟨h1, h2⟩⟩
  · -- columns: `a·(column 0) + b·(column 1) = 0`
    exact Or.inr ⟨a, b, hab, by rw [Fin.forall_fin_two]; exact ⟨h1, h2⟩⟩

#print axioms solution
