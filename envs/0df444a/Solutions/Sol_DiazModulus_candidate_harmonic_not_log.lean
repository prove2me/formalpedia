-- Prove2me | solution 1 for DiazModulus.candidate_harmonic_not_log
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-23T18:25:01.827199+00:00
-- url     : https://prove2.me/submissions/3da66a91-fa4d-4655-a54d-cb1e2b6eba77

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one
import Theorems.Thm_DiazModulus_hermite_lindemann_holds

open Complex ComplexConjugate

namespace HarmonicNotLog

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ DiazModulus.Qbar :=
  DiazModulus.mem_Qbar_iff.symm

theorem isAlg_rat (r : ℚ) : IsAlgebraic ℚ (r : ℂ) :=
  isAlgebraic_algebraMap r

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

/-- The complex numbers algebraic over `ℚ[u]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def E (u : ℂ) : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) ℂ).restrictScalars ℚ

theorem mem_E_iff {u z : ℂ} : z ∈ E u ↔ IsAlgebraic ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) z :=
  Iff.rfl

theorem mem_E_of_alg {u z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ E u :=
  h.extendScalars (algebraMap ℚ ↥(Algebra.adjoin ℚ ({u} : Set ℂ))).injective

theorem self_mem_E (u : ℂ) : u ∈ E u := by
  rw [mem_E_iff]
  have h : u = algebraMap ↥(Algebra.adjoin ℚ ({u} : Set ℂ)) ℂ
      ⟨u, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

theorem mem_E_of_mul {u a z : ℂ} (ha0 : a ≠ 0) (ha : a ∈ E u) (h : a * z ∈ E u) :
    z ∈ E u := by
  rw [mem_E_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero ha0) (mem_E_iff.1 ha) h

/-- A candidate lies on neither axis, so `u` and `ū` are `ℚ`-independent: from
`α u + β ū = 0`, multiplying by `u` gives `α u² = -β ρ`, and `α ≠ 0` would make `u` algebraic,
against Hermite–Lindemann. -/
theorem indep {u : ℂ} (hu : DiazModulus.IsCandidate u) (α β : ℚ)
    (h : (α : ℂ) * u + (β : ℂ) * conj u = 0) : α = 0 ∧ β = 0 := by
  obtain ⟨hu0, hnorm, hexp⟩ := hu
  have hρ : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hρalg : IsAlgebraic ℚ (u * conj u) := by rw [hρ]; exact hnorm.pow 2
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hα : α = 0 := by
    by_contra hα
    have hαC : (α : ℂ) ≠ 0 := by exact_mod_cast hα
    have key : (α : ℂ) * u ^ 2 = -(β : ℂ) * (u * conj u) := by
      linear_combination u * h
    have hsq : u ^ 2 = ((-β / α : ℚ) : ℂ) * (u * conj u) := by
      rw [Rat.cast_div, Rat.cast_neg, div_mul_eq_mul_div, eq_div_iff hαC]
      linear_combination key
    have halg : IsAlgebraic ℚ (u ^ 2) := by
      rw [hsq, alg_iff_mem]
      exact Subfield.mul_mem _ (alg_iff_mem.1 (isAlg_rat _)) (alg_iff_mem.1 hρalg)
    exact DiazModulus.hermite_lindemann_holds u hu0 (halg.of_pow (by norm_num)) hexp
  subst hα
  refine ⟨rfl, ?_⟩
  simp only [Rat.cast_zero, zero_mul, zero_add, mul_eq_zero] at h
  rcases h with h | h
  · exact_mod_cast h
  · exact absurd h hcu

end HarmonicNotLog

open HarmonicNotLog in
/-- Four exponentials (trdeg ≤ 1 form) on the matrix `[[u, m], [l, ū]]`, where
`l = p u + q ū` and `m = ρ / l`, `ρ = u ū`; its determinant is `ρ - m l = 0`. -/
theorem solution (u : ℂ) (hu : DiazModulus.IsCandidate u) (p q : ℚ) (hp : p ≠ 0)
    (hq : q ≠ 0) :
    Transcendental ℚ (Complex.exp (u * conj u / ((p : ℂ) * u + (q : ℂ) * conj u))) := by
  have hind := indep hu
  obtain ⟨hu0, hnorm, hexp⟩ := hu
  intro hmalg
  have hρ : u * conj u = ((‖u‖ : ℝ) : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hρalg : IsAlgebraic ℚ (u * conj u) := by rw [hρ]; exact hnorm.pow 2
  have hcu : conj u ≠ 0 := (map_ne_zero _).2 hu0
  have hρ0 : u * conj u ≠ 0 := mul_ne_zero hu0 hcu
  obtain ⟨l, hl_def⟩ : ∃ l : ℂ, l = (p : ℂ) * u + (q : ℂ) * conj u := ⟨_, rfl⟩
  rw [← hl_def] at hmalg
  have hl0 : l ≠ 0 := by
    intro h0
    rw [h0] at hl_def
    exact hp (hind p q hl_def.symm).1
  obtain ⟨m, hm_def⟩ : ∃ m : ℂ, m = u * conj u / l := ⟨_, rfl⟩
  rw [← hm_def] at hmalg
  have hm0 : m ≠ 0 := by rw [hm_def]; exact div_ne_zero hρ0 hl0
  have hml : m * l = u * conj u := by rw [hm_def]; field_simp
  -- the four exponentials are algebraic
  have hel : IsAlgebraic ℚ (Complex.exp l) := by
    rw [hl_def, Complex.exp_add, alg_iff_mem]
    exact Subfield.mul_mem _ (alg_iff_mem.1 (exp_rat_mul_alg p hexp))
      (alg_iff_mem.1 (exp_rat_mul_alg q (exp_conj_alg hexp)))
  have hecu : IsAlgebraic ℚ (Complex.exp (conj u)) := exp_conj_alg hexp
  -- transcendence degree at most one: everything is algebraic over `ℚ[u]`
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({u, m, l, conj u} : Set ℂ)) ≤ 1 := by
    have hxB : u ∈ Algebra.adjoin ℚ ({u, m, l, conj u} : Set ℂ) :=
      Algebra.subset_adjoin (by simp)
    refine trdeg_le_one_of_adjoin_singleton hxB ?_
    have huE : u ∈ E u := self_mem_E u
    have hcuE : conj u ∈ E u := mem_E_of_mul hu0 huE (mem_E_of_alg hρalg)
    have hlE : l ∈ E u := by
      rw [hl_def]
      exact add_mem (mul_mem (mem_E_of_alg (isAlg_rat p)) huE)
        (mul_mem (mem_E_of_alg (isAlg_rat q)) hcuE)
    have hmE : m ∈ E u :=
      mem_E_of_mul hl0 hlE (by rw [mul_comm, hml]; exact mem_E_of_alg hρalg)
    have hle : Algebra.adjoin ℚ ({u, m, l, conj u} : Set ℂ) ≤ E u := by
      refine Algebra.adjoin_le ?_
      rintro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with h | h | h | h <;> rw [h, SetLike.mem_coe]
      exacts [huE, hmE, hlE, hcuE]
    intro y hy
    exact mem_E_iff.1 (hle hy)
  -- `l₁₁ = u`, `l₁₂ = m`, `l₂₁ = l`, `l₂₂ = ū`
  rcases DiazModulus.four_exponentials_trdeg_one u m l (conj u) hexp hmalg hel hecu
      hu0 hm0 hl0 hcu hml.symm htr with
    ⟨a, b, hab, h1, -⟩ | ⟨a, b, hab, -, h2⟩
  · -- rows: `a u + b l = 0`, i.e. `(a + b p) u + b q ū = 0`
    have hr := hind (a + b * p) (b * q) (by push_cast; linear_combination h1 - (b : ℂ) * hl_def)
    have hb : b = 0 := by
      rcases mul_eq_zero.1 hr.2 with hb | hb
      · exact hb
      · exact absurd hb hq
    have ha : a = 0 := by
      have := hr.1
      rw [hb, zero_mul, add_zero] at this
      exact this
    exact hab ⟨ha, hb⟩
  · -- columns: `a l + b ū = 0`, i.e. `a p u + (a q + b) ū = 0`
    have hr := hind (a * p) (a * q + b) (by push_cast; linear_combination h2 - (a : ℂ) * hl_def)
    have ha : a = 0 := by
      rcases mul_eq_zero.1 hr.1 with ha | ha
      · exact ha
      · exact absurd ha hp
    have hb : b = 0 := by
      have := hr.2
      rw [ha, zero_mul, zero_add] at this
      exact this
    exact hab ⟨ha, hb⟩

#print axioms solution
