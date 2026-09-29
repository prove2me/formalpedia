-- Prove2me | solution 1 for DiazModulus.diaz_of_exp_not_real_irrational_angle_period_aligned_norm_rat_mult
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T15:06:35.062163+00:00
-- url     : https://prove2.me/submissions/e9a7f7d5-d00b-4272-9fac-b9da64be5dce

import Theorems.Thm_DiazModulus_four_exponentials_trdeg_one

open Complex ComplexConjugate

/-!
# The period-aligned `norm_rat_mult` half, from four exponentials in transcendence degree one.

The matrix is `[[u, ν], [c·2πi, conj u]]` with `ν = i(Im u + rπ)` and `c = -A/(2β)`, where
`A = ‖u‖²` and `β = π(Im u + rπ)`.  Its determinant is `A + 2cβ = 0`; its rows and columns
are `ℚ`-independent because `Re u ≠ 0` and `Im u ∉ πℚ`.  The four entries generate a
`ℚ`-algebra of transcendence degree at most one, because each is algebraic over `ℚ[πi]`:
the relation `t²π² + r²π⁴ − (A + 2rβ)π² + β² = 0` makes `Re u` algebraic over `ℚ[πi]`, and
`ν·πi = −β` makes `ν` so.  So `DiazModulus.four_exponentials_trdeg_one` applies, and its
row/column dichotomy is contradicted.
-/

namespace DiazTrdegSol

open DiazModulus

/-! ## 0. Algebraicity bookkeeping over `ℚ`. -/

theorem alg_iff_mem {z : ℂ} : IsAlgebraic ℚ z ↔ z ∈ Qbar := mem_Qbar_iff.symm

/-- Complex conjugation as a `ℚ`-algebra map, used only to transport algebraicity. -/
noncomputable def cjQ : ℂ →ₐ[ℚ] ℂ :=
  (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ).toAlgHom.restrictScalars ℚ

theorem alg_conj {z : ℂ} (h : IsAlgebraic ℚ z) : IsAlgebraic ℚ (conj z) := by
  obtain ⟨p, hp0, hp⟩ := h
  refine ⟨p, hp0, ?_⟩
  have : Polynomial.aeval (cjQ z) p = cjQ (Polynomial.aeval z p) :=
    Polynomial.aeval_algHom_apply cjQ z p
  rw [show (conj z : ℂ) = cjQ z from rfl, this, hp, map_zero]

theorem alg_div {z w : ℂ} (hz : IsAlgebraic ℚ z) (hw : IsAlgebraic ℚ w) :
    IsAlgebraic ℚ (z / w) := by
  rw [alg_iff_mem] at *
  exact Subfield.div_mem _ hz hw

theorem alg_pow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℕ) : IsAlgebraic ℚ (z ^ n) := by
  rw [alg_iff_mem] at *
  exact Subfield.pow_mem _ hz n

/-- A rational multiple of `2πi` is a logarithm of a root of unity. -/
theorem alg_exp_rat_two_pi_I (c : ℚ) :
    IsAlgebraic ℚ (Complex.exp ((c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))) := by
  refine IsAlgebraic.of_pow (n := c.den) c.pos ?_
  have hden : ((c.den : ℕ) : ℂ) * (c : ℂ) = ((c.num : ℤ) : ℂ) := by
    rw [Rat.cast_def]; field_simp
  have hstep : ((c.den : ℕ) : ℂ) * ((c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I))
      = ((c.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
    rw [← mul_assoc, hden]
  rw [← Complex.exp_nat_mul, hstep, Complex.exp_int_mul_two_pi_mul_I]
  simpa using (isAlgebraic_one (R := ℚ) (A := ℂ))

/-! ## 1. `trdeg ≤ 1` from algebraicity over `ℚ[x]` for a single `x` in the algebra. -/

/-- If every element of a `ℚ`-subalgebra `B ⊆ ℂ` is algebraic over `ℚ[x]` for one `x ∈ B`,
then `B` has transcendence degree at most one over `ℚ`.

This is `Algebra.IsAlgebraic.trdeg_le_cardinalMk` with `s = {x}`, whose statement lives in
`↥B`; the work is transporting `Algebra.adjoin ℚ ({x} : Set ↥B)` to
`Algebra.adjoin ℚ ({x} : Set ℂ)`. -/
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

/-! ## 2. The base ring `ℚ[πi]` and the complex numbers algebraic over it. -/

/-- The transcendence generator: `π i`. -/
noncomputable def piI : ℂ := ((Real.pi : ℝ) : ℂ) * Complex.I

theorem piI_ne_zero : piI ≠ 0 := by
  refine mul_ne_zero ?_ Complex.I_ne_zero
  exact_mod_cast Real.pi_ne_zero

/-- The base ring `ℚ[πi] ⊆ ℂ`. -/
noncomputable def Kpi : Subalgebra ℚ ℂ := Algebra.adjoin ℚ ({piI} : Set ℂ)

/-- The complex numbers algebraic over `ℚ[πi]`, as a `ℚ`-subalgebra of `ℂ`. -/
noncomputable def Epi : Subalgebra ℚ ℂ :=
  (Subalgebra.algebraicClosure ↥Kpi ℂ).restrictScalars ℚ

theorem mem_Epi_iff {z : ℂ} : z ∈ Epi ↔ IsAlgebraic ↥Kpi z := Iff.rfl

/-- Everything algebraic over `ℚ` is algebraic over `ℚ[πi]`. -/
theorem mem_Epi_of_alg {z : ℂ} (h : IsAlgebraic ℚ z) : z ∈ Epi :=
  h.extendScalars (algebraMap ℚ ↥Kpi).injective

theorem piI_mem_Epi : piI ∈ Epi := by
  rw [mem_Epi_iff]
  have h : piI = algebraMap ↥Kpi ℂ ⟨piI, Algebra.subset_adjoin rfl⟩ := rfl
  rw [h]
  exact isAlgebraic_algebraMap _

/-- Division by `πi` stays inside `Epi`. -/
theorem mem_Epi_of_mul_piI {z : ℂ} (h : piI * z ∈ Epi) : z ∈ Epi := by
  rw [mem_Epi_iff] at h ⊢
  exact IsAlgebraic.of_mul (mem_nonZeroDivisors_of_ne_zero piI_ne_zero)
    (mem_Epi_iff.1 piI_mem_Epi) h

/-! ## 3. The four matrix entries are algebraic over `ℚ[πi]`. -/

theorem piI_sq : piI ^ 2 = -(((Real.pi : ℝ) : ℂ)) ^ 2 := by
  rw [piI, mul_pow, Complex.I_sq]; ring

theorem piI_pow_four : piI ^ 4 = (((Real.pi : ℝ) : ℂ)) ^ 4 := by
  have : piI ^ 4 = (piI ^ 2) ^ 2 := by ring
  rw [this, piI_sq]; ring

/-- The carrier `ν = i (Im u + rπ)` is algebraic over `ℚ[πi]`: `ν · πi = −β`. -/
theorem nu_mem_Epi (u : ℂ) (r : ℚ)
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    Complex.I * (((u.im + (r : ℝ) * Real.pi : ℝ)) : ℂ) ∈ Epi := by
  refine mem_Epi_of_mul_piI ?_
  have hkey : piI * (Complex.I * (((u.im + (r : ℝ) * Real.pi : ℝ)) : ℂ))
      = -(((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ)) : ℂ) := by
    rw [piI]
    push_cast
    linear_combination (((Real.pi : ℝ) : ℂ) * ((u.im : ℝ) : ℂ)
      + ((Real.pi : ℝ) : ℂ) * ((r : ℂ) * ((Real.pi : ℝ) : ℂ))) * Complex.I_sq
  rw [hkey]
  exact neg_mem (mem_Epi_of_alg hβ)

/-- The real part is algebraic over `ℚ[πi]`: the quartic relation
`t²π² + r²π⁴ − (A + 2rβ)π² + β² = 0` is a quadratic in `t` with leading coefficient
`π² ≠ 0`, hence non-trivial. -/
theorem re_mem_Epi (u : ℂ) (r : ℚ)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    (((u.re : ℝ)) : ℂ) ∈ Epi := by
  set A : ℂ := (((‖u‖ : ℝ)) : ℂ) ^ 2 with hA_def
  set β : ℂ := (((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ)) : ℂ) with hβ_def
  have hAE : A ∈ Epi := pow_mem (mem_Epi_of_alg hnorm) 2
  have hβE : β ∈ Epi := mem_Epi_of_alg hβ
  have hXE : piI ∈ Epi := piI_mem_Epi
  -- `W`, the value of `π²t²` after eliminating `Im u`.
  set W : ℂ := (r : ℂ) ^ 2 * piI ^ 4 + (A + 2 * (r : ℂ) * β) * piI ^ 2 + β ^ 2 with hW_def
  have hWE : W ∈ Epi := by
    rw [hW_def]
    exact add_mem (add_mem (mul_mem (pow_mem (Subalgebra.algebraMap_mem _ _) 2)
        (pow_mem hXE 4))
      (mul_mem (add_mem hAE (mul_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.algebraMap_mem _ _)) hβE)) (pow_mem hXE 2))) (pow_mem hβE 2)
  -- the quartic relation, in `ℂ`
  have hnormsq : (‖u‖ : ℝ) ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hn' : A = (((u.re : ℝ)) : ℂ) ^ 2 + (((u.im : ℝ)) : ℂ) ^ 2 := by
    rw [hA_def, ← Complex.ofReal_pow, hnormsq]; push_cast; ring
  have hkey : piI ^ 2 * ((((u.re : ℝ)) : ℂ)) ^ 2 = W := by
    rw [hW_def, piI_sq, piI_pow_four, hn', hβ_def]
    push_cast
    ring
  have h1 : piI ^ 2 * ((((u.re : ℝ)) : ℂ)) ^ 2 ∈ Epi := by rw [hkey]; exact hWE
  have h2 : ((((u.re : ℝ)) : ℂ)) ^ 2 ∈ Epi := by
    refine mem_Epi_of_mul_piI (mem_Epi_of_mul_piI ?_)
    have : piI * (piI * ((((u.re : ℝ)) : ℂ)) ^ 2)
        = piI ^ 2 * ((((u.re : ℝ)) : ℂ)) ^ 2 := by ring
    rw [this]; exact h1
  rw [mem_Epi_iff] at h2 ⊢
  exact IsAlgebraic.of_pow (n := 2) (by norm_num) h2

/-- `i · Im u = ν − r·πi`. -/
theorem im_mem_Epi (u : ℂ) (r : ℚ)
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    Complex.I * (((u.im : ℝ)) : ℂ) ∈ Epi := by
  have hν := nu_mem_Epi u r hβ
  have hX := piI_mem_Epi
  have hkey : Complex.I * (((u.im : ℝ)) : ℂ)
      = Complex.I * (((u.im + (r : ℝ) * Real.pi : ℝ)) : ℂ) - (r : ℂ) * piI := by
    rw [piI]; push_cast; ring
  rw [hkey]
  exact sub_mem hν (mul_mem (Subalgebra.algebraMap_mem _ _) hX)

theorem self_mem_Epi (u : ℂ) (r : ℚ)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    u ∈ Epi := by
  have h : u = (((u.re : ℝ)) : ℂ) + Complex.I * (((u.im : ℝ)) : ℂ) := by
    conv_lhs => rw [← Complex.re_add_im u]
    ring
  rw [h]
  exact add_mem (re_mem_Epi u r hnorm hβ) (im_mem_Epi u r hβ)

theorem conj_mem_Epi (u : ℂ) (r : ℚ)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    (starRingEnd ℂ) u ∈ Epi := by
  have h : (starRingEnd ℂ) u = (((u.re : ℝ)) : ℂ) - Complex.I * (((u.im : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h]
  exact sub_mem (re_mem_Epi u r hnorm hβ) (im_mem_Epi u r hβ)

/-! ## 4. The transcendence-degree bound for the aligned matrix. -/

/-- **The certificate.**  For the four entries `u`, `ν = i(Im u + rπ)`, `l₃ = c·2πi`,
`conj u` of the aligned matrix, the `ℚ`-algebra they generate has transcendence degree at
most one.  The generator is `πi = l₃/(2c)`, which lies in that algebra; `π` itself need
not. -/
theorem trdeg_aligned_le_one (u : ℂ) (r c : ℚ) (hc : c ≠ 0)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) :
    Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ
      ({u, Complex.I * (((u.im + (r : ℝ) * Real.pi : ℝ)) : ℂ),
        (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I),
        (starRingEnd ℂ) u} : Set ℂ)) ≤ 1 := by
  set ν : ℂ := Complex.I * (((u.im + (r : ℝ) * Real.pi : ℝ)) : ℂ) with hν_def
  set l₃ : ℂ := (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) with hl3_def
  set S : Set ℂ := {u, ν, l₃, (starRingEnd ℂ) u} with hS_def
  have hl3S : l₃ ∈ Algebra.adjoin ℚ S := Algebra.subset_adjoin (by simp [hS_def])
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hxB : piI ∈ Algebra.adjoin ℚ S := by
    have hkey : piI = ((((2 * c)⁻¹ : ℚ)) : ℂ) * l₃ := by
      rw [hl3_def, piI]
      push_cast
      field_simp
    rw [hkey]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) hl3S
  refine trdeg_le_one_of_adjoin_singleton hxB ?_
  have huE : u ∈ Epi := self_mem_Epi u r hnorm hβ
  have hνE : ν ∈ Epi := nu_mem_Epi u r hβ
  have hl3E : l₃ ∈ Epi := by
    have h2 : l₃ = (c : ℂ) * (piI + piI) := by rw [hl3_def, piI]; ring
    rw [h2]
    exact mul_mem (Subalgebra.algebraMap_mem _ _) (add_mem piI_mem_Epi piI_mem_Epi)
  have hcjE : (starRingEnd ℂ) u ∈ Epi := conj_mem_Epi u r hnorm hβ
  have hle : Algebra.adjoin ℚ S ≤ Epi := by
    refine Algebra.adjoin_le ?_
    rintro z hz
    simp only [hS_def, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with h | h | h | h <;> rw [h, SetLike.mem_coe]
    exacts [huE, hνE, hl3E, hcjE]
  intro y hy
  exact mem_Epi_iff.1 (hle hy)

/-! ## 5. The published node, and the leaf half it closes. -/

-- `DiazModulus.four_exponentials_trdeg_one`, verbatim, as an explicit hypothesis.
def FourExpTrdegOne : Prop :=
  ∀ l₁₁ l₁₂ l₂₁ l₂₂ : ℂ,
    IsAlgebraic ℚ (Complex.exp l₁₁) → IsAlgebraic ℚ (Complex.exp l₁₂) →
    IsAlgebraic ℚ (Complex.exp l₂₁) → IsAlgebraic ℚ (Complex.exp l₂₂) →
    l₁₁ ≠ 0 → l₁₂ ≠ 0 → l₂₁ ≠ 0 → l₂₂ ≠ 0 →
    l₁₁ * l₂₂ = l₁₂ * l₂₁ →
    Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₁₁, l₁₂, l₂₁, l₂₂} : Set ℂ)) ≤ 1 →
    (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₂₁ = 0 ∧ (a : ℂ) * l₁₂ + (b : ℂ) * l₂₂ = 0)
    ∨ (∃ a b : ℚ, ¬(a = 0 ∧ b = 0) ∧
        (a : ℂ) * l₁₁ + (b : ℂ) * l₁₂ = 0 ∧ (a : ℂ) * l₂₁ + (b : ℂ) * l₂₂ = 0)

/-- **Main route lemma, unconditional version.**  Same matrix as
`DiazAligned.transcendental_of_fourExpDet`, but fed to the transcendence-degree-one form of
the four exponentials statement, which is a theorem.  The extra input over that lemma is
`‖u‖` algebraic and `π(Im u + rπ)` algebraic — exactly what makes the four entries
algebraic over `ℚ[πi]`. -/
theorem transcendental_of_trdegOne (h4 : FourExpTrdegOne) (u : ℂ)
    (hre : u.re ≠ 0)
    (hirr : ¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi)
    (hnorm : IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ))
    {r c₀ : ℚ}
    (hβ : IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ))
    (hc : (‖u‖ : ℝ) ^ 2 = (c₀ : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) :
    Transcendental ℚ (Complex.exp u) := by
  intro hexp
  have hπ0 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hπC : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ0
  set s : ℝ := u.im + (r : ℝ) * Real.pi with hs_def
  have hs0 : s ≠ 0 := by
    intro h
    refine hirr ⟨-r, ?_⟩
    have : u.im = -((r : ℝ) * Real.pi) := by rw [hs_def] at h; linarith
    push_cast; linarith [this]
  have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs0
  have hu0 : u ≠ 0 := by intro h; exact hre (by rw [h]; rfl)
  have hnorm_pos : (0 : ℝ) < (‖u‖ : ℝ) ^ 2 := by
    have : (0 : ℝ) < ‖u‖ := norm_pos_iff.2 hu0
    positivity
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    rw [h] at hc
    have hz : (‖u‖ : ℝ) ^ 2 = 0 := by rw [hc]; push_cast; ring
    linarith [hnorm_pos, hz]
  set ν : ℂ := Complex.I * ((s : ℝ) : ℂ) with hν_def
  have hν0 : ν ≠ 0 := mul_ne_zero Complex.I_ne_zero hsC
  set c : ℚ := -c₀ / 2 with hc_def
  have hcne : c ≠ 0 := by rw [hc_def]; simpa using hc₀0
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hcne
  set l₃ : ℂ := (c : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) with hl3_def
  have hl30 : l₃ ≠ 0 := by
    rw [hl3_def]
    exact mul_ne_zero hcC (by simp [hπC, Complex.I_ne_zero])
  have hconj0 : (starRingEnd ℂ) u ≠ 0 := by simpa using hu0
  -- the four exponentials are algebraic
  have hexpν : IsAlgebraic ℚ (Complex.exp ν) := by
    refine IsAlgebraic.of_pow (n := 2 * r.den) (by positivity) ?_
    have hmul : (((2 * r.den : ℕ)) : ℂ) * ν =
        ((r.den : ℕ) : ℂ) * (u - (starRingEnd ℂ) u)
          + ((r.num : ℤ) : ℂ) * (2 * ((Real.pi : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.sub_conj, hν_def, hs_def]
      push_cast [Rat.cast_def]
      field_simp
    have hkey : Complex.exp ν ^ (2 * r.den) =
        (Complex.exp u / (starRingEnd ℂ) (Complex.exp u)) ^ r.den := by
      rw [← Complex.exp_nat_mul, hmul, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        mul_one, Complex.exp_nat_mul, Complex.exp_sub, Complex.exp_conj]
    rw [hkey]
    exact alg_pow (alg_div hexp (alg_conj hexp)) r.den
  have hexpconj : IsAlgebraic ℚ (Complex.exp ((starRingEnd ℂ) u)) := by
    rw [Complex.exp_conj]; exact alg_conj hexp
  have hexpl₃ : IsAlgebraic ℚ (Complex.exp l₃) := by
    rw [hl3_def]; exact alg_exp_rat_two_pi_I c
  -- rows and columns are `ℚ`-independent
  have hrows : ∀ a b : ℚ, (a : ℂ) * u + (b : ℂ) * l₃ = 0 →
      (a : ℂ) * ν + (b : ℂ) * ((starRingEnd ℂ) u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 _
    have hre1 : ((a : ℂ) * u + (b : ℂ) * l₃).re = 0 := by rw [h1]; rfl
    have hz : ((a : ℂ) * u + (b : ℂ) * l₃).re = (a : ℝ) * u.re := by rw [hl3_def]; simp
    rw [hz] at hre1
    have ha : (a : ℝ) = 0 := by
      rcases mul_eq_zero.1 hre1 with h | h
      · exact h
      · exact absurd h hre
    have ha' : a = 0 := by exact_mod_cast ha
    refine ⟨ha', ?_⟩
    rw [ha'] at h1
    simp only [Rat.cast_zero, zero_mul, zero_add] at h1
    have : (b : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hl30
    exact_mod_cast this
  have hcols : ∀ a b : ℚ, (a : ℂ) * u + (b : ℂ) * ν = 0 →
      (a : ℂ) * l₃ + (b : ℂ) * ((starRingEnd ℂ) u) = 0 → a = 0 ∧ b = 0 := by
    intro a b h1 _
    have hre1 : ((a : ℂ) * u + (b : ℂ) * ν).re = 0 := by rw [h1]; rfl
    have hz : ((a : ℂ) * u + (b : ℂ) * ν).re = (a : ℝ) * u.re := by rw [hν_def]; simp
    rw [hz] at hre1
    have ha : (a : ℝ) = 0 := by
      rcases mul_eq_zero.1 hre1 with h | h
      · exact h
      · exact absurd h hre
    have ha' : a = 0 := by exact_mod_cast ha
    refine ⟨ha', ?_⟩
    rw [ha'] at h1
    simp only [Rat.cast_zero, zero_mul, zero_add] at h1
    have : (b : ℂ) = 0 := by
      rcases mul_eq_zero.1 h1 with h | h
      · exact h
      · exact absurd h hν0
    exact_mod_cast this
  -- the determinant vanishes
  have hdet : u * ((starRingEnd ℂ) u) = ν * l₃ := by
    have h1 : u * (starRingEnd ℂ) u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have h2 : ν * l₃ = -(2 * (c : ℂ) * ((Real.pi : ℝ) : ℂ) * ((s : ℝ) : ℂ)) := by
      rw [hν_def, hl3_def]
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h1, h2, hc]
    rw [hc_def]
    push_cast
    ring
  -- the transcendence degree bound
  have htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ
      ({u, ν, l₃, (starRingEnd ℂ) u} : Set ℂ)) ≤ 1 :=
    trdeg_aligned_le_one u r c hcne hnorm hβ
  rcases h4 u ν l₃ ((starRingEnd ℂ) u) hexp hexpν hexpl₃ hexpconj hu0 hν0 hl30 hconj0
      hdet htr with ⟨a, b, hab, h1, h2⟩ | ⟨a, b, hab, h1, h2⟩
  · exact hab (hrows a b h1 h2)
  · exact hab (hcols a b h1 h2)


end DiazTrdegSol

open DiazModulus in
-- The rational-multiple half of the period-aligned leaf, from the transcendence-degree-one
-- case of the four exponentials statement.
theorem solution :
    ∀ u : ℂ, u ≠ 0 → IsAlgebraic ℚ ((‖u‖ : ℝ) : ℂ) → (Complex.exp u).im ≠ 0 →
      ¬ (u.im = 0 ∨ u.re = 0) → (¬ ∃ q : ℚ, u.im = (q : ℝ) * Real.pi) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ)) →
      (∃ r : ℚ, r ≠ 0 ∧
        IsAlgebraic ℚ ((Real.pi * (u.im + (r : ℝ) * Real.pi) : ℝ) : ℂ) ∧
        ∃ c : ℚ, (‖u‖ : ℝ) ^ 2 = (c : ℝ) * (Real.pi * (u.im + (r : ℝ) * Real.pi))) →
      Transcendental ℚ (Complex.exp u) := by
  intro u _ hnorm _ hax hirr _ hnrm
  obtain ⟨r, _, hβ, c₀, hc⟩ := hnrm
  have hre : u.re ≠ 0 := fun h => hax (Or.inr h)
  exact DiazTrdegSol.transcendental_of_trdegOne DiazModulus.four_exponentials_trdeg_one
    u hre hirr hnorm (r := r) (c₀ := c₀) hβ hc
