-- Prove2me | solution 1 for DiazModulus.progression_space_ratio_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T19:27:31.686083+00:00
-- url     : https://prove2.me/submissions/b4e97be1-c48b-41c0-8c2f-88e9b84c7336

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # A ratio `h = p(u)/q(u)` with a dimension-5 progression space has degree at most 2

Write `K = Q̄`, `d = max(deg p, deg q)`; `p, q ≠ 0` (otherwise coprimality makes the other one a
unit and `d = 0`). Since `u` is transcendental, `X ↦ u` extends to a field embedding
`ι : K(X) → ℂ` (`RatFunc.liftAlgHom`), and `ι f = h` for `f = p/q ∈ K(X)`. From
`p · denom f = q · num f` and coprimality, `p ∣ num f` and `q ∣ denom f`, so by Mathlib's degree
formula `[K(X) : K(f)] = max(deg num f, deg denom f)` (`RatFunc.finrank_eq_max_natDegree`, from the
Lüroth file) we get `d ≤ [K(X) : K(f)]`. In particular `f` is not constant, so it is transcendental
over `K`, and so is `h`: the `c hᵏ` (`k ≤ 3`) are independent and span a space `P` of dimension 4,
while `H = ⟨1, u, u⁻¹⟩` has dimension 3. As `H ⊔ P ≤ W` has dimension 5, `dim (H ⊓ P) ≥ 2`.
Two non-proportional `x₁, x₂ ∈ H ⊓ P` read `xᵢ = c Aᵢ(h)`, `u xᵢ = Rᵢ(u)` with `deg Rᵢ ≤ 2`. Then
`φ = R₁/R₂ ∈ K(X)` satisfies `ι φ = x₁/x₂ = ι (A₁(f)/A₂(f))`, so `φ ∈ K(f)`, and `φ` is not
constant. The tower `K(φ) ≤ K(f) ≤ K(X)` gives `[K(X) : K(f)] ∣ [K(X) : K(φ)] ≤ 2`, so `d ≤ 2`.
-/

namespace R13_degree

open DiazModulus Polynomial

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem cubic_zero {z : ℂ} (hz : Transcendental (↥Qbar) z) (a₀ a₁ a₂ a₃ : ↥Qbar)
    (h : (a₀ : ℂ) + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3 = 0) :
    a₀ = 0 ∧ a₁ = 0 ∧ a₂ = 0 ∧ a₃ = 0 := by
  have hP := transcendental_iff.1 hz (C a₀ + C a₁ * X + C a₂ * X ^ 2 + C a₃ * X ^ 3)
    (by simpa [am] using h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using congrArg (coeff · 0) hP
  · simpa using congrArg (coeff · 1) hP
  · simpa using congrArg (coeff · 2) hP
  · simpa using congrArg (coeff · 3) hP

theorem aeval_injective {u : ℂ} (hu : u ∉ Qbar) :
    Function.Injective (aeval (R := ↥Qbar) u) :=
  (injective_iff_map_eq_zero _).2 fun P hP => transcendental_iff.1 (tr_of_not_mem hu) P hP

/-- The evaluation embedding `K(X) → ℂ`, `X ↦ u`. -/
noncomputable def ev {u : ℂ} (hu : u ∉ Qbar) : RatFunc (↥Qbar) →ₐ[↥Qbar] ℂ :=
  RatFunc.liftAlgHom (aeval u)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (aeval_injective hu))

theorem ev_alg {u : ℂ} (hu : u ∉ Qbar) (P : (↥Qbar)[X]) :
    ev hu (algebraMap _ _ P) = aeval u P := by
  simp [ev, RatFunc.liftAlgHom_apply]

/-- `d ≤ [K(X) : K(p/q)]` for coprime non-zero `p, q`. -/
theorem lower_bound {p q : (↥Qbar)[X]} (hcop : IsCoprime p q) (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    max p.natDegree q.natDegree ≤ Module.finrank
      (IntermediateField.adjoin (↥Qbar)
        {(algebraMap _ (RatFunc (↥Qbar)) p / algebraMap _ _ q : RatFunc (↥Qbar))})
      (RatFunc (↥Qbar)) := by
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hcross : p * f.denom = q * f.num := by
    apply IsFractionRing.injective (↥Qbar)[X] (RatFunc (↥Qbar))
    have h2 : algebraMap _ (RatFunc (↥Qbar)) f.num / algebraMap _ _ f.denom =
        algebraMap _ (RatFunc (↥Qbar)) p / algebraMap _ _ q := RatFunc.num_div_denom f
    rw [div_eq_div_iff (RatFunc.algebraMap_ne_zero f.denom_ne_zero)
      (RatFunc.algebraMap_ne_zero hq0)] at h2
    simp only [map_mul]
    linear_combination -h2
  have hnum0 : f.num ≠ 0 := by
    intro e; rw [e, mul_zero] at hcross; exact mul_ne_zero hp0 f.denom_ne_zero hcross
  have hdp : p ∣ f.num :=
    hcop.dvd_of_dvd_mul_left ⟨f.denom, by linear_combination -hcross⟩
  have hdq : q ∣ f.denom :=
    hcop.symm.dvd_of_dvd_mul_left ⟨f.num, by linear_combination hcross⟩
  rw [RatFunc.finrank_eq_max_natDegree]
  exact max_le_max (natDegree_le_of_dvd hdp hnum0) (natDegree_le_of_dvd hdq f.denom_ne_zero)

/-- `h = p(u)/q(u)` is transcendental over `K` when `d ≥ 1`. -/
theorem h_transcendental {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hdeg : 1 ≤ max p.natDegree q.natDegree) :
    Transcendental (↥Qbar) (aeval u p / aeval u q) := by
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hfnc : ¬ ∃ k, f = RatFunc.C k := by
    intro hk
    have hb : max p.natDegree q.natDegree ≤ max f.num.natDegree f.denom.natDegree := by
      have := lower_bound hcop hp0 hq0
      rw [RatFunc.finrank_eq_max_natDegree] at this
      exact this
    rw [RatFunc.eq_C_iff] at hk
    omega
  have hιf : ev hu f = aeval u p / aeval u q := by rw [hf, map_div₀, ev_alg, ev_alg]
  rintro ⟨A, hA0, hA⟩
  refine RatFunc.transcendental_of_ne_C f hfnc ⟨A, hA0, (ev hu).toRingHom.injective ?_⟩
  change ev hu (aeval f A) = ev hu 0
  rw [← aeval_algHom_apply, hιf, hA, map_zero]

/-- The degree argument: two non-proportional elements of `H ⊓ P` force `d ≤ 2`. -/
theorem ratio_bound {u : ℂ} (hu : u ∉ Qbar) {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) {c x₁ x₂ : ℂ} (hc : c ≠ 0) (hx₂ : x₂ ≠ 0)
    (hne : ∀ k : ↥Qbar, x₁ ≠ k * x₂) {A₁ A₂ R₁ R₂ : (↥Qbar)[X]}
    (hR₁ : R₁.natDegree ≤ 2) (hR₂ : R₂.natDegree ≤ 2)
    (hA₁ : c * aeval (aeval u p / aeval u q) A₁ = x₁)
    (hA₂ : c * aeval (aeval u p / aeval u q) A₂ = x₂)
    (hE₁ : aeval u R₁ = u * x₁) (hE₂ : aeval u R₂ = u * x₂) :
    max p.natDegree q.natDegree ≤ 2 := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hinj : Function.Injective (ev hu) := (ev hu).toRingHom.injective
  have hdf := lower_bound hcop hp0 hq0
  set f : RatFunc (↥Qbar) := algebraMap _ _ p / algebraMap _ _ q with hf
  have hιf : ev hu f = aeval u p / aeval u q := by rw [hf, map_div₀, ev_alg, ev_alg]
  have hR₁0 : R₁ ≠ 0 := by
    intro e; rw [e, map_zero] at hE₁
    exact hne 0 (by simpa [hu0] using hE₁.symm)
  have hR₂0 : R₂ ≠ 0 := by
    intro e; rw [e, map_zero] at hE₂
    exact hx₂ (by simpa [hu0] using hE₂.symm)
  set φ : RatFunc (↥Qbar) := algebraMap _ _ R₁ / algebraMap _ _ R₂ with hφ
  have hιφ : ev hu φ = x₁ / x₂ := by
    rw [hφ, map_div₀, ev_alg, ev_alg, hE₁, hE₂, mul_div_mul_left _ _ hu0]
  have hφmem : φ ∈ IntermediateField.adjoin (↥Qbar) {f} := by
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨A₁, A₂, hinj ?_⟩
    rw [hιφ, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hιf, ← hA₁, ← hA₂]
    exact mul_div_mul_left _ _ hc
  have hφnc : ¬ ∃ k, φ = RatFunc.C k := by
    rintro ⟨k, hk⟩
    apply hne k
    have : ev hu φ = k := by rw [hk, ← RatFunc.algebraMap_eq_C, AlgHom.commutes]; rfl
    rw [hιφ] at this
    exact (div_eq_iff hx₂).1 this
  have hφdeg : Module.finrank (IntermediateField.adjoin (↥Qbar) {φ}) (RatFunc (↥Qbar)) ≤ 2 := by
    rw [RatFunc.finrank_eq_max_natDegree]
    exact max_le ((natDegree_le_of_dvd (RatFunc.num_div_dvd R₁ hR₂0) hR₁0).trans hR₁)
      ((natDegree_le_of_dvd (RatFunc.denom_div_dvd R₁ R₂) hR₂0).trans hR₂)
  have hpos : 0 < Module.finrank (IntermediateField.adjoin (↥Qbar) {φ}) (RatFunc (↥Qbar)) := by
    rw [RatFunc.finrank_eq_max_natDegree]
    rw [RatFunc.eq_C_iff] at hφnc
    omega
  have hle : IntermediateField.adjoin (↥Qbar) {φ} ≤ IntermediateField.adjoin (↥Qbar) {f} :=
    IntermediateField.adjoin_simple_le_iff.2 hφmem
  have := Nat.le_of_dvd hpos (IntermediateField.finrank_dvd_of_le_left hle)
  omega

/-- Unpacking membership in `H ⊓ P`. -/
theorem unpack {u c h x : ℂ} (hu0 : u ≠ 0)
    (hx : x ∈ Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) ⊓
      Submodule.span (↥Qbar) (Set.range (fun k : Fin 4 => c * h ^ (k : ℕ)))) :
    ∃ A R : (↥Qbar)[X], R.natDegree ≤ 2 ∧ c * aeval h A = x ∧ aeval u R = u * x := by
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).1
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun (↥Qbar)).1 (Submodule.mem_inf.1 hx).2
  simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at ha
  simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul,
    show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
    show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hb
  refine ⟨C (b 0) + C (b 1) * X + C (b 2) * X ^ 2 + C (b 3) * X ^ 3,
    C (a 2) + C (a 0) * X + C (a 1) * X ^ 2, by compute_degree!, ?_, ?_⟩
  · simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
    linear_combination hb
  · simp only [map_add, map_mul, aeval_C, am, map_pow, aeval_X]
    rw [← ha]; field_simp; ring

end R13_degree

open DiazModulus R13_degree Polynomial in
theorem solution
    (u : ℂ) (hu : u ∉ Qbar) (p q : Polynomial ↥Qbar) (hcop : IsCoprime p q)
    (hdeg : 1 ≤ max p.natDegree q.natDegree) (c : ℂ) (hc : c ≠ 0)
    (hdim : Module.finrank (↥Qbar) (Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
      Set.range (fun k : Fin 4 => c * (Polynomial.aeval u p / Polynomial.aeval u q) ^ (k : ℕ)))) = 5) :
    max p.natDegree q.natDegree ≤ 2 := by
  by_contra hd
  push Not at hd
  set h := aeval u p / aeval u q with hh
  set W := Submodule.span Qbar (({1, u, u⁻¹} : Set ℂ) ∪
    Set.range (fun k : Fin 4 => c * h ^ (k : ℕ))) with hW
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hp0 : p ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_left.1 hcop)
    simp [this] at hdeg
  have hq0 : q ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
    simp [this] at hdeg
  have htr : Transcendental (↥Qbar) h := h_transcendental hu hcop hp0 hq0 hdeg
  have h1 : (1 : ℂ) ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hu1 : u ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hui : u⁻¹ ∈ W := Submodule.subset_span (Or.inl (by simp))
  have hP : ∀ k : ℕ, k < 4 → c * h ^ k ∈ W :=
    fun k hk => Submodule.subset_span (Or.inr ⟨⟨k, hk⟩, rfl⟩)
  set H := Submodule.span (↥Qbar) (Set.range ![(1 : ℂ), u, u⁻¹]) with hH
  set P := Submodule.span (↥Qbar) (Set.range (fun j : Fin 4 => c * h ^ (j : ℕ))) with hP'
  have hHli : LinearIndependent (↥Qbar) ![(1 : ℂ), u, u⁻¹] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_three, Subfield.smul_def, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, smul_eq_mul, Matrix.tail_cons] at hg
    have := cubic_zero (tr_of_not_mem hu) (g 2) (g 0) (g 1) 0 (by
      have hu' : u * u⁻¹ = 1 := mul_inv_cancel₀ hu0
      push_cast
      linear_combination u * hg - (g 2 : ℂ) * hu')
    intro i; fin_cases i
    exacts [this.2.1, this.2.2.1, this.1]
  have hPli : LinearIndependent (↥Qbar) (fun j : Fin 4 => c * h ^ (j : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, Subfield.smul_def, smul_eq_mul,
      show ((0 : Fin 4) : ℕ) = 0 from rfl, show ((1 : Fin 4) : ℕ) = 1 from rfl,
      show ((2 : Fin 4) : ℕ) = 2 from rfl, show ((3 : Fin 4) : ℕ) = 3 from rfl] at hg
    have := cubic_zero htr (g 0) (g 1) (g 2) (g 3) (by
      have : c * ((g 0 : ℂ) + g 1 * h + g 2 * h ^ 2 + g 3 * h ^ 3) = 0 := by
        linear_combination hg
      exact (mul_eq_zero.1 this).resolve_left hc)
    intro i; fin_cases i
    exacts [this.1, this.2.1, this.2.2.1, this.2.2.2]
  have : FiniteDimensional (↥Qbar) H := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) P := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have : FiniteDimensional (↥Qbar) W :=
    FiniteDimensional.span_of_finite _ ((Set.toFinite _).union (Set.finite_range _))
  have hfH : Module.finrank (↥Qbar) H = 3 := by rw [hH, finrank_span_eq_card hHli]; simp
  have hfP : Module.finrank (↥Qbar) P = 4 := by rw [hP', finrank_span_eq_card hPli]; simp
  have hle : H ⊔ P ≤ W := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [h1, hu1, hui]
    · rintro _ ⟨j, rfl⟩
      exact hP j (by omega)
  -- if `d > 2`, any two elements of `H ⊓ P` are proportional
  have key : ∀ x₁ ∈ H ⊓ P, ∀ x₂ ∈ H ⊓ P, x₂ ≠ 0 → ∃ k : ↥Qbar, x₁ = k * x₂ := by
    intro x₁ hx₁ x₂ hx₂ hx₂0
    by_contra hne
    push Not at hne
    obtain ⟨A₁, R₁, hR₁, hA₁, hE₁⟩ := unpack hu0 hx₁
    obtain ⟨A₂, R₂, hR₂, hA₂, hE₂⟩ := unpack hu0 hx₂
    have := ratio_bound hu hcop hp0 hq0 hc hx₂0 hne hR₁ hR₂ hA₁ hA₂ hE₁ hE₂
    omega
  have hfin : Module.finrank (↥Qbar) ↥(H ⊓ P) ≤ 1 := by
    by_cases hb : H ⊓ P = ⊥
    · rw [hb, finrank_bot]; omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    refine finrank_le_one ⟨v, hv⟩ ?_
    rintro ⟨w, hw⟩
    obtain ⟨k, hk⟩ := key w hw v hv hv0
    exact ⟨k, Subtype.ext (by simp [hk, Subfield.smul_def])⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq H P
  have hmono := Submodule.finrank_mono hle
  rw [hdim] at hmono
  omega
