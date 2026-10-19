-- Prove2me | solution 1 for DiazModulus.two_by_three_configuration_ratio_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-18T14:46:47.137483+00:00
-- url     : https://prove2.me/submissions/dc53680b-6d90-43b0-876b-94d2a845453a

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_progression_space_ratio_degree_le_two
import Theorems.Thm_DiazModulus_progression_pair_span_ratio_degree_le_two

open Complex ComplexConjugate

/-! # A configuration in a space of dimension at most five containing 1, u, 1/u has a ratio of degree at most two

Let `h = p(u)/q(u)`. Coprimality and `max(deg p, deg q) ≥ 1` give `q ≠ 0`, so `q(u) ≠ 0` and
`x₁ = x₀ h`. As `x` is free, `h ∉ Q̄`, so `h` is transcendental over `Q̄` (`Q̄` is algebraically
closed in `ℂ`). Put `Y' = span(x₀ yⱼ)`, of dimension 3, and `hY'`, its image under multiplication
by `h`; then `XY := Y' + hY'` is spanned by the six products and lies in `W`, so
`dim(Y' ∩ hY') = 6 − dim XY ≥ 1`. Write `H = span(1, u, u⁻¹) ≤ W`.
* If `H ≤ XY`: take `0 ≠ h t ∈ Y' ∩ hY'` with `t ∈ Y'`. Then `t, h t` are free, and some
  `c' ∈ Y'` is outside their span, so `Y' = span(t, h t, c')`. With `k = c'/t`,
  `XY ≤ span(t, t h, t h², t k, t h k)`, which therefore contains `1, u, u⁻¹`: this is
  `progression_pair_span_ratio_degree_le_two`.
* Otherwise `XY < XY + H ≤ W` gives `dim XY ≤ 4`, so `I = Y' ∩ hY'` has dimension `≥ 2`, and so
  does `h⁻¹ I ≤ Y'`. Two planes in the 3-space `Y'` meet: `0 ≠ z ∈ I ∩ h⁻¹ I`, `z = h t`, gives
  `t, h t, h² t ∈ Y'`. The `t hᵏ` (`k ≤ 3`) are free and lie in `XY`, so they span it, and
  `span(H ∪ {t hᵏ})` strictly contains it inside `W`: its dimension is `5`, which is
  `progression_space_ratio_degree_le_two`.
-/

namespace R18_C2

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

/-- Multiplication by `h ≠ 0` as a `Q̄`-linear automorphism of `ℂ`. -/
noncomputable def mulE (h : ℂ) (hh : h ≠ 0) : ℂ ≃ₗ[↥Qbar] ℂ :=
  LinearEquiv.ofLinearMap (LinearMap.mulLeft (↥Qbar) h) (LinearMap.mulLeft (↥Qbar) h⁻¹)
    (LinearMap.ext fun z => by simp [hh]) (LinearMap.ext fun z => by simp [hh])

theorem mulE_apply (h : ℂ) (hh : h ≠ 0) (z : ℂ) : mulE h hh z = h * z := rfl

theorem smul_eq (a : ↥Qbar) (z : ℂ) : a • z = (a : ℂ) * z := rfl

end R18_C2

open DiazModulus R18_C2 Polynomial Submodule in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (W : Submodule (↥Qbar) ℂ)
    [FiniteDimensional (↥Qbar) W] (hW : Module.finrank (↥Qbar) W ≤ 5)
    (h1 : (1 : ℂ) ∈ W) (hu1 : u ∈ W) (hui : u⁻¹ ∈ W)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ W)
    (p q : (↥Qbar)[X]) (hcop : IsCoprime p q) (hdeg : 1 ≤ max p.natDegree q.natDegree)
    (hpq : x 1 * aeval u q = x 0 * aeval u p) :
    max p.natDegree q.natDegree ≤ 2 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop), natDegree_zero] at hdeg
    simp at hdeg
  have hqu : aeval u q ≠ 0 := fun h0 => hq0 (aeval_injective hu (by rw [h0, map_zero]))
  set h := aeval u p / aeval u q with hhdef
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  have hx1 : x 1 = x 0 * h := by rw [hhdef]; field_simp; linear_combination hpq
  have hnot : h ∉ Qbar := by
    intro hm
    have hxv : x = ![x 0, x 1] := by ext i; fin_cases i <;> rfl
    rw [hxv] at hx
    exact (LinearIndependent.pair_iff' hx0).1 hx ⟨h, hm⟩ (by rw [smul_eq, hx1, mul_comm])
  have htr : Transcendental (↥Qbar) h := tr_of_not_mem hnot
  have hh0 : h ≠ 0 := fun h0 => hnot (h0 ▸ Subfield.zero_mem _)
  set e := mulE h hh0 with he
  set c : Fin 3 → ℂ := fun j => x 0 * y j
  have hc : LinearIndependent (↥Qbar) c :=
    hy.map' (LinearMap.mulLeft (↥Qbar) (x 0)) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hx0))
  set Y' := span (↥Qbar) (Set.range c)
  have hY'3 : Module.finrank (↥Qbar) Y' = 3 := by rw [finrank_span_eq_card hc]; simp
  set hY := Y'.map (e : ℂ →ₗ[↥Qbar] ℂ)
  have hhY3 : Module.finrank (↥Qbar) hY = 3 := (LinearEquiv.finrank_map_eq e Y').trans hY'3
  have hY'W : Y' ≤ W := span_le.2 (Set.range_subset_iff.2 fun j => hxy 0 j)
  have hhYW : hY ≤ W := by
    change Submodule.map (e : ℂ →ₗ[↥Qbar] ℂ) (span (↥Qbar) (Set.range c)) ≤ W
    rw [map_span, span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    change h * (x 0 * y j) ∈ W
    rw [← mul_assoc, mul_comm h, ← hx1]
    exact hxy 1 j
  have hXYW : Y' ⊔ hY ≤ W := sup_le hY'W hhYW
  have := finiteDimensional_of_le hY'W
  have := finiteDimensional_of_le hhYW
  have hsum := finrank_sup_add_finrank_inf_eq Y' hY
  have hXY5 : Module.finrank (↥Qbar) ↥(Y' ⊔ hY) ≤ 5 := (finrank_mono hXYW).trans hW
  have hmulY : ∀ t ∈ Y', h * t ∈ hY := fun t ht => mem_map_of_mem (f := (e : ℂ →ₗ[↥Qbar] ℂ)) ht
  by_cases hH : (1 : ℂ) ∈ Y' ⊔ hY ∧ u ∈ Y' ⊔ hY ∧ u⁻¹ ∈ Y' ⊔ hY
  · -- `H ≤ XY`
    have hI : Y' ⊓ hY ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hsum
      omega
    obtain ⟨z, hz, hz0⟩ := exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨hzY, hzhY⟩ := mem_inf.1 hz
    obtain ⟨t, htY, rfl⟩ := mem_map.1 hzhY
    change h * t ∈ Y' at hzY
    change h * t ≠ 0 at hz0
    have ht0 : t ≠ 0 := fun h0 => hz0 (by rw [h0, mul_zero])
    have hli2 : LinearIndependent (↥Qbar) ![t, h * t] :=
      (LinearIndependent.pair_iff' ht0).2 fun a ha => by
        have hah : (a : ℂ) = h := mul_right_cancel₀ ht0 (by rw [← smul_eq]; exact ha)
        exact hnot (hah ▸ a.2)
    have hnle : ¬ Y' ≤ span (↥Qbar) (Set.range ![t, h * t]) := by
      intro hle
      have := FiniteDimensional.span_of_finite (↥Qbar) (Set.finite_range ![t, h * t])
      have := finrank_mono hle
      rw [finrank_span_eq_card hli2, hY'3] at this
      simp at this
    obtain ⟨c', hc'Y, hc'⟩ := SetLike.not_le_iff_exists.1 hnle
    have hli3 : LinearIndependent (↥Qbar) (Fin.cons c' ![t, h * t] : Fin 3 → ℂ) :=
      linearIndependent_finCons.2 ⟨hli2, hc'⟩
    have hTY : span (↥Qbar) (Set.range (Fin.cons c' ![t, h * t] : Fin 3 → ℂ)) ≤ Y' := by
      rw [span_le, Set.range_subset_iff]
      intro i
      fin_cases i
      · exact hc'Y
      · exact htY
      · exact hzY
    have hTeq := eq_of_le_of_finrank_eq hTY (by rw [finrank_span_eq_card hli3, hY'3]; simp)
    set k := c' / t
    set S := span (↥Qbar) ({t, t * h, t * h ^ 2, t * k, t * h * k} : Set ℂ)
    have hk1 : c' = t * k := by simp only [k]; field_simp
    have hk2 : h * c' = t * h * k := by simp only [k]; field_simp
    have hTS : ∀ i : Fin 3, (Fin.cons c' ![t, h * t] : Fin 3 → ℂ) i ∈ S ∧
        h * (Fin.cons c' ![t, h * t] : Fin 3 → ℂ) i ∈ S := by
      intro i
      fin_cases i
      · change c' ∈ S ∧ h * c' ∈ S
        exact ⟨by rw [hk1]; exact subset_span (by simp), by rw [hk2]; exact subset_span (by simp)⟩
      · change t ∈ S ∧ h * t ∈ S
        refine ⟨subset_span (by simp), ?_⟩
        rw [mul_comm]; exact subset_span (by simp)
      · change h * t ∈ S ∧ h * (h * t) ∈ S
        refine ⟨?_, ?_⟩
        · rw [mul_comm]; exact subset_span (by simp)
        · rw [show h * (h * t) = t * h ^ 2 by ring]; exact subset_span (by simp)
    have hYS : Y' ≤ S := by
      rw [← hTeq, span_le, Set.range_subset_iff]
      exact fun i => (hTS i).1
    have hhYS : hY ≤ S := by
      change Submodule.map (e : ℂ →ₗ[↥Qbar] ℂ) Y' ≤ S
      rw [← hTeq, map_span, span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact (hTS i).2
    have hXS := sup_le hYS hhYS
    exact DiazModulus.progression_pair_span_ratio_degree_le_two u hu p q hcop hdeg t k ht0
      (hXS hH.1) (hXS hH.2.1) (hXS hH.2.2)
  · -- `H ⊄ XY`
    have hHW : span (↥Qbar) ({1, u, u⁻¹} : Set ℂ) ≤ W := by
      rw [span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl <;> assumption
    have hlt : Y' ⊔ hY < (Y' ⊔ hY) ⊔ span (↥Qbar) ({1, u, u⁻¹} : Set ℂ) := by
      refine lt_of_le_of_ne le_sup_left fun heq => hH ?_
      have hle : span (↥Qbar) ({1, u, u⁻¹} : Set ℂ) ≤ Y' ⊔ hY := by
        rw [heq]; exact le_sup_right
      exact ⟨hle (subset_span (by simp)), hle (subset_span (by simp)),
        hle (subset_span (by simp))⟩
    have := finiteDimensional_of_le (sup_le hXYW hHW)
    have h4 : Module.finrank (↥Qbar) ↥(Y' ⊔ hY) ≤ 4 := by
      have := finrank_lt_finrank_of_lt hlt
      have := finrank_mono (sup_le hXYW hHW)
      omega
    set I := Y' ⊓ hY
    set J := I.map (e.symm : ℂ →ₗ[↥Qbar] ℂ)
    have hJI : Module.finrank (↥Qbar) J = Module.finrank (↥Qbar) I :=
      LinearEquiv.finrank_map_eq e.symm I
    have hJY : J ≤ Y' := by
      rintro z hz
      obtain ⟨i, hi, rfl⟩ := mem_map.1 hz
      obtain ⟨t, ht, rfl⟩ := mem_map.1 (mem_inf.1 hi).2
      change e.symm (e t) ∈ Y'
      rw [LinearEquiv.symm_apply_apply]
      exact ht
    have := finiteDimensional_of_le (inf_le_left.trans hY'W : I ≤ W)
    have := finiteDimensional_of_le (hJY.trans hY'W)
    have hsum2 := finrank_sup_add_finrank_inf_eq I J
    have hIJ3 : Module.finrank (↥Qbar) ↥(I ⊔ J) ≤ 3 := hY'3 ▸ finrank_mono (sup_le inf_le_left hJY)
    have hIJ : I ⊓ J ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hsum2
      omega
    obtain ⟨z, hz, hz0⟩ := exists_mem_ne_zero_of_ne_bot hIJ
    obtain ⟨hzI, hzJ⟩ := mem_inf.1 hz
    obtain ⟨hzY, hzhY⟩ := mem_inf.1 hzI
    obtain ⟨t, htY, rfl⟩ := mem_map.1 hzhY
    obtain ⟨i, hiI, hi⟩ := mem_map.1 hzJ
    have hie : i = e (e t) := by simpa using congrArg e hi
    rw [hie] at hiI
    have hh2 : h * (h * t) ∈ Y' := (mem_inf.1 hiI).1
    change h * t ∈ Y' at hzY
    change h * t ≠ 0 at hz0
    have ht0 : t ≠ 0 := fun h0 => hz0 (by rw [h0, mul_zero])
    set f4 : Fin 4 → ℂ := fun k => t * h ^ (k : ℕ)
    have hli4 : LinearIndependent (↥Qbar) f4 := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      simp only [f4, Fin.sum_univ_four, smul_eq] at hg
      have hg' : t * ((g 0 : ℂ) + g 1 * h + g 2 * h ^ 2 + g 3 * h ^ 3) = 0 := by
        rw [← hg]; simp; ring
      obtain ⟨e0, e1, e2, e3⟩ :=
        cubic_zero htr (g 0) (g 1) (g 2) (g 3) ((mul_eq_zero.1 hg').resolve_left ht0)
      intro i
      fin_cases i <;> assumption
    have hRXY : span (↥Qbar) (Set.range f4) ≤ Y' ⊔ hY := by
      rw [span_le, Set.range_subset_iff]
      intro k
      fin_cases k
      · exact mem_sup_left (by simpa [f4] using htY)
      · exact mem_sup_left (by simpa [f4, mul_comm] using hzY)
      · exact mem_sup_left (by
          simpa [f4, show t * h ^ 2 = h * (h * t) by ring] using hh2)
      · exact mem_sup_right (by
          simpa [f4, show t * h ^ 3 = h * (h * (h * t)) by ring] using hmulY _ hh2)
    have hReq := eq_of_le_of_finrank_le hRXY
      (by rw [finrank_span_eq_card hli4]; simpa using h4)
    have hHfW : span (↥Qbar) (({1, u, u⁻¹} : Set ℂ) ∪ Set.range f4) ≤ W :=
      span_le.2 (Set.union_subset (subset_span.trans hHW)
        (subset_span.trans (hRXY.trans hXYW)))
    have := finiteDimensional_of_le hHfW
    refine DiazModulus.progression_space_ratio_degree_le_two u hu p q hcop hdeg t ht0
      (le_antisymm ((finrank_mono hHfW).trans hW) ?_)
    have hlt2 : span (↥Qbar) (Set.range f4) <
        span (↥Qbar) (({1, u, u⁻¹} : Set ℂ) ∪ Set.range f4) := by
      refine lt_of_le_of_ne (span_mono Set.subset_union_right) fun heq => hH ?_
      have hle : span (↥Qbar) (({1, u, u⁻¹} : Set ℂ) ∪ Set.range f4) ≤ Y' ⊔ hY := by
        rw [← heq]; exact hRXY
      exact ⟨hle (subset_span (by simp)), hle (subset_span (by simp)),
        hle (subset_span (by simp))⟩
    have := finrank_lt_finrank_of_lt hlt2
    rw [finrank_span_eq_card hli4] at this
    exact this
