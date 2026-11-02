-- Prove2me | solution 1 for DiazModulus.invisible_cyclic_space_configuration_ratio_mobius
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:27:59.19634+00:00
-- url     : https://prove2.me/submissions/640a7158-d4fb-4c80-9e61-904ed873d837

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_invisible_cyclic_space_u_multiplier_space_eq
import Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element
import Theorems.Thm_DiazModulus_scalar_quadratic_space_visible_element_mem
import Theorems.Thm_DiazModulus_degree_two_configuration_pencil_normal_form
import Theorems.Thm_DiazModulus_configuration_ratio_quadratic_of_not_degree_one
import Theorems.Thm_DiazModulus_invisible_cyclic_space_pole_pencil
import Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator
import Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
import Theorems.Thm_DiazModulus_coprime_pencil_mobius

open Complex ComplexConjugate

/-! # Q1.6, cyclic case (ramified orbits included): every configuration ratio is a Möbius function of `P(u)/Q(u)`

Let `W = WB(P, Q, S₁, S₂)` be invisible. As in the two-orbit case
(`invisible_cyclic_space_u_multiplier_space_eq`, `u_multiplier_space_le_span_no_degree_one_no_visible_element`,
`configuration_ratio_quadratic_of_not_degree_one`, `degree_two_configuration_pencil_normal_form`),
`x₁/x₀ = p(u)/q(u)` and `(P′, Q′)` is a Möbius image of `(p, q)` with three cases.
- Scalar: `scalar_quadratic_space_visible_element_mem` puts a `t_x` in `W`, impossible.
- `W = WA(P′, Q′, …)`: `invisible_cyclic_space_pole_pencil` on `Q′S₁′/(uP′)` and `P′S₂′/(uQ′)` makes
  both `P′` and `Q′` multiples of `P`, against coprimality.
- `W = WB(P′, Q′, …)` (the cyclic core): the same node gives `P′ = κP` and
  `Q′S₁′/(uP′) = R₀(u)/u + μ′·QS₁/(uP)` with `μ′ ≠ 0`; `quadratic_space_mem_iff_numerator` writes the
  second generator over `uP²`. Eliminating gives `Q S₁ (μ′Q′ − κμQ) = P·B` with `deg B ≤ 4`, and
  `binary_quadratic_dvd_of_coprime_mul_eq` (`d = 4`, `e = 2`) gives `μ′Q′ = κμQ + c₀P`; `μ ≠ 0` since
  `P′`, `Q′` are coprime of degree 2.
So `(P′, Q′)` is an invertible combination of `(P, Q)`, and so is `(p, q)`. -/

namespace R21b_Q6b

open DiazModulus Polynomial

theorem am (x : ↥Qbar) : algebraMap (↥Qbar) ℂ x = x := rfl

theorem tr_of_not_mem {u : ℂ} (hu : u ∉ Qbar) : Transcendental (↥Qbar) u := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  exact (Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1 fun h' => hu (mem_Qbar_iff.2 h')

theorem aeval_ne_zero {u : ℂ} (hu : u ∉ Qbar) {P : (↥Qbar)[X]} (hP : P ≠ 0) : aeval u P ≠ 0 :=
  fun h => hP (transcendental_iff.1 (tr_of_not_mem hu) P h)

theorem aeval_inj {u : ℂ} (hu : u ∉ Qbar) {A B : (↥Qbar)[X]} (h : aeval u A = aeval u B) : A = B :=
  sub_eq_zero.1 (transcendental_iff.1 (tr_of_not_mem hu) _ (by rw [map_sub, h, sub_self]))

theorem q_ne_zero {p q : (↥Qbar)[X]} (hcop : IsCoprime p q)
    (hdeg : max p.natDegree q.natDegree = 2) : q ≠ 0 := by
  rintro rfl
  have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hcop)
  simp at hdeg
  omega

theorem aeval_lin (u : ℂ) (a b : ↥Qbar) (p q : (↥Qbar)[X]) :
    aeval u (C a * p + C b * q) = (a : ℂ) * aeval u p + (b : ℂ) * aeval u q := by
  simp only [map_add, map_mul, aeval_C, am]

/-- Two coprime polynomials of degree 2 are not multiples of one polynomial. -/
theorem not_both {X P' Q' : (↥Qbar)[X]} {k₁ k₂ : ↥Qbar} (hc : IsCoprime P' Q')
    (hd : max P'.natDegree Q'.natDegree = 2) (h₁ : P' = C k₁ * X) (h₂ : Q' = C k₂ * X) : False := by
  subst h₁ h₂
  have := natDegree_eq_zero_of_isUnit (isCoprime_self.1 hc.of_mul_left_right.of_mul_right_right)
  have := natDegree_C_mul_le k₁ X
  have := natDegree_C_mul_le k₂ X
  omega

/-- In a five-dimensional `span(1, u, u⁻¹, A, B)`, `A ∉ H₀`. -/
theorem not_mem_H0 {u A B : ℂ} (h5 : Module.finrank (↥Qbar) (Submodule.span Qbar ({1, u, u⁻¹, A, B} : Set ℂ)) = 5) :
    A ∉ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  classical
  intro hA
  have e : Submodule.span Qbar ({1, u, u⁻¹, A, B} : Set ℂ) =
      Submodule.span Qbar ((({1, u, u⁻¹, B} : Finset ℂ) : Set ℂ)) := by
    push_cast
    have hH : Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) ≤ Submodule.span Qbar ({1, u, u⁻¹, B} : Set ℂ) :=
      Submodule.span_mono (by intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto)
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by
      intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢; tauto))
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
    · exact hH hA
    · exact Submodule.subset_span (by simp)
  have h := finrank_span_finset_le_card (R := ↥Qbar) ({1, u, u⁻¹, B} : Finset ℂ)
  have h4 := Finset.card_le_four (a := (1 : ℂ)) (b := u) (c := u⁻¹) (d := B)
  unfold Set.finrank at h
  rw [← e, h5] at h
  omega

/-- The final Möbius bookkeeping: `(p, q) ↦ (P′, Q′) ↦ (A, B)` are both invertible. -/
theorem final {x0 x1 p q A B : ℂ} {a b c d r₁₁ r₁₂ r₂₁ r₂₂ : ↥Qbar} (hdet : a * d - b * c ≠ 0)
    (hr : r₁₁ * r₂₂ - r₁₂ * r₂₁ ≠ 0) (hpq : x1 * q = x0 * p)
    (h₁ : (a : ℂ) * p + b * q = r₁₁ * A + r₁₂ * B) (h₂ : (c : ℂ) * p + d * q = r₂₁ * A + r₂₂ * B) :
    ∃ α β γ δ : ℂ, α ∈ Qbar ∧ β ∈ Qbar ∧ γ ∈ Qbar ∧ δ ∈ Qbar ∧ α * δ - β * γ ≠ 0 ∧
      x1 * (γ * A + δ * B) = x0 * (α * A + β * B) := by
  refine ⟨(d * r₁₁ - b * r₂₁ : ↥Qbar), (d * r₁₂ - b * r₂₂ : ↥Qbar), (-c * r₁₁ + a * r₂₁ : ↥Qbar),
    (-c * r₁₂ + a * r₂₂ : ↥Qbar), Subtype.prop _, Subtype.prop _, Subtype.prop _, Subtype.prop _, ?_, ?_⟩
  · have e : (d * r₁₁ - b * r₂₁) * (-c * r₁₂ + a * r₂₂) - (d * r₁₂ - b * r₂₂) * (-c * r₁₁ + a * r₂₁) =
        (a * d - b * c) * (r₁₁ * r₂₂ - r₁₂ * r₂₁) := by ring
    have h : ((d * r₁₁ - b * r₂₁) * (-c * r₁₂ + a * r₂₂) - (d * r₁₂ - b * r₂₂) * (-c * r₁₁ + a * r₂₁) : ↥Qbar) ≠ 0 := by
      rw [e]; exact mul_ne_zero hdet hr
    exact_mod_cast h
  · push_cast
    linear_combination ((a : ℂ) * d - b * c) * hpq + (x1 * c + x0 * d) * h₁ - (x1 * a + x0 * b) * h₂


/-- `R(u)/u ∈ H₀` when `deg R ≤ 2`. -/
theorem quad_div_mem {u : ℂ} (hu0 : u ≠ 0) {R : (↥Qbar)[X]} (hR : R.natDegree ≤ 2) :
    aeval u R / u ∈ Submodule.span Qbar ({1, u, u⁻¹} : Set ℂ) := by
  have e : aeval u R / u = R.coeff 1 • (1 : ℂ) + R.coeff 2 • u + R.coeff 0 • u⁻¹ := by
    rw [aeval_eq_sum_range' (n := 3) (by omega)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Algebra.smul_def, am]
    field_simp
    ring
  rw [e]
  exact add_mem (add_mem (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))) (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

/-- A member of `span(1, u, u⁻¹, g)` is `R(u)/u + μ g` with `deg R ≤ 2`. -/
theorem mem_four {u f g : ℂ} (hu0 : u ≠ 0) (hf : f ∈ Submodule.span Qbar ({1, u, u⁻¹, g} : Set ℂ)) :
    ∃ R : (↥Qbar)[X], R.natDegree ≤ 2 ∧ ∃ μ : ↥Qbar, f = aeval u R / u + μ * g := by
  obtain ⟨c₁, w₁, hw₁, rfl⟩ := Submodule.mem_span_insert.1 hf
  obtain ⟨c₂, w₂, hw₂, rfl⟩ := Submodule.mem_span_insert.1 hw₁
  obtain ⟨c₃, w₃, hw₃, rfl⟩ := Submodule.mem_span_insert.1 hw₂
  obtain ⟨c₄, rfl⟩ := Submodule.mem_span_singleton.1 hw₃
  refine ⟨C c₃ + C c₁ * X + C c₂ * X ^ 2, by compute_degree!, c₄, ?_⟩
  simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, am, Algebra.smul_def]
  field_simp
  ring

end R21b_Q6b

open DiazModulus R21b_Q6b in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ)) :
    ∃ a b c d : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ d ∈ Qbar ∧ a * d - b * c ≠ 0 ∧
      x 1 * (c * aeval u P + d * aeval u Q) = x 0 * (a * aeval u P + b * aeval u Q) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hP0 : P ≠ 0 := q_ne_zero hcop.symm (by rw [max_comm]; exact hdeg)
  have hQ0 : Q ≠ 0 := q_ne_zero hcop hdeg
  have hPu := aeval_ne_zero hu hP0
  obtain ⟨h5, hZ, hD1⟩ := DiazModulus.invisible_cyclic_space_u_multiplier_space_eq u hu P Q S₁ S₂
    hcop hdeg hS₁ hS₂ hPS hP2
  set W := Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
    aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ) with hWdef
  have : FiniteDimensional (↥Qbar) W := FiniteDimensional.span_of_finite _ (Set.toFinite _)
  have h1 : (1 : ℂ) ∈ W := Submodule.subset_span (by simp)
  have hu1 : u ∈ W := Submodule.subset_span (by simp)
  have hui : u⁻¹ ∈ W := Submodule.subset_span (by simp)
  have hPT := (DiazModulus.u_multiplier_space_le_span_no_degree_one_no_visible_element u hu W hu1 hui
    (fun f hf huf => (hZ f).1 ⟨hf, huf⟩)).2
  have hrat : ∀ w ∈ W, w ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
    have hK : ∀ R : (↥Qbar)[X], aeval u R ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := fun R =>
      IntermediateField.algebra_adjoin_le_adjoin _ _ (Polynomial.aeval_mem_adjoin_singleton _ _)
    have hu' : u ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := IntermediateField.subset_adjoin _ _ rfl
    have hsub : ∀ t ∈ ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u Q * (aeval u Q * aeval u S₁ + aeval u P * aeval u S₂) / (u * aeval u P ^ 2)} : Set ℂ),
        t ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact inv_mem hu'
      · exact div_mem (mul_mem (hK _) (hK _)) (mul_mem hu' (hK _))
      · exact div_mem (mul_mem (hK _) (add_mem (mul_mem (hK _) (hK _)) (mul_mem (hK _) (hK _))))
          (mul_mem hu' (pow_mem (hK _) 2))
    exact fun w hw => (Submodule.span_le
      (p := (IntermediateField.adjoin Qbar ({u} : Set ℂ)).toSubalgebra.toSubmodule)).2 hsub hw
  obtain ⟨p, q, hpqc, hpqd, hpq⟩ := DiazModulus.configuration_ratio_quadratic_of_not_degree_one u hu W h5.le
    h1 hu1 hui hrat hD1 x y hx hy hxy
  obtain ⟨a, b, c, d, hdet, hcase⟩ := DiazModulus.degree_two_configuration_pencil_normal_form u hu W h5
    h1 hu1 hui x y hx hy hxy p q hpqc hpqd hpq
  obtain ⟨hc', hd'⟩ := DiazModulus.coprime_pencil_mobius p q hpqc hpqd a b c d hdet
  have hPv := aeval_lin u a b p q
  have hQv := aeval_lin u c d p q
  set P' := C a * p + C b * q
  set Q' := C c * p + C d * q
  have hP'0 : P' ≠ 0 := q_ne_zero hc'.symm (by rw [max_comm]; exact hd')
  have hQ'0 : Q' ≠ 0 := q_ne_zero hc' hd'
  have hP'2 : P'.natDegree ≤ 2 := le_of_max_le_left hd'.le
  have hQ'2 : Q'.natDegree ≤ 2 := le_of_max_le_right hd'.le
  have hP'u := aeval_ne_zero hu hP'0
  have hQ'u := aeval_ne_zero hu hQ'0
  suffices key : ∃ r₁₁ r₁₂ r₂₁ r₂₂ : ↥Qbar, r₁₁ * r₂₂ - r₁₂ * r₂₁ ≠ 0 ∧
      aeval u P' = r₁₁ * aeval u P + r₁₂ * aeval u Q ∧ aeval u Q' = r₂₁ * aeval u P + r₂₂ * aeval u Q by
    obtain ⟨r₁₁, r₁₂, r₂₁, r₂₂, hr, e₁, e₂⟩ := key
    exact final hdet hr hpq (hPv ▸ e₁) (hQv ▸ e₂)
  rcases hcase with hsc | ⟨S₁', S₂', hS₁', hS₂', hW'⟩ | ⟨S₁', S₂', hS₁', hS₂', hW'⟩
  · exact (hPT (DiazModulus.scalar_quadratic_space_visible_element_mem u hu W h1 hu1 hui P' Q' hc' hd' hsc)).elim
  · -- `W = WA(P′, Q′, …)`: both `P′` and `Q′` would be multiples of `P`
    have h5' := hW' ▸ h5
    have hg₁ : aeval u Q' * aeval u S₁' / (u * aeval u P') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    have hg₂ : aeval u P' * aeval u S₂' / (u * aeval u Q') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    obtain ⟨⟨k₁, e₁⟩, -⟩ := DiazModulus.invisible_cyclic_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hP2 P' (Q' * S₁') hP'2 hP'0 (natDegree_mul_le.trans (by omega)) _ hg₁ (not_mem_H0 h5')
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hP'u), map_mul])
    obtain ⟨⟨k₂, e₂⟩, -⟩ := DiazModulus.invisible_cyclic_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hP2 Q' (P' * S₂') hQ'2 hQ'0 (natDegree_mul_le.trans (by omega)) _ hg₂
      (not_mem_H0 (by rw [Set.pair_comm] at h5'; exact h5'))
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hQ'u), map_mul])
    exact (not_both hc' hd' e₁ e₂).elim
  · -- `W = WB(P′, Q′, …)`: the cyclic core
    have h5' := hW' ▸ h5
    have hg₁ : aeval u Q' * aeval u S₁' / (u * aeval u P') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    have hh₂ : aeval u Q' * (aeval u Q' * aeval u S₁' + aeval u P' * aeval u S₂') / (u * aeval u P' ^ 2) ∈ W := by
      rw [hW']; exact Submodule.subset_span (by simp)
    have hg₁0 := not_mem_H0 h5'
    obtain ⟨⟨κ, e₁⟩, hmem⟩ := DiazModulus.invisible_cyclic_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hP2 P' (Q' * S₁') hP'2 hP'0 (natDegree_mul_le.trans (by omega)) _ hg₁ hg₁0
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hP'u), map_mul])
    have hκ : κ ≠ 0 := by rintro rfl; simp [e₁] at hP'0
    have hκc : (κ : ℂ) ≠ 0 := fun h => hκ (Subtype.ext h)
    have hP'κ : aeval u P' = κ * aeval u P := by rw [e₁]; simp [am]
    obtain ⟨R₀, hR₀, μ', hg⟩ := mem_four hu0 hmem
    have hμ' : μ' ≠ 0 := by
      rintro rfl
      exact hg₁0 (by rw [hg]; simpa using quad_div_mem hu0 hR₀)
    have hμ'c : (μ' : ℂ) ≠ 0 := fun h => hμ' (Subtype.ext h)
    obtain ⟨A₂, b₁, μ, hA₂, hN⟩ := ((DiazModulus.quadratic_space_mem_iff_numerator u hu P Q S₁ S₂ hP0 hQ0).2 _).1 hh₂
    have v1' := div_mul_cancel₀ (aeval u Q' * aeval u S₁') (mul_ne_zero hu0 hP'u)
    have v2' := div_mul_cancel₀ (aeval u Q' * (aeval u Q' * aeval u S₁' + aeval u P' * aeval u S₂'))
      (mul_ne_zero hu0 (pow_ne_zero 2 hP'u))
    generalize aeval u Q' * aeval u S₁' / (u * aeval u P') = F at v1' hg
    generalize aeval u Q' * (aeval u Q' * aeval u S₁' + aeval u P' * aeval u S₂') / (u * aeval u P' ^ 2) = Hh at v2' hN
    rw [hP'κ] at v1' v2'
    have v1 : F * (u * aeval u P) = aeval u R₀ * aeval u P + μ' * (aeval u Q * aeval u S₁) := by
      rw [hg]; field_simp
    simp only [map_add, map_mul, map_pow, aeval_C, am] at hN
    have hS₁0 : S₁ ≠ 0 := by
      rintro rfl
      have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hPS)
      simp [coeff_eq_zero_of_natDegree_lt (show P.natDegree < 2 by omega)] at hP2
    -- the identity `Q S₁ (μ′Q′ − κμQ) = P·B`
    have hpoly : Q * S₁ * (C μ' * Q' - C κ * (C μ * Q)) =
        P * (C κ * (P * A₂ + C b₁ * (Q * S₁) + C μ * (Q * S₂)) - Q' * (R₀ + S₂')) := by
      apply aeval_inj hu
      simp only [map_add, map_sub, map_mul, aeval_C, am]
      apply mul_left_cancel₀ hκc
      linear_combination (-((κ : ℂ) * aeval u Q')) * v1 + aeval u Q' * v1' + (κ : ℂ) ^ 2 * hN - v2'
    have hm : ∀ {F G : (↥Qbar)[X]} {m n : ℕ}, F.natDegree ≤ m → G.natDegree ≤ n → (F * G).natDegree ≤ m + n :=
      fun hF hG => natDegree_mul_le.trans (add_le_add hF hG)
    have hP2' := le_of_max_le_left hdeg.le
    have hQ2' := le_of_max_le_right hdeg.le
    have hL : (C μ' * Q' - C κ * (C μ * Q)).natDegree ≤ 2 := natDegree_sub_le_of_le
      ((natDegree_C_mul_le _ _).trans hQ'2) ((natDegree_C_mul_le _ _).trans ((natDegree_C_mul_le _ _).trans hQ2'))
    have hB : (C κ * (P * A₂ + C b₁ * (Q * S₁) + C μ * (Q * S₂)) - Q' * (R₀ + S₂')).natDegree + 2 ≤ 4 + 2 := by
      have : (C κ * (P * A₂ + C b₁ * (Q * S₁) + C μ * (Q * S₂)) - Q' * (R₀ + S₂')).natDegree ≤ 2 + 2 :=
        natDegree_sub_le_of_le ((natDegree_C_mul_le _ _).trans (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (hm hP2' hA₂) ((natDegree_C_mul_le _ _).trans (hm hQ2' hS₁)))
        ((natDegree_C_mul_le _ _).trans (hm hQ2' hS₂))))
        (hm hQ'2 (natDegree_add_le_of_degree_le hR₀ hS₂'))
      omega
    have hF : P.natDegree = 2 ∨ (Q * S₁).natDegree = 4 := by
      by_cases h2 : P.natDegree = 2
      · exact Or.inl h2
      right
      have hS2 : S₁.natDegree = 2 :=
        le_antisymm hS₁ (le_natDegree_of_ne_zero (hP2.resolve_left (by
          rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact not_not.2 rfl)))
      rw [natDegree_mul hQ0 hS₁0, hS2]; omega
    obtain ⟨L₀, hL₀, hL₀'⟩ := DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq P (Q * S₁) _ _ 4 2
      (hcop.mul_right hPS) (mul_ne_zero hQ0 hS₁0) hF hL hB hpoly
    have hc₀ : L₀ = C (L₀.coeff 0) := by
      rcases hL₀' with rfl | h
      · simp
      · exact eq_C_of_natDegree_le_zero (by omega)
    rw [hc₀] at hL₀
    have hQ'v : (μ' : ℂ) * aeval u Q' = κ * μ * aeval u Q + L₀.coeff 0 * aeval u P := by
      have := congrArg (aeval u) hL₀
      simp only [map_sub, map_mul, aeval_C, am] at this
      linear_combination this
    by_cases hμ : μ = 0
    · rw [hμ] at hQ'v
      refine (not_both hc' hd' e₁ (k₂ := μ'⁻¹ * L₀.coeff 0) (aeval_inj hu ?_)).elim
      simp only [map_mul, aeval_C, am]
      push_cast at hQ'v ⊢
      field_simp
      linear_combination hQ'v
    · refine ⟨κ, 0, L₀.coeff 0 / μ', κ * μ / μ', ?_, by rw [hP'κ]; simp, ?_⟩
      · rw [zero_mul, sub_zero]; exact mul_ne_zero hκ (div_ne_zero (mul_ne_zero hκ hμ) hμ')
      · push_cast
        field_simp
        linear_combination hQ'v
