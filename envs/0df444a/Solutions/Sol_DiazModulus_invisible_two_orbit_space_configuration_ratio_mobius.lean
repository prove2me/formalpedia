-- Prove2me | solution 1 for DiazModulus.invisible_two_orbit_space_configuration_ratio_mobius
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-01T09:28:01.995246+00:00
-- url     : https://prove2.me/submissions/3173f0ec-14c0-48b4-9d25-de7ee71a168c

import Mathlib
import Definitions.Def_DiazModulus
import Theorems.Thm_DiazModulus_invisible_two_orbit_space_u_multiplier_space_eq
import Theorems.Thm_DiazModulus_u_multiplier_space_le_span_no_degree_one_no_visible_element
import Theorems.Thm_DiazModulus_scalar_quadratic_space_visible_element_mem
import Theorems.Thm_DiazModulus_degree_two_configuration_pencil_normal_form
import Theorems.Thm_DiazModulus_configuration_ratio_quadratic_of_not_degree_one
import Theorems.Thm_DiazModulus_invisible_two_orbit_space_pole_pencil
import Theorems.Thm_DiazModulus_quadratic_space_mem_iff_numerator
import Theorems.Thm_DiazModulus_binary_quadratic_dvd_of_coprime_mul_eq
import Theorems.Thm_DiazModulus_coprime_pencil_mobius

open Complex ComplexConjugate

/-! # Q1.6, two-orbit case: every configuration ratio is a Möbius function of `P(u)/Q(u)`

Let `W = WA(P, Q, S₁, S₂)` be invisible. By `invisible_two_orbit_space_u_multiplier_space_eq`,
`dim W = 5`, `W ∩ u⁻¹W = span(1, u⁻¹)` and `W` has no degree-one configuration; by
`u_multiplier_space_le_span_no_degree_one_no_visible_element` it contains no `t_x`. Since `W ⊆ Q̄(u)`,
`configuration_ratio_quadratic_of_not_degree_one` writes `x₁/x₀ = p(u)/q(u)` with `(p, q)` coprime of
degree 2, and `degree_two_configuration_pencil_normal_form` gives a Möbius image `(P′, Q′)` of
`(p, q)` with three cases.
- Scalar: `scalar_quadratic_space_visible_element_mem` puts a `t_x` in `W`, impossible.
- `W = WA(P′, Q′, …)`: the generators `Q′S₁′/(uP′)` and `P′S₂′/(uQ′)` lie outside `H₀`
  (`dim W = 5`), so `invisible_two_orbit_space_pole_pencil` makes each of `P′`, `Q′` proportional to
  `P` or `Q`; they are not both proportional to the same one (coprime of degree 2).
- `W = WB(P′, Q′, …)`: the same node makes `P′ = κP` or `κQ`. Then `PS₂/(uQ)` (resp. `QS₁/(uP)`) lies
  in `WB(P′, …)`, and `quadratic_space_mem_iff_numerator` gives `κ²P³S₂ = Q·N` with `deg N ≤ 6`;
  `binary_quadratic_dvd_of_coprime_mul_eq` (`e = 0`, `d = 8`) forces `κ = 0`, a contradiction.
So `(P′, Q′)` is an invertible combination of `(P, Q)`, and so is `(p, q)`. -/

namespace R21b_Q6a

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

/-- The numerator of a `WB` member has degree at most 6. -/
theorem deg_six {P Q A S₁ S₂ : (↥Qbar)[X]} (hP : P.natDegree ≤ 2) (hQ : Q.natDegree ≤ 2) (hA : A.natDegree ≤ 2)
    (h₁ : S₁.natDegree ≤ 2) (h₂ : S₂.natDegree ≤ 2) (a₁ a₂ : ↥Qbar) :
    (P ^ 2 * A + C a₁ * (P * Q * S₁) + C a₂ * (Q * (Q * S₁ + P * S₂))).natDegree ≤ 6 := by
  have m : ∀ {F G : (↥Qbar)[X]} {m n : ℕ}, F.natDegree ≤ m → G.natDegree ≤ n → (F * G).natDegree ≤ m + n :=
    fun hF hG => natDegree_mul_le.trans (add_le_add hF hG)
  refine natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le ?_ ?_) ?_
  · exact m (natDegree_pow_le.trans (by omega)) hA
  · exact (natDegree_C_mul_le _ _).trans (m (m hP hQ) h₁)
  · exact (natDegree_C_mul_le _ _).trans (m hQ (natDegree_add_le_of_degree_le (m hQ h₁) (m hP h₂)))

/-- A `WB(P′, …)` with `P′ = κU` cannot contain `U S/(u T)` when `T` is coprime to `U S`. -/
theorem wb_contra {u : ℂ} (hu : u ∉ Qbar) {T U S P' Q' S₁' S₂' : (↥Qbar)[X]} {κ : ↥Qbar} (hκ : κ ≠ 0)
    (hTU : IsCoprime T U) (hdeg : max T.natDegree U.natDegree = 2) (hTS : IsCoprime T S)
    (hT2 : T.coeff 2 ≠ 0 ∨ S.coeff 2 ≠ 0) (hS : S.natDegree ≤ 2) (hP' : P' = C κ * U) (hQ'0 : Q' ≠ 0)
    (hQ'2 : Q'.natDegree ≤ 2) (hS₁' : S₁'.natDegree ≤ 2) (hS₂' : S₂'.natDegree ≤ 2)
    (hmem : aeval u U * aeval u S / (u * aeval u T) ∈ Submodule.span Qbar ({1, u, u⁻¹,
      aeval u Q' * aeval u S₁' / (u * aeval u P'),
      aeval u Q' * (aeval u Q' * aeval u S₁' + aeval u P' * aeval u S₂') / (u * aeval u P' ^ 2)} : Set ℂ)) : False := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hU0 : U ≠ 0 := q_ne_zero hTU hdeg
  have hT0 : T ≠ 0 := q_ne_zero hTU.symm (by rw [max_comm]; exact hdeg)
  have hS0 : S ≠ 0 := by
    rintro rfl
    have := natDegree_eq_zero_of_isUnit (isCoprime_zero_right.1 hTS)
    simp [coeff_eq_zero_of_natDegree_lt (show T.natDegree < 2 by omega)] at hT2
  have hP'0 : P' ≠ 0 := by rw [hP']; exact mul_ne_zero (C_ne_zero.2 hκ) hU0
  obtain ⟨A, a₁, a₂, hA, hN⟩ := ((DiazModulus.quadratic_space_mem_iff_numerator u hu P' Q' S₁' S₂' hP'0 hQ'0).2 _).1 hmem
  have hP'2 : P'.natDegree ≤ 2 := by rw [hP']; exact (natDegree_C_mul_le _ _).trans (le_of_max_le_right hdeg.le)
  have hTu := aeval_ne_zero hu hT0
  have hpoly : U ^ 3 * S * C (κ ^ 2) = T * (P' ^ 2 * A + C a₁ * (P' * Q' * S₁') + C a₂ * (Q' * (Q' * S₁' + P' * S₂'))) := by
    apply aeval_inj hu
    rw [map_mul (aeval u) T, ← hN, hP']
    simp only [map_mul, map_pow, aeval_C, am]
    field_simp
  have hF : (U ^ 3 * S).natDegree = 8 ∨ T.natDegree = 2 := by
    by_cases h2 : T.natDegree = 2
    · exact Or.inr h2
    have hU2 : U.natDegree = 2 := by omega
    have hS2 : S.natDegree = 2 :=
      le_antisymm hS (le_natDegree_of_ne_zero (hT2.resolve_left (by
        rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact not_not.2 rfl)))
    left
    rw [natDegree_mul (pow_ne_zero _ hU0) hS0, natDegree_pow, hU2, hS2]
  obtain ⟨L₀, hL₀, hL₀'⟩ := DiazModulus.binary_quadratic_dvd_of_coprime_mul_eq T (U ^ 3 * S) (C (κ ^ 2)) _ 8 0
    ((hTU.pow_right).mul_right hTS) (mul_ne_zero (pow_ne_zero _ hU0) hS0) hF.symm (by simp)
    (by have := deg_six hP'2 hQ'2 hA hS₁' hS₂' a₁ a₂; omega) hpoly
  rcases hL₀' with rfl | h
  · simp at hL₀; exact hκ hL₀
  · omega

end R21b_Q6a

open DiazModulus R21b_Q6a in
open Polynomial in
theorem solution (u : ℂ) (hu : u ∉ Qbar) (P Q S₁ S₂ : (↥Qbar)[X])
    (hcop : IsCoprime P Q) (hdeg : max P.natDegree Q.natDegree = 2) (hS₁ : S₁.natDegree ≤ 2) (hS₂ : S₂.natDegree ≤ 2)
    (hPS : IsCoprime P S₁) (hQS : IsCoprime Q S₂)
    (hP2 : P.coeff 2 ≠ 0 ∨ S₁.coeff 2 ≠ 0) (hQ2 : Q.coeff 2 ≠ 0 ∨ S₂.coeff 2 ≠ 0)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x) (hy : LinearIndependent (↥Qbar) y)
    (hxy : ∀ i j, x i * y j ∈ Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ)) :
    ∃ a b c d : ℂ, a ∈ Qbar ∧ b ∈ Qbar ∧ c ∈ Qbar ∧ d ∈ Qbar ∧ a * d - b * c ≠ 0 ∧
      x 1 * (c * aeval u P + d * aeval u Q) = x 0 * (a * aeval u P + b * aeval u Q) := by
  have hu0 : u ≠ 0 := fun h => hu (h ▸ Qbar.zero_mem)
  have hP0 : P ≠ 0 := q_ne_zero hcop.symm (by rw [max_comm]; exact hdeg)
  have hQ0 : Q ≠ 0 := q_ne_zero hcop hdeg
  obtain ⟨h5, hZ, hD1⟩ := DiazModulus.invisible_two_orbit_space_u_multiplier_space_eq u hu P Q S₁ S₂
    hcop hdeg hS₁ hS₂ hPS hQS hP2 hQ2
  set W := Submodule.span Qbar ({1, u, u⁻¹, aeval u Q * aeval u S₁ / (u * aeval u P),
    aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ) with hWdef
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
        aeval u P * aeval u S₂ / (u * aeval u Q)} : Set ℂ), t ∈ IntermediateField.adjoin Qbar ({u} : Set ℂ) := by
      intro t ht
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hu'
      · exact inv_mem hu'
      all_goals exact div_mem (mul_mem (hK _) (hK _)) (mul_mem hu' (hK _))
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
  have hmul : ∀ {k : ↥Qbar} {T : (↥Qbar)[X]}, T ≠ 0 → (C k * T = P' ∨ C k * T = Q') → k ≠ 0 := by
    rintro k T - h rfl
    rcases h with h | h <;> simp [← h] at hP'0 hQ'0
  rcases hcase with hsc | ⟨S₁', S₂', hS₁', hS₂', hW'⟩ | ⟨S₁', S₂', hS₁', hS₂', hW'⟩
  · exact (hPT (DiazModulus.scalar_quadratic_space_visible_element_mem u hu W h1 hu1 hui P' Q' hc' hd' hsc)).elim
  · -- `W = WA(P′, Q′, …)`
    have h5' := hW' ▸ h5
    have hg₁ : aeval u Q' * aeval u S₁' / (u * aeval u P') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    have hg₂ : aeval u P' * aeval u S₂' / (u * aeval u Q') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    have hg₂0 := not_mem_H0 (by rw [Set.pair_comm] at h5'; exact h5')
    obtain ⟨⟨k₁, e₁⟩, -⟩ | ⟨⟨k₁, e₁⟩, -⟩ := DiazModulus.invisible_two_orbit_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hQS hP2 hQ2 P' (Q' * S₁') hP'2 hP'0 (natDegree_mul_le.trans (by omega)) _ hg₁ (not_mem_H0 h5')
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hP'u), map_mul]) <;>
    obtain ⟨⟨k₂, e₂⟩, -⟩ | ⟨⟨k₂, e₂⟩, -⟩ := DiazModulus.invisible_two_orbit_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hQS hP2 hQ2 Q' (P' * S₂') hQ'2 hQ'0 (natDegree_mul_le.trans (by omega)) _ hg₂ hg₂0
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hQ'u), map_mul])
    · exact (not_both hc' hd' e₁ e₂).elim
    · exact ⟨k₁, 0, 0, k₂, by simpa using mul_ne_zero (hmul hP0 (.inl e₁.symm)) (hmul hQ0 (.inr e₂.symm)),
        by rw [e₁]; simp [am], by rw [e₂]; simp [am]⟩
    · exact ⟨0, k₁, k₂, 0, by simpa using mul_ne_zero (hmul hQ0 (.inl e₁.symm)) (hmul hP0 (.inr e₂.symm)),
        by rw [e₁]; simp [am], by rw [e₂]; simp [am]⟩
    · exact (not_both hc' hd' e₁ e₂).elim
  · -- `W = WB(P′, Q′, …)`: impossible
    have h5' := hW' ▸ h5
    have hg₁ : aeval u Q' * aeval u S₁' / (u * aeval u P') ∈ W := by rw [hW']; exact Submodule.subset_span (by simp)
    have hA₁ : aeval u Q * aeval u S₁ / (u * aeval u P) ∈ W := Submodule.subset_span (by simp)
    have hA₂ : aeval u P * aeval u S₂ / (u * aeval u Q) ∈ W := Submodule.subset_span (by simp)
    rw [hW'] at hA₁ hA₂
    obtain ⟨⟨k₁, e₁⟩, -⟩ | ⟨⟨k₁, e₁⟩, -⟩ := DiazModulus.invisible_two_orbit_space_pole_pencil u hu P Q S₁ S₂ hcop hdeg
      hS₁ hS₂ hPS hQS hP2 hQ2 P' (Q' * S₁') hP'2 hP'0 (natDegree_mul_le.trans (by omega)) _ hg₁ (not_mem_H0 h5')
      (by rw [div_mul_cancel₀ _ (mul_ne_zero hu0 hP'u), map_mul])
    · exact (wb_contra hu (hmul hP0 (.inl e₁.symm)) hcop.symm (by rw [max_comm]; exact hdeg) hQS hQ2 hS₂ e₁
        hQ'0 hQ'2 hS₁' hS₂' hA₂).elim
    · exact (wb_contra hu (hmul hQ0 (.inl e₁.symm)) hcop hdeg hPS hP2 hS₁ e₁ hQ'0 hQ'2 hS₁' hS₂' hA₁).elim
