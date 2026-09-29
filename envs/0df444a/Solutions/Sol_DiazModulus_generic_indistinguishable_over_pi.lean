-- Prove2me | solution 1 for DiazModulus.generic_indistinguishable_over_pi
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T05:05:42.708179+00:00
-- url     : https://prove2.me/submissions/5f024a50-3ba3-408c-992a-7e1481698163

import Mathlib
import Definitions.Def_Diaz_Closure
import Theorems.Thm_DiazModulus_circle_points_indistinguishable
import Theorems.Thm_DiazModulus_exists_noncandidate_transcendental_on_circle

open ComplexConjugate

namespace P14OverPi

/-- `ℚ(π)` is countable. -/
theorem countable_Qpi :
    Countable ↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) := by
  rw [← Cardinal.mk_le_aleph0_iff]
  refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
  exact sup_le (sup_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl

/-- Every element of `ℚ(π)` is real, i.e. fixed by complex conjugation. -/
theorem conj_eq_of_mem_Qpi {x : ℂ}
    (hx : x ∈ IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) : conj x = x := by
  have hx' : x ∈ Subfield.closure
      (Set.range (algebraMap ℚ ℂ) ∪ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) := hx
  have h : Set.EqOn (starRingEnd ℂ) (RingHom.id ℂ)
      (Set.range (algebraMap ℚ ℂ) ∪ ({((Real.pi : ℝ) : ℂ)} : Set ℂ)) := by
    rintro y (⟨q, rfl⟩ | hy)
    · simp
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      simp
  exact RingHom.eqOn_field_closure h hx'

/-- A field of numbers algebraic over `ℚ(π)` is countable. -/
theorem countable_K (K : Subfield ℂ)
    (hK : ∀ z : ℂ, z ∈ K ↔
      IsAlgebraic (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) z) :
    Countable ↥K := by
  have := countable_Qpi
  have h : (K : Set ℂ).Countable :=
    (Algebraic.countable (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) ℂ).mono
      (fun z hz => (hK z).mp hz)
  exact h.to_subtype

/-- The algebraic closure of `ℚ(π)` in `ℂ` is stable under complex conjugation: conjugation
fixes `ℚ(π)` pointwise, so a polynomial over `ℚ(π)` killing `z` also kills `conj z`. -/
theorem conj_mem (K : Subfield ℂ)
    (hK : ∀ z : ℂ, z ∈ K ↔
      IsAlgebraic (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) z) :
    ∀ z ∈ K, conj z ∈ K := by
  intro z hz
  let σ : ℂ →ₐ[↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))] ℂ :=
    { starRingEnd ℂ with
      commutes' := fun r => conj_eq_of_mem_Qpi r.2 }
  exact (hK _).mpr (((hK z).mp hz).algHom σ)

/-- A number algebraic over `ℚ` is algebraic over `ℚ(π)`. -/
theorem mem_of_isAlgebraic_rat (K : Subfield ℂ)
    (hK : ∀ z : ℂ, z ∈ K ↔
      IsAlgebraic (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) z)
    {x : ℂ} (hx : IsAlgebraic ℚ x) : x ∈ K :=
  (hK x).mpr (hx.tower_top _)

end P14OverPi

open P14OverPi in
theorem solution (K : Subfield ℂ)
    (hK : ∀ z : ℂ, z ∈ K ↔
      IsAlgebraic (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) z)
    {u : ℂ} (hu0 : u ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u)) (hgen : Transcendental (↥K) u) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥K) t ∧ t * conj t = u * conj u ∧
      Transcendental ℚ (Complex.exp t) ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t ∧
        (∀ z ∈ Diaz.hull K u, Φ (conj z) = conj (Φ z)) ∧
        (∀ z ∈ Diaz.hull K u, Φ z ∈ Diaz.hull K t) ∧
        ∀ (p q : ℕ) (N : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
          (∀ i j, N i j ∈ Diaz.hull K u) → (∀ i, w i ∈ K) → (∀ j, v j ∈ K) →
            ((∑ i, ∑ j, w i * N i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (N i j) * v j) = 0) := by
  have hKcount : Countable ↥K := countable_K K hK
  have hKc : ∀ z ∈ K, conj z ∈ K := conj_mem K hK
  have hρK : u * conj u ∈ K := mem_of_isAlgebraic_rat K hK hρ
  -- the radius: `u * conj u = normSq u > 0`
  have hpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
  obtain ⟨t, htc, htr, hexp⟩ :=
    DiazModulus.exists_noncandidate_transcendental_on_circle K hKcount hpos
  have hut : t * conj t = u * conj u := by
    rw [htc, Complex.mul_conj]
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact htr isAlgebraic_zero
  exact ⟨t, ht0, htr, hut, hexp,
    DiazModulus.circle_points_indistinguishable K hKc hρK hgen htr hut⟩

#print axioms solution
