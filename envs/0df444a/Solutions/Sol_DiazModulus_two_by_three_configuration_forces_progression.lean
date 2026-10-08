-- Prove2me | solution 1 for DiazModulus.two_by_three_configuration_forces_progression
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-05T08:18:41.484918+00:00
-- url     : https://prove2.me/submissions/f2a52f3e-637a-40c2-96fb-a42b83691dbd

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-!
# A `2 × 3` configuration in a space of dimension at most four is a geometric progression

Let `V` be a `Q̄`-subspace of `ℂ` of dimension at most `4`, and let `x₀, x₁` and `y₀, y₁, y₂` be
`Q̄`-free with every `xᵢ yⱼ ∈ V`. Then `V = span_Q̄ {b, b h, b h², b h³}` for some `b ≠ 0` and some
transcendental `h`.

**Proof.** Put `h = x₁ / x₀`, transcendental since `x₀, x₁` are free, and `B = x₀ · span {yⱼ}`, of
dimension `3`. Both `B` and `h B` lie in `V`, so `W = B ∩ h B` has dimension at least `2`.
Then `W` and `h⁻¹ W` are two planes in `B`, so they meet in some `c ≠ 0`. Writing `c = h b` with
`b ∈ B` gives `b, h b, h² b ∈ B` (`chain`) and `h³ b ∈ h B`. These four vectors lie in `V` and are
free because `h` is transcendental (`powers_li`), so they span `V`.
-/

namespace R4B_progression

open DiazModulus Module Polynomial

/-- `B` and `h B` in a space of dimension at most `4`, with `dim B = 3`: some `b ≠ 0` has
`b, h b, h² b ∈ B`. -/
theorem chain {K L : Type*} [Field K] [Field L] [Algebra K L] {V B : Submodule K L}
    [FiniteDimensional K V] [FiniteDimensional K B] (hV : finrank K V ≤ 4)
    (hB : finrank K B = 3) {h : L} (h0 : h ≠ 0) (hBV : B ≤ V)
    (hhBV : B.map (LinearMap.mulLeft K h) ≤ V) :
    ∃ b ∈ B, b ≠ 0 ∧ h * b ∈ B ∧ h * (h * b) ∈ B := by
  have hM : Function.Injective (LinearMap.mulLeft K h) := mul_right_injective₀ h0
  have hM' : Function.Injective (LinearMap.mulLeft K h⁻¹) :=
    mul_right_injective₀ (inv_ne_zero h0)
  have h3 : finrank K (B.map (LinearMap.mulLeft K h)) = 3 := by
    rw [← (Submodule.equivMapOfInjective _ hM B).finrank_eq, hB]
  have hW : 2 ≤ finrank K ↥(B ⊓ B.map (LinearMap.mulLeft K h)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq B (B.map (LinearMap.mulLeft K h))
    have h2 := (Submodule.finrank_mono (sup_le hBV hhBV)).trans hV
    omega
  set W := B ⊓ B.map (LinearMap.mulLeft K h)
  have hW' : 2 ≤ finrank K (W.map (LinearMap.mulLeft K h⁻¹)) := by
    rw [← (Submodule.equivMapOfInjective _ hM' W).finrank_eq]
    exact hW
  have hW'B : W.map (LinearMap.mulLeft K h⁻¹) ≤ B := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hz
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hc).2
    rwa [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, inv_mul_cancel_left₀ h0]
  have hpos : 1 ≤ finrank K ↥(W ⊓ W.map (LinearMap.mulLeft K h⁻¹)) := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W (W.map (LinearMap.mulLeft K h⁻¹))
    have h2 : finrank K ↥(W ⊔ W.map (LinearMap.mulLeft K h⁻¹)) ≤ finrank K B :=
      Submodule.finrank_mono (sup_le inf_le_left hW'B)
    omega
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.1 hpos)
  obtain ⟨hcW, w, hw, hwc⟩ := Submodule.mem_inf.1 hc
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hcW).2
  refine ⟨b, hb, ?_, (Submodule.mem_inf.1 hcW).1, ?_⟩
  · rintro rfl
    exact hc0 (map_zero _)
  · have : h * (h * b) = w := by
      simp only [LinearMap.mulLeft_apply] at hwc
      rw [← hwc, mul_inv_cancel_left₀ h0]
    rw [this]
    exact (Submodule.mem_inf.1 hw).1

/-- A transcendental `h` gives free vectors `b, b h, b h², b h³` for every `b ≠ 0`. -/
theorem powers_li {h b : ℂ} (hh : h ∉ Qbar) (hb : b ≠ 0) :
    LinearIndependent (↥Qbar) (fun k : Fin 4 => b * h ^ (k : ℕ)) := by
  have : Algebra.IsAlgebraic ℚ Qbar :=
    ⟨fun a => (isAlgebraic_algebraMap_iff Subtype.val_injective).mp (mem_Qbar_iff.mp a.2)⟩
  have hinj : Function.Injective (aeval h : (↥Qbar)[X] →ₐ[↥Qbar] ℂ) :=
    transcendental_iff_injective.1 ((Algebra.IsAlgebraic.transcendental_iff ℚ Qbar).1
      fun h' => hh (mem_Qbar_iff.2 h'))
  have h1 := (((basisMonomials (↥Qbar)).linearIndependent.map' (aeval h).toLinearMap
    (LinearMap.ker_eq_bot.2 hinj)).comp (Fin.val : Fin 4 → ℕ) Fin.val_injective).map'
    (LinearMap.mulLeft (↥Qbar) b) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hb))
  have e : (fun k : Fin 4 => b * h ^ (k : ℕ)) = (LinearMap.mulLeft (↥Qbar) b) ∘
      ((aeval h).toLinearMap ∘ basisMonomials (↥Qbar)) ∘ Fin.val := by
    funext k
    simp [coe_basisMonomials, aeval_monomial]
  rw [e]
  exact h1

end R4B_progression

open DiazModulus R4B_progression in
theorem solution (V : Submodule (↥Qbar) ℂ)
    [FiniteDimensional (↥Qbar) V] (hV : Module.finrank (↥Qbar) V ≤ 4)
    (x : Fin 2 → ℂ) (y : Fin 3 → ℂ) (hx : LinearIndependent (↥Qbar) x)
    (hy : LinearIndependent (↥Qbar) y) (hxy : ∀ i j, x i * y j ∈ V) :
    ∃ b h : ℂ, b ≠ 0 ∧ h ∉ Qbar ∧
      V = Submodule.span (↥Qbar) (Set.range fun k : Fin 4 => b * h ^ (k : ℕ)) := by
  have hx0 : x 0 ≠ 0 := hx.ne_zero 0
  obtain ⟨h, hx1⟩ : ∃ h : ℂ, h * x 0 = x 1 := ⟨x 1 / x 0, div_mul_cancel₀ _ hx0⟩
  have hh : h ∉ Qbar := by
    intro hq
    have := Fintype.linearIndependent_iff.1 hx ![⟨h, hq⟩, -1]
      (by simp [Fin.sum_univ_two, Subfield.smul_def, hx1])
    simpa using this 1
  have h0 : h ≠ 0 := fun h' => hh (h' ▸ Subfield.zero_mem _)
  have hli : LinearIndependent (↥Qbar) (fun j => x 0 * y j) :=
    hy.map' (LinearMap.mulLeft _ (x 0)) (LinearMap.ker_eq_bot.2 (mul_right_injective₀ hx0))
  have : FiniteDimensional (↥Qbar) (Submodule.span (↥Qbar) (Set.range fun j => x 0 * y j)) :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hBV : Submodule.span (↥Qbar) (Set.range fun j => x 0 * y j) ≤ V :=
    Submodule.span_le.2 (Set.range_subset_iff.2 fun j => hxy 0 j)
  have hhBV : (Submodule.span (↥Qbar) (Set.range fun j => x 0 * y j)).map
      (LinearMap.mulLeft (↥Qbar) h) ≤ V := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun j => ?_)
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply, ← mul_assoc, hx1]
    exact hxy 1 j
  obtain ⟨b, hb, hb0, hb1, hb2⟩ := chain hV
    (by rw [finrank_span_eq_card hli, Fintype.card_fin]) h0 hBV hhBV
  refine ⟨b, h, hb0, hh, (Submodule.eq_of_le_of_finrank_le ?_ ?_).symm⟩
  · have m0 : b * h ^ 0 ∈ V := by rw [pow_zero, mul_one]; exact hBV hb
    have m1 : b * h ^ 1 ∈ V := by rw [pow_one, mul_comm]; exact hBV hb1
    have m2 : b * h ^ 2 ∈ V := by
      rw [show b * h ^ 2 = h * (h * b) by ring]; exact hBV hb2
    have m3 : b * h ^ 3 ∈ V := by
      rw [show b * h ^ 3 = h * (h * (h * b)) by ring]
      exact hhBV (Submodule.mem_map_of_mem hb2)
    refine Submodule.span_le.2 (Set.range_subset_iff.2 fun k => SetLike.mem_coe.2 ?_)
    fin_cases k
    exacts [m0, m1, m2, m3]
  · rw [finrank_span_eq_card (powers_li hh hb0), Fintype.card_fin]
    exact hV

#print axioms solution
