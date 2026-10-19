-- Prove2me | solution 1 for CauchyRiemannIndex.nonzeroLoop_homotopic_const_of_three_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T18:14:12.14829+00:00
-- url     : https://prove2.me/submissions/e14a09d7-9088-40c4-bc28-521fe1705d4c

import Definitions.Def_CauchyRiemannIndex_Setting
import Theorems.Thm_CauchyRiemannIndex_simplyConnectedSpace_nonzero_of_three_le_card

namespace CauchyRiemannIndex

open Matrix

theorem nonzeroLoop_homotopic_const_of_three_le_card_aux {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (x₀ : ι → ℝ) (v : C(unitInterval, ι → ℝ)) (hv : ∀ t, v t ≠ 0)
    (h0 : v 0 = x₀) (h1 : v 1 = x₀) :
    ∃ H : C(unitInterval × unitInterval, ι → ℝ), (∀ t, H (0, t) = v t) ∧
      (∀ t, H (1, t) = x₀) ∧ (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = x₀) ∧ ∀ s, H (s, 1) = x₀ := by
  haveI := simplyConnectedSpace_nonzero_of_three_le_card hι
  have hx₀ : x₀ ≠ 0 := h0 ▸ hv 0
  let x : {y : ι → ℝ // y ≠ 0} := ⟨x₀, hx₀⟩
  let γ : Path x x :=
    { toFun := fun t => ⟨v t, hv t⟩
      continuous_toFun := v.continuous.subtype_mk hv
      source' := Subtype.ext h0
      target' := Subtype.ext h1 }
  obtain ⟨F⟩ := SimplyConnectedSpace.paths_homotopic γ (Path.refl x)
  refine ⟨⟨fun p => (F p).1, continuous_subtype_val.comp F.continuous⟩, fun t => ?_,
    fun t => ?_, fun p => (F p).2, fun s => ?_, fun s => ?_⟩
  · show (F (0, t)).1 = v t
    rw [F.apply_zero]; rfl
  · show (F (1, t)).1 = x₀
    rw [F.apply_one]; rfl
  · show (F (s, 0)).1 = x₀
    rw [F.source]
  · show (F (s, 1)).1 = x₀
    rw [F.target]

end CauchyRiemannIndex

open CauchyRiemannIndex

open Matrix

theorem solution {ι : Type*} [Fintype ι]
    (hι : 3 ≤ Fintype.card ι) (x₀ : ι → ℝ) (v : C(unitInterval, ι → ℝ)) (hv : ∀ t, v t ≠ 0)
    (h0 : v 0 = x₀) (h1 : v 1 = x₀) :
    ∃ H : C(unitInterval × unitInterval, ι → ℝ), (∀ t, H (0, t) = v t) ∧
      (∀ t, H (1, t) = x₀) ∧ (∀ p, H p ≠ 0) ∧ (∀ s, H (s, 0) = x₀) ∧ ∀ s, H (s, 1) = x₀ :=
  nonzeroLoop_homotopic_const_of_three_le_card_aux hι x₀ v hv h0 h1
