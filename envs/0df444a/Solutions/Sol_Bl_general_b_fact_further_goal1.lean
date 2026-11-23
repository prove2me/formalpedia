-- Prove2me | solution 1 for Bl.general_b_fact_further.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:00.208534+00:00
-- url     : https://prove2.me/submissions/475d20b4-af62-46b0-871c-6f8b0b6b96fc

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactFurther_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_further
namespace Bl.general_b_fact_further
theorem _root_.solution :
  ∀ {V : Type} [inst : CommRing.{0} V] [inst_1 : IsDomain.{0} V] [IsDiscreteValuationRing.{0} V] {ϖ : V},
  Irreducible.{0} ϖ → IsLocalization.Away.{0, 0} ϖ (FractionRing.{0} V) := by
  intro V _ _ _ ϖ hϖ
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective V _
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ hinj).mpr (pow_ne_zero n hϖ.ne_zero))
  · intro z
    obtain ⟨⟨x, y, hy⟩, h⟩ := IsLocalization.surj (nonZeroDivisors V) z
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
    refine ⟨⟨x * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    simp only at h ⊢
    rw [map_mul] at h
    rw [map_mul, ← h]
    have hu : algebraMap V (FractionRing V) (↑u : V) * algebraMap V (FractionRing V) (↑u⁻¹ : V) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc z * algebraMap V (FractionRing V) (ϖ ^ n)
        = z * (algebraMap V (FractionRing V) (↑u : V) * algebraMap V (FractionRing V) (↑u⁻¹ : V))
            * algebraMap V (FractionRing V) (ϖ ^ n) := by rw [hu, mul_one]
      _ = _ := by ring
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩
end Bl.general_b_fact_further
