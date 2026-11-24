-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:40:13.813353+00:00
-- url     : https://prove2.me/submissions/a6809232-c019-4dac-942a-d7fa2bba2178

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) (x : Qq) (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Wˣ), x = algebraMap W Qq u * (p : Qq) ^ n := by
  have := h.frac_alt
  have hp := p_ne h
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨i, u1, ha⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 h.p_unif
  obtain ⟨k, u2, hb'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 h.p_unif
  refine ⟨(i : ℤ) - k, u1 * u2⁻¹, ?_⟩
  have hu2 : algebraMap W Qq (u2 : W) * algebraMap W Qq ((u2⁻¹ : Wˣ) : W) = 1 := by
    rw [← map_mul]; simp
  have hu20 : algebraMap W Qq (u2 : W) ≠ 0 := left_ne_zero_of_mul_eq_one hu2
  rw [ha, hb', zpow_sub₀ hp, div_eq_iff (by
    rw [map_mul, map_pow, map_natCast]; exact mul_ne_zero hu20 (pow_ne_zero _ hp))]
  simp only [map_mul, map_pow, map_natCast, Units.val_mul, zpow_natCast]
  have hk : (p : Qq) ^ k ≠ 0 := pow_ne_zero _ hp
  calc algebraMap W Qq (u1 : W) * (p : Qq) ^ i
      = algebraMap W Qq (u1 : W) * (algebraMap W Qq (u2 : W) * algebraMap W Qq ((u2⁻¹ : Wˣ) : W)) *
          ((p : Qq) ^ i / (p : Qq) ^ k * (p : Qq) ^ k) := by
        rw [hu2, mul_one, div_mul_cancel₀ _ hk]
    _ = _ := by ring
end Formalism.MainNotions.G.Inhab
