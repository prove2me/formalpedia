-- Prove2me | solution 1 for Formalism.MainNotions.G.Inhab.le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:44:47.673749+00:00
-- url     : https://prove2.me/submissions/d3fb52c0-7f9c-4ecc-9eba-dd906f6d1e82

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}
namespace Formalism.MainNotions.G.Inhab
theorem _root_.solution (h : HidaSetting p n' W Qq O Kf ι σ j w) {a b : ℤ}
    (hm : (fun _ : Fin 1 => (p : Qq) ^ a) ∈ line W (Qq := Qq) p b) : b ≤ a := by
  have := h.frac_alt
  have hp := p_ne h
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hm
  have hc0 : algebraMap W Qq c * (p : Qq) ^ b = (p : Qq) ^ a := by
    have := congrFun hc 0
    rwa [Pi.smul_apply, Algebra.smul_def] at this
  obtain ⟨k, hk⟩ : ∃ k : ℕ, b = a + (k + 1 : ℕ) := ⟨(b - a - 1).toNat, by push_cast; omega⟩
  have h1 : algebraMap W Qq (c * (p : W) ^ (k + 1)) = 1 := by
    rw [map_mul, map_pow, map_natCast]
    rw [hk, zpow_add₀ hp, zpow_natCast] at hc0
    have ha : (p : Qq) ^ a ≠ 0 := zpow_ne_zero _ hp
    apply mul_left_cancel₀ ha
    calc (p : Qq) ^ a * (algebraMap W Qq c * (p : Qq) ^ (k + 1))
        = algebraMap W Qq c * ((p : Qq) ^ a * (p : Qq) ^ (k + 1)) := by ring
      _ = (p : Qq) ^ a := hc0
      _ = (p : Qq) ^ a * 1 := (mul_one _).symm
  have h2 : c * (p : W) ^ (k + 1) = 1 := IsFractionRing.injective W Qq (by rw [h1, map_one])
  have h3 : IsUnit ((p : W) ^ (k + 1)) := IsUnit.of_mul_eq_one c (by rw [mul_comm]; exact h2)
  exact h.p_unif.not_isUnit ((isUnit_pow_iff (Nat.succ_ne_zero k)).1 h3)
end Formalism.MainNotions.G.Inhab
