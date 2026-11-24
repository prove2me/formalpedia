-- Prove2me | solution 1 for Formalism.HN.DualPolygon.dual_inf_ann_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:20.869913+00:00
-- url     : https://prove2.me/submissions/687fdc34-b4cc-4011-a86e-d07c5b550e9f

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_misc_mem_dual_one
import Theorems.Thm_Formalism_HN_DualPolygon_misc_diff_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open nonZeroDivisors
namespace Formalism.HN.DualPolygon
theorem _root_.solution (A N : Submodule (𝓞 K) V) :
    dualLat A ⊓ annO N = (differentIdeal ℤ (𝓞 K)) • (tdualLat A ⊓ annO N) := by
  set D1 := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
  set 𝔡 := differentIdeal ℤ (𝓞 K)
  apply le_antisymm
  · rintro f ⟨hfA, hfN⟩

    have key : ∀ t ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K),
        t • f ∈ 𝔡 • (tdualLat A ⊓ annO N) := by
      intro t ht
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro r hr η hη
        obtain ⟨r₀, hr₀, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hr
        have hηf : η • f ∈ tdualLat A ⊓ annO N := by
          refine ⟨?_, ?_⟩
          · intro x hx
            obtain ⟨s, hs⟩ := hfA x hx
            have hη' := (misc_mem_dual_one η).1 hη s
            obtain ⟨z, hz⟩ := hη'
            refine ⟨z, ?_⟩
            simp only [LinearMap.smul_apply, smul_eq_mul]
            rw [← hs]
            exact hz
          · intro x hx
            simp [hfN x hx]
        have : (algebraMap (𝓞 K) K r₀ * η) • f = r₀ • (η • f) := by
          rw [mul_smul, algebraMap_smul]
        rw [this]
        exact Submodule.smul_mem_smul hr₀ hηf
      · intro t₁ t₂ h₁ h₂
        rw [add_smul]
        exact add_mem h₁ h₂
    have h1 : (1 : K) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K) * D1 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [misc_diff_mul]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩
    simpa using key 1 h1
  · rw [Submodule.smul_le]
    rintro r hr g ⟨hgA, hgN⟩
    refine ⟨?_, (annO N).smul_mem r hgN⟩
    intro x hx
    have hgx : g x ∈ D1 := by
      rw [misc_mem_dual_one]
      intro s
      obtain ⟨z, hz⟩ := hgA (s • x) (A.smul_mem s hx)
      refine ⟨z, ?_⟩
      rw [← hz, ← algebraMap_smul K s x, map_smul, smul_eq_mul, mul_comm]
    have hr' : (algebraMap (𝓞 K) K r) ∈ ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩
    have hm := FractionalIdeal.mul_mem_mul hr' hgx
    rw [misc_diff_mul] at hm
    obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).1 hm
    refine ⟨s, ?_⟩
    rw [hs, LinearMap.smul_apply, ← algebraMap_smul K r (g x), smul_eq_mul]
end Formalism.HN.DualPolygon
