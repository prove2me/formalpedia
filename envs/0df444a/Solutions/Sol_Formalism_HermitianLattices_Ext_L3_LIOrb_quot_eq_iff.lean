-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.quot_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:02:24.226334+00:00
-- url     : https://prove2.me/submissions/d782312d-f5c0-4967-be2f-184bcd2fffbc

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_mem_stabB
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_Dv_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {A : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {J : ℕ} {x : V}
    {D : Subgroup (V ≃ₗ[K] V)} (hD : D ≤ autSub h A) (a b : ↥D) :
    (QuotientGroup.mk a : ↥D ⧸ (stabB h A 𝔭 J x).subgroupOf D) = QuotientGroup.mk b ↔
      (b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x ∈ ((extP K 𝔭) ^ J • A : Submodule (𝓞 K) V) := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, mem_stabB]
  have ha := hD a.2
  have hb := hD b.2
  have e1 : ((a⁻¹ * b : ↥D) : V ≃ₗ[K] V) x - x =
      (a : V ≃ₗ[K] V)⁻¹ ((b : V ≃ₗ[K] V) x - (a : V ≃ₗ[K] V) x) := by
    rw [map_sub, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, inv_mul_cancel,
      DA.one_app]
    rfl
  constructor
  · rintro ⟨-, h2⟩
    rw [e1] at h2
    have := DA.apply_mem_smul ha.2 _ h2
    rwa [← LinearEquiv.mul_apply, mul_inv_cancel, DA.one_app] at this
  · intro h2
    refine ⟨hD (a⁻¹ * b).2, ?_⟩
    rw [e1]
    exact DA.apply_mem_smul (inv_mem ha).2 _ h2
end Formalism.HermitianLattices.Ext.L3.LIOrb
