-- Prove2me | solution 1 for Formalism.L2.SG.Pf.GluingBases.bin_step_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:36.146177+00:00
-- url     : https://prove2.me/submissions/4d022145-7e59-4e4d-9d53-e9003c93bc80

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace Formalism.L2.SG.Pf.GluingBases
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (hz : ∀ x y, h x y = 0 → h y x = 0) (e₁ e₂ : V)
    (a b x y n : K) (h12 : h e₁ e₂ = 0) (h11 : h e₁ e₁ = a) (h22 : h e₂ e₂ = b) (ha : star a = a)
    (hb : star b = b) (hxy : a * (x * star x) + b * (y * star y) = n) :
    h (x • e₁ + y • e₂) (x • e₁ + y • e₂) = n ∧
      h (x • e₁ + y • e₂) ((star y * b) • e₁ - (star x * a) • e₂) = 0 ∧
      h ((star y * b) • e₁ - (star x * a) • e₂) ((star y * b) • e₁ - (star x * a) • e₂) =
        a * b * n := by
  have h21 : h e₂ e₁ = 0 := hz _ _ h12
  refine ⟨?_, ?_, ?_⟩
  · simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    linear_combination hxy
  · simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22]
    ring
  · simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, h12, h21, h11, h22, star_mul', star_star, ha, hb]
    linear_combination (a * b) * hxy
end Formalism.L2.SG.Pf.GluingBases
