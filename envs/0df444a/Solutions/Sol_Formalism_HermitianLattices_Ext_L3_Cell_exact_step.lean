-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Cell.exact_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:31:10.497391+00:00
-- url     : https://prove2.me/submissions/7c6ca495-0c4d-4cc8-becb-ca2aac7fa3c2

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}
namespace Formalism.HermitianLattices.Ext.L3.Cell
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {b x : V}
    (hd : h (x - b) (x - b) ≠ 0) :
    h (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b))
        (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) = h b b ∧
      (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) - x =
        -(((h (x - b) (x - b))⁻¹ * (h x x - h b b)) • (x - b)) := by
  set w := x - b with hw
  have hx : x = w + b := by rw [hw]; abel
  have e1 : star (h b w) = h w b := hs.eq b w
  have e2 : star (h w b) = h b w := hs.eq w b
  have e3 : star (h w w) = h w w := hs.eq w w
  set d := h w w with hdd
  constructor
  · simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, star_mul', star_add, star_inv₀, e1, e2, e3, ← hdd]
    field_simp
    ring
  · have e4 : h x x - h b b = d + (h b w + h w b) := by
      rw [hx]
      simp only [map_add, LinearMap.add_apply, ← hdd]
      ring
    rw [e4]
    have e5 : d⁻¹ * (d + (h b w + h w b)) = 1 + (h b w + h w b) * d⁻¹ := by
      field_simp
    rw [e5, add_smul, one_smul]
    conv_lhs => rw [hx]
    abel
end Formalism.HermitianLattices.Ext.L3.Cell
