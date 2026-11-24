-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.form_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:42:43.976272+00:00
-- url     : https://prove2.me/submissions/0f2c80ee-eab5-41e7-970a-f72bd5c3f295

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_coe_lin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_form_right
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)
variable {z g}
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hzo : ∀ i j, i ≠ j → h (z i : V) (z j : V) = 0)
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (c : Fin m → 𝓞 K) :
    h (lin z c : V) (lin z c : V) = algebraMap (𝓞 K) K (∑ i, conjO K (c i) * c i * g i) := by
  nth_rewrite 1 [coe_lin]
  rw [map_sum, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← algebraMap_smul K (c i) (z i : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
    form_right hzo hzg, smul_eq_mul, map_mul, map_mul, map_mul, ← mul_assoc]
  congr 2 <;> simp [conjO]
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
