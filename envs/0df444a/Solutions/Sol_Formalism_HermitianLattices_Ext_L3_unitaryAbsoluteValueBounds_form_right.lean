-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.form_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:31:23.989594+00:00
-- url     : https://prove2.me/submissions/303ba297-6792-4d04-8816-ac06bc586b7c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_coe_lin
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
    (hzg : ∀ i, h (z i : V) (z i : V) = algebraMap (𝓞 K) K (g i)) (j : Fin m) (c : Fin m → 𝓞 K) :
    h (z j : V) (lin z c : V) = algebraMap (𝓞 K) K (c j * g j) := by
  rw [coe_lin, map_sum, Finset.sum_eq_single j]
  · rw [← algebraMap_smul K (c j) (z j : V), map_smul, hzg, smul_eq_mul, map_mul]
  · intro i _ hij
    rw [← algebraMap_smul K (c i) (z i : V), map_smul, hzo j i (Ne.symm hij), smul_zero]
  · simp
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
