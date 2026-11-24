-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.form_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:57.725974+00:00
-- url     : https://prove2.me/submissions/c502c2c7-9c5e-41cf-a8ec-820b684032f6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassSt
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteDimensionalOfOrtho
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
namespace Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
theorem _root_.solution {h : V →ₗ⋆[K] V →ₗ[K] K} {n : ℕ} {e : Fin n → V}
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (i : Fin n) (d : Fin n → K) :
    h (e i) (∑ j, d j • e j) = d i := by
  simp [map_sum, he]
end Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
