-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums.mem_lat_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:24:59.065075+00:00
-- url     : https://prove2.me/submissions/7ef7b9c1-6a96-4f57-8e5d-9f1cad70376f

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
theorem _root_.solution {n : ℕ} {e : Fin n → V} (x : V) :
    x ∈ Submodule.span (𝓞 K) (Set.range e) ↔
      ∃ c : Fin n → 𝓞 K, ∑ i, algebraMap (𝓞 K) K (c i) • e i = x := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [algebraMap_smul]
end Formalism.HermitianLattices.Ext.L3.StandardSymmetricSums
