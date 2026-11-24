-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.cmb_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:03.476239+00:00
-- url     : https://prove2.me/submissions/75fb29b5-d620-4617-95a4-aad3e3b13b0f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_crd_cmb
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
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]
end Formalism.HermitianLattices.Ext.L3.HU
