-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.bO_eq_cmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:42:58.273967+00:00
-- url     : https://prove2.me/submissions/4073b531-af5d-4f0d-a521-eecae848f49c

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_coe_cmb_single
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_bO_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (b : Basis κ K V) (i : κ) : bO b i = cmb b (Pi.single i 1) := by
  apply Subtype.ext
  rw [bO_apply, coe_cmb_single]
end Formalism.HermitianLattices.Ext.L3.HU
