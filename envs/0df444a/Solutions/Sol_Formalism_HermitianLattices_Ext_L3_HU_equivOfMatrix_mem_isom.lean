-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.equivOfMatrix_mem_isom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:42:38.567737+00:00
-- url     : https://prove2.me/submissions/15dd64b4-4fcf-4689-a291-ac31d4a82e4a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NeZeroOfNotMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EquivFunEquivOfMatrixSymm
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_form_repr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_equivFun_equivOfMatrix
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_form_mulVec


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
theorem _root_.solution (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) (G G' : Matrix κ κ K)
    (hG : G * G' = 1) (hU : Gᴴ * gramK h b * G = gramK h b) :
    equivOfMatrix b G G' hG ∈ Formalism.HermitianLatticesTheory.isom h := by
  intro x y
  rw [form_repr h b, form_repr h b x y, equivFun_equivOfMatrix, equivFun_equivOfMatrix, form_mulVec, hU]
end Formalism.HermitianLattices.Ext.L3.HU
