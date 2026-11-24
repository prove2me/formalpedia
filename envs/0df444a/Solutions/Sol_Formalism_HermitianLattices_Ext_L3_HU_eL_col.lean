-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.eL_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:00:46.186056+00:00
-- url     : https://prove2.me/submissions/ef3bc203-4452-42be-ba87-1a82437ac881

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_quotLocF_mk__fd1bb1b492f4
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_bO_eq_cmb
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_InP_conj
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_eM_mulVec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_bO


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
theorem _root_.solution {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (i : κ) :
    (fun l => eL h𝔭 b k X l i) = qE b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm
      (X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))))) := by
  have h1 := eM_mulVec b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm.conj X)
    (Submodule.Quotient.mk (bO b i))
  rw [qE_bO, mulVec_single_one, LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, bO_eq_cmb,
    quotLocF_mk'] at h1
  exact h1
end Formalism.HermitianLattices.Ext.L3.HU
