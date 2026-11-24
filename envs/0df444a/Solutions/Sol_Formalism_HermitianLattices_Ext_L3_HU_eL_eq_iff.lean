-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.eL_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:10:30.118857+00:00
-- url     : https://prove2.me/submissions/ea155741-76a5-40bb-b49c-8c5bfbdf674d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMatrixOfIsom
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_crd_cmb
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_HU_quotLocF_mk__fd1bb1b492f4
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_eL_col
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_mk


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
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K)) :
    eL h𝔭 b k X = Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) ↔
      ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
        Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)) := by
  have key : ∀ i, (fun l => Ideal.Quotient.mk (extP K 𝔭 ^ k) (Y l i)) =
      qE b (extP K 𝔭 ^ k) ((quotLocF h𝔭 (spanO b) k).symm
        (Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i)))) := by
    intro i
    rw [← quotLocF_mk' h𝔭, LinearEquiv.symm_apply_apply, qE_mk, crd_cmb]
  constructor
  · intro h i
    have h1 := eL_col h𝔭 b k X i
    rw [h] at h1
    have h2 : (fun l => (Y.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) l i) =
        fun l => Ideal.Quotient.mk (extP K 𝔭 ^ k) (Y l i) := rfl
    rw [h2, key i] at h1
    exact ((quotLocF h𝔭 (spanO b) k).symm.injective ((qE b (extP K 𝔭 ^ k)).injective h1)).symm
  · intro h
    ext l i
    have h1 := eL_col h𝔭 b k X i
    rw [h i, ← key i] at h1
    exact congrFun h1 l
end Formalism.HermitianLattices.Ext.L3.HU
