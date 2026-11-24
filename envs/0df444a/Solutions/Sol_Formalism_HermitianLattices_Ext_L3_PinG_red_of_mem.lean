-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:54.354161+00:00
-- url     : https://prove2.me/submissions/2c6ec625-b4fe-4b51-b9a0-cee47ce3b7c6

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_quotLocF_mk


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.PinG
theorem _root_.solution (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ)
    (w : ↥(locF 𝔭 (spanO b))) (hw : (w : V) ∈ spanO b) :
    red b h𝔭 k w = fun i => Ideal.Quotient.mk (extP K 𝔭 ^ k) (crd b ⟨w, hw⟩ i) := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk ⟨(w : V), hw⟩ := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k ⟨(w : V), hw⟩ w.2]
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk w)) = _
  rw [e, qE_mk]
end Formalism.HermitianLattices.Ext.L3.PinG
