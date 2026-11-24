-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.PinG.red_bM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.377735+00:00
-- url     : https://prove2.me/submissions/9d706cdc-bd3e-4e52-b767-6a69553d7b60

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_bO_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_bO
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
theorem _root_.solution (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (k : ℕ) (j : κ) :
    red b h𝔭 k (bM b 𝔭 j) = Pi.single j 1 := by
  have e : (quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j)) =
      Submodule.Quotient.mk (bO b j) := by
    rw [LinearEquiv.symm_apply_eq, quotLocF_mk h𝔭 (spanO b) k (bO b j)
      (by rw [bO_apply]; exact (bM b 𝔭 j).2)]
    congr 1
    apply Subtype.ext
    exact (bO_apply b j).symm
  show qE b _ ((quotLocF h𝔭 (spanO b) k).symm (Submodule.Quotient.mk (bM b 𝔭 j))) = _
  rw [e, qE_bO]
end Formalism.HermitianLattices.Ext.L3.PinG
