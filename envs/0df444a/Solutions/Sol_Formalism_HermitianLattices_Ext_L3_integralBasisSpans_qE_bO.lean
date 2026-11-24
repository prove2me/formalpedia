-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.integralBasisSpans.qE_bO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:09.997838+00:00
-- url     : https://prove2.me/submissions/4ffe71c4-1ab8-4835-9a9e-ac2413e8e655

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_qE_mk
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.integralBasisSpans
open LocalSpans idealPowerSpanBounds localizedQuotients
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]
namespace Formalism.HermitianLattices.Ext.L3.integralBasisSpans
theorem _root_.solution (b : Basis κ K V) (J : Ideal (𝓞 K)) (i : κ) :
    qE b J (Submodule.Quotient.mk (bO b i)) = Pi.single i 1 := by
  rw [qE_mk]
  funext l
  rw [crd, Basis.equivFun_self]
  by_cases hl : i = l
  · subst hl; simp
  · rw [if_neg hl, map_zero, Pi.single_eq_of_ne (Ne.symm hl)]
end Formalism.HermitianLattices.Ext.L3.integralBasisSpans
