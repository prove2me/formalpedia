-- Prove2me | solution 1 for Formalism.L2.Th1.F.S2IsogenyPsi.isOpen_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:25:03.294832+00:00
-- url     : https://prove2.me/submissions/0da92519-b128-45bd-9ed1-169b887d6ba1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_MulStableIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_QuasiPeriodConstIsogeny
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open Formalism.L2.Th1.F.S2IsogenyPsi
namespace Formalism.L2.Th1.F.S2IsogenyPsi
theorem _root_.solution (L : PeriodPair) (α : ℂ) : IsOpen (dom L α) := by
  have h1 : IsClosed ((fun z => α * z) ⁻¹' (L.lattice : Set ℂ)) :=
    L.isClosed_lattice.preimage (continuous_const.mul continuous_id)
  exact h1.isOpen_compl
end Formalism.L2.Th1.F.S2IsogenyPsi
