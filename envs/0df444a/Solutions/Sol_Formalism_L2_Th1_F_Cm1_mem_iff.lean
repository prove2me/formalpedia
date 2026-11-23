-- Prove2me | solution 1 for Formalism.L2.Th1.F.Cm1.mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:18.047282+00:00
-- url     : https://prove2.me/submissions/ef3e4986-c2c4-408c-96bf-1cdd7aad0248

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_CMQuasiPeriodConst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_CmAlternatingForm

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
open Formalism.L2.Th1.F.Cm1
namespace Formalism.L2.Th1.F.Cm1
theorem _root_.solution (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (z : ℂ) :
    z ∈ (cmPair a b d ha hd).lattice ↔ ∃ x y : ℤ, (x : ℂ) * (a : ℂ) + (y : ℂ) * cmTheta b d = z := by
  exact PeriodPair.mem_lattice
end Formalism.L2.Th1.F.Cm1
