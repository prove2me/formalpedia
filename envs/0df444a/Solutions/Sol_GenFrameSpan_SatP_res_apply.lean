-- Prove2me | solution 1 for GenFrameSpan.SatP.res_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:12.627504+00:00
-- url     : https://prove2.me/submissions/f8e36427-75ad-4ddd-ae59-081c3fb5d17e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_SatProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open GenFrameSpan
open CutKW MvPolynomial
open GenFrameSpan.SatP
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 : ℕ}
namespace GenFrameSpan.SatP
theorem _root_.solution (s : Lt) (m : Lt × ℕ × Fin N0 →₀ ℕ) (p : ℕ × Fin N0) :
    res s m p = m (emb s p) :=
  Finsupp.comapDomain_apply _ _ _ _
end GenFrameSpan.SatP
