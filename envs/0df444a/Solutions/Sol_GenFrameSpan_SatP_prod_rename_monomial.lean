-- Prove2me | solution 1 for GenFrameSpan.SatP.prod_rename_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:11.352269+00:00
-- url     : https://prove2.me/submissions/48ab120c-6031-44ec-9a69-4b8157e50897

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
theorem _root_.solution (n : Lt → (ℕ × Fin N0 →₀ ℕ)) :
    ∏ s, rename (emb s) (monomial (n s) (1 : ℤ)) =
      monomial (∑ s, (n s).mapDomain (emb s)) 1 := by
  simp only [rename_monomial]
  rw [monomial_sum_one]
end GenFrameSpan.SatP
