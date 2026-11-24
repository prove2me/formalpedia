-- Prove2me | solution 1 for GenFrameSpan.sfe_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:22.195883+00:00
-- url     : https://prove2.me/submissions/6d389248-fdf8-4f4e-b297-ed54e9cbfb13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply

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
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N0 N1 l : ℕ} [Fact l.Prime]
namespace GenFrameSpan
theorem _root_.solution (α : Lt × ℕ × Fin N0 →₀ ℕ) (β : Lt × Fin N0 × Fin N1 →₀ ℕ) :
    Finsupp.sumFinsuppEquivProdFinsupp
      (α.mapDomain (Sum.inl : _ → XZ Lt N0 N1) + β.mapDomain Sum.inr) = (α, β) := by
  ext x
  · rw [Finsupp.fst_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_of_notMem_range] <;> simp
  · rw [Finsupp.snd_sumFinsuppEquivProdFinsupp, Finsupp.add_apply,
      Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_of_notMem_range] <;> simp
end GenFrameSpan
