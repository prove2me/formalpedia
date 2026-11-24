-- Prove2me | solution 1 for GenFrameSpan.Sj_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:51:13.936025+00:00
-- url     : https://prove2.me/submissions/48c2a26d-a448-4728-bb97-25460e2917d1

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_P2M_GenFrameSpan_basisMonomials_apply__3e1a67869174

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
theorem _root_.solution (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l])
    (β : Lt × Fin N0 × Fin N1 →₀ ℕ) (c : ℤ) :
    Sj Th (monomial β c) = c • ((β.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff β Th) := by
  have h : (monomial β c : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) =
      c • basisMonomials (Lt × Fin N0 × Fin N1) ℤ β := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Sj, Module.Basis.constr_basis]
end GenFrameSpan
