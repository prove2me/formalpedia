-- Prove2me | solution 1 for GenFrameSpan.Lj_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:11.356441+00:00
-- url     : https://prove2.me/submissions/0518e915-b2f4-4678-822b-f6c476d2734d

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
theorem _root_.solution (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]) (μ : XZ Lt N0 N1 →₀ ℕ)
    (c : ℤ) : Lj Th (monomial μ c) = c • atMon Th μ := by
  have h : (monomial μ c : MvPolynomial (XZ Lt N0 N1) ℤ) = c • basisMonomials (XZ Lt N0 N1) ℤ μ := by
    rw [basisMonomials_apply', smul_monomial, smul_eq_mul, mul_one]
  rw [h, map_smul, Lj, Module.Basis.constr_basis]
end GenFrameSpan
