-- Prove2me | solution 1 for GenFrameSpan.Lj_inl_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:26.286536+00:00
-- url     : https://prove2.me/submissions/758bf03c-25e8-42e5-b7f9-519ebf27e241

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_Lj_monomial
import Theorems.Thm_GenFrameSpan_Sj_monomial
import Theorems.Thm_GenFrameSpan_sfe_inl_inr

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
    (a : MvPolynomial (Lt × ℕ × Fin N0) ℤ) (q : MvPolynomial (Lt × Fin N0 × Fin N1) ℤ) :
    Lj Th (rename (Sum.inl : _ → XZ Lt N0 N1) a * rename (Sum.inr : _ → XZ Lt N0 N1) q) =
      Sj Th q • map (Int.castRingHom ℂ_[l]) a := by
  induction a using MvPolynomial.induction_on' with
  | monomial α r =>
    induction q using MvPolynomial.induction_on' with
    | monomial β t =>
      rw [rename_monomial, rename_monomial, monomial_mul, Lj_monomial, Sj_monomial, map_monomial,
        atMon, sfe_inl_inr]
      simp only [smul_monomial, zsmul_eq_mul, smul_eq_mul, eq_intCast, Int.cast_mul]
      congr 1
      ring
    | add q1 q2 h1 h2 => rw [map_add, mul_add, map_add, h1, h2, map_add, add_smul]
  | add a1 a2 h1 h2 => rw [map_add, add_mul, map_add, h1, h2, map_add, smul_add]
end GenFrameSpan
