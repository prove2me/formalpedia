-- Prove2me | solution 1 for GenFrameSpan.prodD_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:27.327518+00:00
-- url     : https://prove2.me/submissions/d1e515ae-f80e-4020-be93-be3b330f0b65

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_NablaSpanC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_BasisMonomialsApply
import Theorems.Thm_GenFrameSpan_nablaX_eq
import Theorems.Thm_GenFrameSpan_det_submatrix_fun


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
theorem _root_.solution (nu : Lt → YoungDiagram)
    (F : ∀ s (c : Fin ((nu s).rowLen 0)), Fin ((nu s).colLen c) → Fin N0) :
    map (Int.castRingHom ℂ_[l]) (∏ s, ∏ c, Dm s _ (F s c)) ∈ nablaSpanC Lt l N0 nu := by
  by_cases h : ∀ s (c : Fin ((nu s).rowLen 0)), ∃ (J : Fin ((nu s).colLen c) ↪o Fin N0) (e : ℤ),
      Dm s _ (F s c) = (e : MvPolynomial (Lt × ℕ × Fin N0) ℤ) * Dm s _ J
  · choose Jf ef hJ using h
    have hp : ∏ s, ∏ c, Dm s _ (F s c) =
        ((∏ s, ∏ c, ef s c : ℤ) : MvPolynomial (Lt × ℕ × Fin N0) ℤ) *
          nablaX N0 nu (Jf : ColChoice N0 nu) := by
      have hn : nablaX N0 nu Jf = ∏ s, ∏ c, Dm s _ (Jf s c) := nablaX_eq nu Jf
      rw [hn]
      simp_rw [hJ, Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hp, map_mul, map_intCast, ← zsmul_eq_mul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun J : ColChoice N0 nu =>
      MvPolynomial.map (Int.castRingHom ℂ_[l]) (nablaX N0 nu J)) Jf)) _
  · push Not at h
    obtain ⟨s, c, hsc⟩ := h
    have h0 : Dm s _ (F s c) = 0 := by
      rcases det_submatrix_fun (Xm (N0 := N0) s _) (F s c) with h0 | ⟨J, e, he⟩
      · exact h0
      · exact absurd he (hsc J e)
    rw [Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero (Finset.mem_univ c) h0),
      map_zero]
    exact Submodule.zero_mem _
end GenFrameSpan
