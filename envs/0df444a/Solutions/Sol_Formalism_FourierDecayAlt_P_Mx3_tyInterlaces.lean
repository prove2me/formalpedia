-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx3.tyInterlaces
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:49:07.48895+00:00
-- url     : https://prove2.me/submissions/67cf7a43-c418-4ab8-9fd4-423170155934

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx3
namespace Formalism.FourierDecayAlt.P.Mx3
theorem _root_.solution : TyInterlaces := by
  intro P hP π i hi
  have h := Finset.mem_Icc.1 hi
  have hg := hP.gap i hi
  rw [rho_eq P π i h]
  have hb : ((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) ≤ P.wid i := by
    have := (π ⟨i - 1, by omega⟩).2
    have e : i - 1 + 1 = i := by omega
    simp only [e] at this
    omega
  have hw : (P.wid i : ℝ) ≤ P.hi i - P.lo i := Nat.floor_le (by linarith)
  have hb' : (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) ≤ P.wid i := by exact_mod_cast hb
  have h0 : (0 : ℝ) ≤ (((π ⟨i - 1, by omega⟩ : Fin _) : ℕ) : ℝ) := Nat.cast_nonneg _
  have a1 : P.hi i ≤ P.u i - 1 / 2 := by unfold Par.hi; linarith [min_le_left (P.u i) (P.u' i)]
  have a2 : P.hi i ≤ P.u' i - 1 / 2 := by unfold Par.hi; linarith [min_le_right (P.u i) (P.u' i)]
  have a3 : P.u (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_left (P.u (i + 1)) (P.u' (i + 1))]
  have a4 : P.u' (i + 1) + 1 / 2 ≤ P.lo i := by unfold Par.lo; linarith [le_max_right (P.u (i + 1)) (P.u' (i + 1))]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩
end Formalism.FourierDecayAlt.P.Mx3
