-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx4.nrmFacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:41.93864+00:00
-- url     : https://prove2.me/submissions/21bd398c-b964-414d-905b-6564a94541ad

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrm_down
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx4
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P.Mx4
theorem _root_.solution : NrmFacts := by
  intro P hP l hl π
  have hl' := Finset.mem_Icc.1 hl
  refine ⟨fun π' hU => ⟨nrm_pos P hP l hl π π' hU, nrm_down P l hl π π' hU⟩, ?_, ?_⟩
  · intro h
    have ht := top P hP l hl π h
    unfold Nrm I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l - 1 + 1 / 2 + P.u i) * (-rho P π l - 1 + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l) (Finset.mem_Icc.2 ⟨hl'.1, by omega⟩)
      rw [ht]; unfold Par.hi
      rcases min_choice (P.u l) (P.u' l) with h | h <;> rw [h] <;> ring
    rw [this]; simp
  · intro h
    have ht := bot P l hl π h
    unfold NrmDown I.qpoly
    have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
      apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      rw [ht]; unfold Par.lo
      rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
    rw [this]; simp
end Formalism.FourierDecayAlt.P.Mx4
