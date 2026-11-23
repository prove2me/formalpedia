-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.nrmDown_key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:48.560829+00:00
-- url     : https://prove2.me/submissions/afeac9c5-0401-49a4-9f34-1720eb5c6f21

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_bot
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrmFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_bot
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_nrmFacts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (π : Ty P) :
    NrmDown P l π * ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) =
      -I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) := by
  have hl' := Finset.mem_Icc.1 hl
  by_cases h : ∃ π', Up P l π' π
  · obtain ⟨π', hU⟩ := h
    have hp := (Mx3.nrmFacts P hP l hl π').1 π hU
    have hpos : 0 < NrmDown P l π := by rw [hp.2]; exact hp.1
    have hD : ((∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l + 1)) *
      ∏ j ∈ (Icc 1 (P.k - 1)).erase l, (rho P π j - rho P π l)) ≠ 0 := by
      intro h0
      unfold NrmDown at hpos
      rw [h0, div_zero] at hpos
      exact lt_irrefl _ hpos
    unfold NrmDown
    exact div_mul_cancel₀ _ hD
  · rw [(Mx3.nrmFacts P hP l hl π).2.2 h]
    have ht := Mx3.bot P l hl π h
    have h0 : I.qpoly P.k P.T P.T' P.u P.u' (-rho P π l) = 0 := by
      unfold I.qpoly
      have : ∏ i ∈ Icc 1 P.k, ((-rho P π l + 1 / 2 + P.u i) * (-rho P π l + 1 / 2 + P.u' i)) = 0 := by
        apply Finset.prod_eq_zero (i := l + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
        rw [ht]; unfold Par.lo
        rcases max_choice (P.u (l + 1)) (P.u' (l + 1)) with h | h <;> rw [h] <;> ring
      rw [this]; simp
    rw [h0]; simp
end Formalism.FourierDecayAlt.P.Mx7
