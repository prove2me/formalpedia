-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.diagonal_top_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:59:29.87642+00:00
-- url     : https://prove2.me/submissions/8687b9fa-8e15-45cf-be85-5b873c8aa1f9

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock
import Theorems.Thm_Formalism_FourierDecayAlt_P_TA1_isPt_PT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.TA Finset Filter Topology TA1
open scoped InnerProductSpace ComplexConjugate
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TA.DiagTop := by
  intro E _ _ H _ _ W D Sg Φ w hNZ hA2
  unfold Ssplit Diag
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.sum_eq_single t]
  · intro t' ht' hne
    unfold Nst
    refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
    have := hA2 (D.r + 1) 1 le_rfl (by omega) le_rfl h h' t t' (isPt_PT Sg hNZ _ h hh)
      (isPt_PT Sg hNZ _ h' hh') (hNZ _ _ t ht) (hNZ _ _ t' ht')
      (Or.inr ⟨rfl, rfl, fun e => hne e.symm⟩)
    simp [offK, this]
  · intro h; exact absurd ht h
end Formalism.FourierDecayAlt.P
