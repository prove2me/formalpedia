-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_OutsideDomination
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:22.961917+00:00
-- url     : https://prove2.me/submissions/69f7214f-b6ed-4786-a300-d5105e143497

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : OutsideDomination := by
  classical
  intro hPD E α P _ _ k L t F hk hd
  have := hPD α P F k (fun p _ _ => if t ∈ L p then (1 : ℂ) else 0) hk hd
  refine psd_congr (fun x _ y _ => ?_) this
  congr 1
  by_cases h : t ∈ ⨅ p, L p
  · rw [if_pos h]
    have h' : ∀ p, t ∈ L p := AddSubgroup.mem_iInf.1 h
    exact Finset.prod_eq_one fun p _ => if_pos (h' p)
  · rw [if_neg h]
    have : ∃ p, t ∉ L p := by
      by_contra hc
      exact h (AddSubgroup.mem_iInf.2 fun p => by_contra fun hp => hc ⟨p, hp⟩)
    obtain ⟨p, hp⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ p) (if_neg hp)
end Formalism.FourierDecayAlt.P.Jx8
