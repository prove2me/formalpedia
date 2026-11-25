-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh.pred_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:59:58.700292+00:00
-- url     : https://prove2.me/submissions/d5b0eac2-d388-4255-9338-490823989e8e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTSSPhaseA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
theorem _root_.solution (P : M.Par) (ρ' : M.Ty P) (h : height P ρ' ≠ 0) :
    ∃ l ∈ Icc 1 (P.k - 1), ∃ ρ, M.Up P l ρ ρ' := by
  obtain ⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h
    unfold height
    exact Finset.sum_eq_zero fun i _ => hall i
  refine ⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩
  · rw [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp only [hj, dif_neg, not_false_eq_true]
      rw [if_neg]
      · simp
      · intro h2
        apply hj
        ext
        omega
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
