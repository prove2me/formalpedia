-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_pos_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:26.08386+00:00
-- url     : https://prove2.me/submissions/714f0858-340b-41b2-b4cc-3fadde382603

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSFdeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.QuantumDeterminants
open Formalism.REAL
private lemma fin_sub_pos {n : ℕ} {a b : Fin n} (h : a < b) :
    0 < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) :=
  sub_pos.mpr (Nat.cast_lt.mpr h)
end Formalism.QuantumDeterminants
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : FdegPos := by
  intro n lam hl
  unfold fdegHC
  apply div_pos
  · refine Finset.prod_pos fun a _ => Finset.prod_pos fun b hb => ?_
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hl h))
  · exact Finset.prod_pos fun a _ => Finset.prod_pos fun b hb =>
      fin_sub_pos (Finset.mem_filter.mp hb).2
end Formalism.QuantumDeterminants
