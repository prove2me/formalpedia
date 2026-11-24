-- Prove2me | solution 1 for Formalism.QuantumDeterminants.formal_degree_weyl_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:39.631821+00:00
-- url     : https://prove2.me/submissions/f92c3a13-bf1e-49be-baa0-c5c9224e5511

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
theorem _root_.solution : FdegWeyl := by
  intro n m hm
  unfold fdegHC
  simp_rw [Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  have hab := (Finset.mem_filter.mp hb).2
  have h2 := fin_sub_pos hab
  have h3 : (m b : ℝ) ≤ m a := by exact_mod_cast hm hab.le
  have e : (m a : ℝ) + Formalism.QuantumDeterminants.rhoStd n a - ((m b : ℝ) + Formalism.QuantumDeterminants.rhoStd n b) =
      (m a : ℝ) - m b + (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; ring
  show |(m a : ℝ) + Formalism.QuantumDeterminants.rhoStd n a - ((m b : ℝ) + Formalism.QuantumDeterminants.rhoStd n b)| = _
  rw [e, abs_of_pos (by linarith)]
end Formalism.QuantumDeterminants
