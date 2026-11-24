-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_smul_monLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:16:11.339367+00:00
-- url     : https://prove2.me/submissions/a9bb86a2-7365-493a-87a0-b0115c121046

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mem_of_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {n : ℕ} (s : Fin n) (d N : ℕ) (hN : ∀ i ≤ d, d.choose i ∣ N)
    (y : MvPolynomial (Fin 2 × Fin n) ℤ) (hy : y ∈ la_monLat ℤ s d) :
    ((N : ℕ) : ℤ) • y ∈ la_binLat ℤ s d := by
  rw [la_monLat] at hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    rw [zsmul_eq_mul, Int.cast_natCast]
    exact la_mem_of_dvd ℤ s hpq (by rw [hpq]; exact hN q (by omega))
  | zero =>
    rw [smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx
end Formalism.CohomologicalDescent.LA
