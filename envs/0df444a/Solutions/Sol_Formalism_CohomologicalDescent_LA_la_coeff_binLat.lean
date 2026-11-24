-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_coeff_binLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:38.665061+00:00
-- url     : https://prove2.me/submissions/d0bb8f0e-b5c3-441e-8f19-15708440d901

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_xy_eq
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_mono_inj
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LA
theorem _root_.solution {n : ℕ} (s : Fin n) (d : ℕ) (f : MvPolynomial (Fin 2 × Fin n) ℤ)
    (hf : f ∈ la_binLat ℤ s d) (p q : ℕ) :
    ((p + q).choose q : ℤ) ∣ coeff (la_mono s p q) f := by
  rw [la_binLat] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p', q', hpq, rfl⟩ := hx
    rw [la_xy_eq, ← nsmul_eq_mul, coeff_smul, coeff_monomial]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := la_mono_inj s h
      simp
    · simp
  | zero => simp
  | add x y _ _ hx hy =>
    rw [coeff_add]
    exact dvd_add hx hy
  | smul a x _ hx =>
    rw [coeff_smul, smul_eq_mul]
    exact Dvd.dvd.mul_left hx a
end Formalism.CohomologicalDescent.LA
