-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LA.la_incl_R_of_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:14:47.321812+00:00
-- url     : https://prove2.me/submissions/70dee251-4ebd-40d8-a7c7-784fbc363579

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLA
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDlatLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_PadicValIntProdElevenMultiples
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointExactExponentStopHigh
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Theorems.Thm_Formalism_CohomologicalDescent_LA_la_map_weyl
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldlat_map_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_standardMonomialSpanDomain
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
theorem _root_.solution (R : Type) [CommRing R] [IsDomain R] (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ)
    (l e : ℕ) (hu : ∀ m : ℕ, ¬ l ∣ m → IsUnit (m : R)) (hZ : InclZ r n hn ν l e)
    (x : MvPolynomial (Fin r × Fin n) R) (hx : x ∈ dualWeyl R r n ν) :
    (l : R) ^ e • x ∈ weyl R r n hn ν := by
  obtain ⟨m, hm, h⟩ := hZ
  rw [standardMonomialSpanDomain R r n ν] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨K, sz, hsz, I, hshape, rfl⟩ := hg
    have h1 : bideterminant ℤ sz hsz I ∈ dualWeyl ℤ r n ν := hshape ▸ bidetMem ℤ r n K sz hsz I
    have h2 := la_map_weyl R hn ν _ (h _ h1)
    rw [MvPolynomial.smul_eq_C_mul, map_mul, map_C, ldlat_map_bidet, ← MvPolynomial.smul_eq_C_mul]
      at h2
    obtain ⟨u, hu'⟩ := hu m hm
    have h3 := Submodule.smul_mem _ (↑u⁻¹ : R) h2
    rw [smul_smul] at h3
    convert h3 using 2
    simp only [eq_intCast]
    push_cast
    rw [← hu', ← mul_assoc, Units.inv_mul, one_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
end Formalism.CohomologicalDescent.LA
