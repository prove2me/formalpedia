-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.totalDegree_pderiv_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:47:27.566274+00:00
-- url     : https://prove2.me/submissions/d4fcec75-7c57-427d-a836-405c8d21b401

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
variable {F : Type} [Field F]
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution {E : Type} [CommRing E] {σ : Type} (p : MvPolynomial σ E) (i : σ)
    (h : MvPolynomial.pderiv i p ≠ 0) : (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  obtain ⟨m, hm⟩ := Finset.nonempty_of_ne_empty (mt MvPolynomial.support_eq_empty.mp h)
  have key : ∀ m ∈ (MvPolynomial.pderiv i p).support, (m.sum fun _ e => e) + 1 ≤ p.totalDegree := by
    intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_pderiv] at hm
    have hs : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hm)
    have hle := MvPolynomial.le_totalDegree hs
    rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at hle
  have h1 := key m hm
  have h2 : (MvPolynomial.pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    apply Finset.sup_le
    intro s hs
    have := key s hs
    omega
  omega
end Formalism.L2.Pj.GenericSectionMinimum
