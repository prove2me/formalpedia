-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.stepNo2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:11.625527+00:00
-- url     : https://prove2.me/submissions/c9d37ef5-3f4e-4c76-92dd-e0611b013c2c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_lead_biadd
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_zero_of_biadd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
private theorem memIo_lemma {σ : Type} (n : ℕ) (p : MvPolynomial σ S) :
    p ∈ Io S σ ^ n ↔ ∀ x ∈ p.support, n ≤ Finsupp.degree x :=
  mem_pow_idealOfVars_iff n p
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) (hj2 : j ≠ 2)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (j + 1) := by
  obtain ⟨hA, hs⟩ := lead_biadd hj1 hjm fF hF hph1 hsym hP
  have h0 := zero_of_biadd (homogeneousComponent_isHomogeneous j (P - 1)) hj2 hA hs
  rw [memIo_lemma] at hP ⊢
  intro x hx
  have hle := hP x hx
  rcases Nat.lt_or_ge j (Finsupp.degree x) with hlt | hge
  · omega
  · exfalso
    have hxj : Finsupp.degree x = j := le_antisymm hge hle
    have hcx := congrArg (coeff x) h0
    rw [coeff_homogeneousComponent, if_pos hxj, coeff_zero] at hcx
    exact (MvPolynomial.mem_support_iff.1 hx) hcx
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
