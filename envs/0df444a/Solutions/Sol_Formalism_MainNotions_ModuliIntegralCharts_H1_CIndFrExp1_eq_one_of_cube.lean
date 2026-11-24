-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.eq_one_of_cube
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:12:45.299541+00:00
-- url     : https://prove2.me/submissions/ff45cac2-a7a0-4390-b4c1-f86ca9501305

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_stepNo2
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
theorem _root_.solution {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (h3 : P - 1 ∈ Io S (Fin 2 × Fin d) ^ 3) : P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by
  have key : ∀ k, 3 + k ≤ m + 1 → P - 1 ∈ Io S (Fin 2 × Fin d) ^ (3 + k) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using h3
    | succ k ih =>
      intro hk
      have h := stepNo2 (j := 3 + k) (by omega) (by omega) (by omega) fF hF hph1 hsym (ih (by omega))
      have e : 3 + (k + 1) = 3 + k + 1 := by omega
      rw [e]
      exact h
  by_cases hm : m + 1 ≤ 3
  · rw [memIo_lemma] at h3 ⊢
    intro x hx
    have := h3 x hx
    omega
  · have h := key (m + 1 - 3) (by omega)
    have e : 3 + (m + 1 - 3) = m + 1 := by omega
    rw [e] at h
    exact h
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
