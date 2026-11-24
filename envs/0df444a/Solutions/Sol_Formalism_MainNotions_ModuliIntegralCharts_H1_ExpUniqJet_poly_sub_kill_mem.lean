-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet.poly_sub_kill_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:46:51.960738+00:00
-- url     : https://prove2.me/submissions/5f30997b-7c20-4e0c-90a3-ff9774750c22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_SpanXLeKerAevalZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqJet

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
open MvPolynomial Formalism.L2.Pj
variable {R : Type} [CommRing R]
variable {n : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
theorem _root_.solution (i : Fin 2) (P : MvPolynomial (Fin 2 × Fin n) R) :
    P - aeval (killS i) P ∈ Ideal.span (Set.range fun j : Fin n => (X (i, j) : MvPolynomial (Fin 2 × Fin n) R)) := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  next p v hp =>
    rw [map_mul, aeval_X]
    have e : p * X v - aeval (killS i) p * killS i v =
        (p - aeval (killS i) p) * X v + aeval (killS i) p * (X v - killS i v) := by ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ ?_)
    rcases v with ⟨a, b⟩
    unfold killS
    split_ifs with hv
    · have ha : a = i := hv
      subst ha
      rw [sub_zero]
      exact Ideal.subset_span ⟨b, rfl⟩
    · rw [sub_self]
      exact Ideal.zero_mem _
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
