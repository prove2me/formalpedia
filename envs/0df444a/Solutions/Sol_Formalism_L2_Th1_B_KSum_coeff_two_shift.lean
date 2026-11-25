-- Prove2me | solution 1 for Formalism.L2.Th1.B.KSum.coeff_two_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:14:12.1558+00:00
-- url     : https://prove2.me/submissions/b2582a7a-7c81-4d3f-8ef5-429158ce4686

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_GoodModelLattice
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_CoeffTwoPSeries
import Theorems.Thm_Formalism_L2_Th1_F_HalfPeriodDerivative_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_PeriodLatticeBasisLemmas_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_WeierstrassZetaQuasiPeriod_isOpen_compl
import Theorems.Thm_Formalism_L2_Th1_F_pSecond


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.KSum
open Formalism.L2.Th1.F (MulStable IsKerReps taylor0 pSeries)
namespace Formalism.L2.Th1.B.KSum
theorem _root_.solution (L : PeriodPair) (P : ℂ) (hP : P ∉ L.lattice) :
    PowerSeries.coeff 2 (taylor0 (fun z => L.weierstrassP (z + P)))
      = 3 * L.weierstrassP P ^ 2 - L.g₂ / 4 := by
  unfold taylor0
  rw [PowerSeries.coeff_mk]
  have hc : IsClosed (L.lattice : Set ℂ) := by
    first
      | exact L.isClosed_lattice
      | exact PeriodPair.isClosed_lattice L
      | (haveI : DiscreteTopology L.lattice.toAddSubgroup := inferInstanceAs (DiscreteTopology L.lattice)
         exact AddSubgroup.isClosed_of_discrete (H := L.lattice.toAddSubgroup))
  have hopen : ∀ᶠ w in nhds P, w ∉ L.lattice := hc.isOpen_compl.mem_nhds hP
  have hev : deriv L.weierstrassP =ᶠ[nhds P] L.derivWeierstrassP := by
    filter_upwards [hopen] with w hw
    first
      | exact (L.hasDerivAt_weierstrassP hw).deriv
      | exact (PeriodPair.hasDerivAt_weierstrassP L hw).deriv
      | exact congrFun L.deriv_weierstrassP w
  have h1 : deriv (fun z => L.weierstrassP (z + P)) = fun w => deriv L.weierstrassP (w + P) := by
    funext w
    rw [deriv_comp_add_const]
  have h2 : deriv (fun w => deriv L.weierstrassP (w + P)) 0 = 6 * L.weierstrassP P ^ 2 - L.g₂ / 2 := by
    rw [deriv_comp_add_const, zero_add, hev.deriv_eq]
    exact (Formalism.L2.Th1.F.pSecond L P hP).deriv
  have h3 : iteratedDeriv 2 (fun z => L.weierstrassP (z + P)) =
      deriv (deriv (fun z => L.weierstrassP (z + P))) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h3, h1, h2, Nat.factorial_two]
  push_cast
  ring
end Formalism.L2.Th1.B.KSum
