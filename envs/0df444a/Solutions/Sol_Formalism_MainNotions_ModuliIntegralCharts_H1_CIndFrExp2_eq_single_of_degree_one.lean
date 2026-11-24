-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2.eq_single_of_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:02.460948+00:00
-- url     : https://prove2.me/submissions/4769b5e3-6b54-440f-9a7d-a2a2463d08b1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FormalGroupLinearSecond
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt FGLaw)
variable {S : Type} [CommRing S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
theorem _root_.solution {κ : Type} (e : κ →₀ ℕ) (he : e.degree = 1) : ∃ q, e = Finsupp.single q 1 := by
  classical
  have h1 : ∑ i ∈ e.support, e i = 1 := by
    first
      | exact he
      | simpa [Finsupp.degree] using he
  obtain ⟨q, hq⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at h1
    exact zero_ne_one h1
  have h2 := Finset.add_sum_erase e.support e hq
  rw [h1] at h2
  have hq0 : e q ≠ 0 := Finsupp.mem_support_iff.1 hq
  have h3s : ∑ i ∈ e.support.erase q, e i = 0 := by omega
  have h3 := Finset.sum_eq_zero_iff.1 h3s
  refine ⟨q, ?_⟩
  ext i
  by_cases hi : i = q
  · subst hi
    rw [Finsupp.single_eq_same]
    omega
  · rw [Finsupp.single_apply, if_neg (Ne.symm hi)]
    by_contra hne
    exact hne (h3 i (Finset.mem_erase.2 ⟨hi, Finsupp.mem_support_iff.2 hne⟩))
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2
