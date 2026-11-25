-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b.mk_X_psJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:40:51.182718+00:00
-- url     : https://prove2.me/submissions/e0693e12-c10f-4a6e-98be-799c9d929b8d

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ExpLaw
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HomUniq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_PderivSecondEvFirstPointEqZero
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
theorem _root_.solution {n : ℕ} (m : ℕ) (q : Fin n × Fin d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n × Fin d) ^ (m + 1)) (X q) = psJet m (pt S d q.1 q.2) := by
  unfold psJet
  rw [Ideal.Quotient.eq]
  have hc : ∀ e, MvPowerSeries.coeff e (pt S d q.1 q.2) = if e = Finsupp.single q 1 then (1 : S) else 0 := by
    intro e; simp [pt, MvPowerSeries.coeff_X]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp only [zero_add, pow_one]
    refine sub_mem (Ideal.subset_span ⟨q, rfl⟩) ?_
    unfold psTrunc
    refine Ideal.sum_mem _ fun e _ => ?_
    rw [hc]
    split_ifs with he
    · subst he
      exact Ideal.subset_span ⟨q, rfl⟩
    · rw [map_zero]
      exact Ideal.zero_mem _
  · have hmem : Finsupp.single q 1 ∈ degLE m := by
      unfold degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => if i = q then ⟨1, by omega⟩ else 0, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = q
        · subst h
          simp
        · simp [h, Finsupp.single_apply, Ne.symm h]
      · rw [Finsupp.sum_single_index rfl]
        show 1 ≤ m
        omega
    have ht : psTrunc m (pt S d q.1 q.2) = X q := by
      unfold psTrunc
      rw [Finset.sum_eq_single (Finsupp.single q 1)]
      · rw [hc, if_pos rfl]
        rfl
      · intro b _ hb
        rw [hc, if_neg hb, map_zero]
      · intro h
        exact absurd hmem h
    rw [ht, sub_self]
    exact Ideal.zero_mem _
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
