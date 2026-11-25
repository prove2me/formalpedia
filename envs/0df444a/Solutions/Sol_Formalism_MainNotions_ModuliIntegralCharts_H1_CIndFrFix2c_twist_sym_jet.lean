-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c.twist_sym_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:26:33.291562+00:00
-- url     : https://prove2.me/submissions/4e4cf021-76ab-4fc2-972c-0051f1bc2da8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2c_twist_sym
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrFix2b_jetSubstP_psJet
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)
section Series
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
end Series
section Jet
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
private lemma mkX_lemma_10 {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (s : ι) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S ι ^ (m + 1)) (MvPolynomial.X s) =
      psJet m (MvPowerSeries.X s : MvPowerSeries ι S) := by
  unfold Formalism.L2.Pj.psJet
  rw [Ideal.Quotient.eq]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [zero_add, pow_one]
    refine Ideal.sub_mem _ (Ideal.subset_span ⟨s, rfl⟩) ?_
    exact Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_mem_orig 0 _ (MvPowerSeries.constantCoeff_X s)
  · have hmem : (Finsupp.single s 1 : ι →₀ ℕ) ∈ Formalism.L2.Pj.degLE m := by
      unfold Formalism.L2.Pj.degLE
      rw [Finset.mem_filter, Finset.mem_image]
      refine ⟨⟨fun i => ⟨if i = s then 1 else 0, by split_ifs <;> omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
      · ext i
        by_cases h : i = s
        · subst h
          simp
        · simp [h, Ne.symm h, Finsupp.single_apply]
      · rw [Finsupp.sum_single_index rfl]
        exact hm
    have htr : Formalism.L2.Pj.psTrunc m (MvPowerSeries.X s : MvPowerSeries ι S) = MvPolynomial.X s := by
      unfold Formalism.L2.Pj.psTrunc
      rw [Finset.sum_eq_single_of_mem _ hmem
        (fun b _ hb => by rw [MvPowerSeries.coeff_X, if_neg hb, map_zero])]
      rw [MvPowerSeries.coeff_X, if_pos rfl]
      rfl
    rw [htr, sub_self]
    exact Ideal.zero_mem _
end Jet
section Chart
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
end Chart
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
theorem _root_.solution (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) (m : ℕ) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m (expP (-bilL G cc))) =
      psJet m (expP (-bilL G cc)) := by
  have hcc : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact cc_pt_lemma _ i'
    · exact cc_pt_lemma _ i'
  have hXc : ∀ p : Fin 2 × Fin d, MvPolynomial.constantCoeff
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) = 0 := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact MvPolynomial.constantCoeff_X S _
    · exact MvPolynomial.constantCoeff_X S _
  have hXm : ∀ p : Fin 2 × Fin d, Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin 2 × Fin d) ^ (m + 1))
      ((![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) =
        psJet m ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) p.1 p.2) := by
    rintro ⟨j', i'⟩
    fin_cases j'
    · exact mkX_lemma_10 m _
    · exact mkX_lemma_10 m _
  rw [jetSubstP_psJet m _ _ hcc hXc hXm, twist_sym G cc hs]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
