-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c.twist_sym
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:50:33.51642+00:00
-- url     : https://prove2.me/submissions/1aba919d-ef9d-4007-b39a-2fc01a9ac42c

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
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
private lemma germEval_oneStandardPoint_self_lemma_3 {n : ℕ} (b : Fin 2 → Pt S n d)
    (hb : ∀ j i, MvPowerSeries.constantCoeff (b j i) = 0) (j : Fin 2) (f : PS S 1 d) :
    ev b (ev (n := 2) ![pt S d j] f) = ev ![b j] f := by
  rw [ev_ev _ _ (fun j' i => by fin_cases j'; exact cc_pt_lemma j i) hb]
  congr 1
  funext j' i
  fin_cases j'
  exact ev_X b hb j i
private lemma ev_hom_lemma_4 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a f = MvPowerSeries.substAlgHom (hasSubst_pts a ha) f := by
  rw [MvPowerSeries.coe_substAlgHom]
  rfl
private lemma ev_neg_lemma_5 {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d) :
    ev a (-f) = -ev a f := by
  rw [ev_hom_lemma_4 a ha, ev_hom_lemma_4 a ha, map_neg]
private lemma eval_expSeries {m n : ℕ} (a : Fin m → Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS S m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : ev a (expP f) = expP (ev a f) :=
  subst_exp (fun p : Fin m × Fin d => a p.1 p.2) (fun s => ha s.1 s.2) hf
private lemma ev_bilL_lemma_9 {n : ℕ} (G : FGLaw S d) (c : Fin d → Fin d → S) (x y : Pt S n d)
    (ha : ∀ j i, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → Pt S n d) j i) = 0) :
    ev ![x, y] (bilL G c) = ∑ i, ∑ l, c i l •
      (ev ![x] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) * ev ![y] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G l)) := by
  have key : ∀ f, ev ![x, y] f = MvPowerSeries.substAlgHom (hasSubst_pts _ ha) f :=
    fun f => ev_hom_lemma_4 _ ha f
  have hl : ∀ (j : Fin 2) i, ev ![x, y] (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) =
      ev ![(![x, y] : Fin 2 → Pt S n d) j] (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) :=
    fun j i => germEval_oneStandardPoint_self_lemma_3 _ ha j _
  rw [key]
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_mul, ← key, ← key, hl, hl]
  all_goals rfl
end Series
section Jet
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
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
theorem _root_.solution (G : FGLaw S d) (cc : Fin d → Fin d → S) (hs : ∀ i l, cc i l = cc l i) :
    ev (n := 2) ![pt S d 1, pt S d 0] (expP (-bilL G cc)) = expP (-bilL G cc) := by
  have ha : ∀ j i, MvPowerSeries.constantCoeff ((![pt S d 1, pt S d 0] : Fin 2 → Pt S 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_pt_lemma _ i
    · exact cc_pt_lemma _ i
  have hneg : MvPowerSeries.constantCoeff (-bilL G cc) = 0 := by
    rw [map_neg, cc_bilL_lemma_8 G cc, neg_zero]
  have hsw : ev (n := 2) ![pt S d 1, pt S d 0] (bilL G cc) = bilL G cc := by
    rw [ev_bilL_lemma_9 G cc _ _ ha]
    conv_rhs => rw [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
    rw [hs l i, mul_comm] <;> rfl
  rw [eval_expSeries _ ha _ hneg, ev_neg_lemma_5 _ ha, hsw]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
