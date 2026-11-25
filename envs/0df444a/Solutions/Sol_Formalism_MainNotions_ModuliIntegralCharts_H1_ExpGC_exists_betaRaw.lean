-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC.exists_betaRaw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:36:35.064845+00:00
-- url     : https://prove2.me/submissions/227a3ff4-5d2d-4f19-b2fe-124ddc2e8ea5

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CocycleProductThree
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_act_zero
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_c__8940c3ad981f
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_comp_th__a85f9d38c14f
import Theorems.Thm_P2M_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_prod_c_2_07c5413953a7
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_cocycle_product_three
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGC_Bq_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen


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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
theorem _root_.solution (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : AdTy Xo a) (hwa : wLa.IsGen) (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (Bq wP a wLa wLb) r z J := by
  have hL := Xo.univ.t.PP.isLB
  refine exists_gen hL ?_ _ (Bq_isGen wP hwP a wLa hwa wLb hwb)
  intro U _ hU
  unfold betaφ betaε
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Fin.prod_univ_four,
    comp_cφ, comp_thφ, Category.comp_id, zpow_neg, zpow_one, neg_neg, Finset.prod_inv_distrib, prod_cφ2, cocycle_product_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, x3, lift_fst, lift_snd_assoc, lift_snd, lift_fst_assoc, Category.id_comp]
  have h1 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p * Xo.univ.t.act.act q = Xo.univ.t.act.act (p + q) :=
    fun p q => (Xo.univ.t.act.add p q).symm
  have h2 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p ≫ Xo.univ.t.act.act q = Xo.univ.t.act.act (p * q) :=
    fun p q => (Xo.univ.t.act.mul p q).symm
  have h3 : (1 : Xo.univ.t.G ⟶ Xo.univ.t.G) = Xo.univ.t.act.act 0 := act_zero.symm
  have h4 : 𝟙 Xo.univ.t.G = Xo.univ.t.act.act 1 := Xo.univ.t.act.one.symm
  have h5 : 𝟙 Xo.univ.t.G.left = (Xo.univ.t.act.act 1).left := by rw [Xo.univ.t.act.one]; rfl
  simp only [h3, h1, h2, hbb, h4, h5]
  ring_nf
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  abel
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
