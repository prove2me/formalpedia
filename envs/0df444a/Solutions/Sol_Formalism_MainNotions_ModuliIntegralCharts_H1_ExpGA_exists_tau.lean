-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA.exists_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:28.442582+00:00
-- url     : https://prove2.me/submissions/34cdf5bd-405a-4360-8e1a-05d17b8b30fb

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpTie
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBCorr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_HarmonicValueIntegral
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CPfSym
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpGA_eL_isGen
import Theorems.Thm_Formalism_L2_Pj_isChart_iff
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_formEq_eL
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_corr_of_val
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
theorem _root_.solution (C : ChartAt Xo c y) (m : ℕ) :
    ∃ τ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (Y := (jO y C.d m 1).left) (K := Fin 1) (fun _ => (C.x m).left)
      fun _ => (1 : ℤ)), τ.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ τ (eL y C.d C.x C.B.A.act C.e C.wP m) := by
  have hL := Xo.univ.t.PP.isLB
  have hch := (isChart_iff y C.d C.B.G.F C.B.A.act C.uvec C.x).1 C.chart
  obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (C.x m).left) (ε' := fun _ => (1 : ℤ)) (by
      intro U _ hU
      have hf : ∀ I : ULift.{0} (Finset (Fin 2)),
          (C.x m).left ≫ cφ ![𝟙 Xo.univ.t.G, Xo.univ.t.act.act H.w0] I =
            (homAt y.x (jetSubstP m fun p : Fin 2 × Fin C.d =>
              (![fun j => MvPolynomial.X ((0 : Fin 1), j), fun j => psIn C.d m ![0] (C.B.A.act H.w0 j)] :
                Fin 2 → Fin C.d → MvPolynomial (Fin 1 × Fin C.d) S) p.1 p.2)).left ≫
              cφ ![jpt y C.d C.x m (0 : Fin 2), jpt y C.d C.x m (1 : Fin 2)] I :=
        fun I => GermD.formEq_eL hch m I
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, hf]
      rw [_root_.mul_assoc, ← Finset.prod_mul_distrib]
      simp only [← zpow_add, neg_add_cancel, zpow_zero, Finset.prod_const_one, _root_.mul_one]) _ (eL_isGen C m)
  exact ⟨τ, hτ, corr_of_val hL fun y' J hJ => hv _ (𝟙 _) y' J hJ⟩
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGA
