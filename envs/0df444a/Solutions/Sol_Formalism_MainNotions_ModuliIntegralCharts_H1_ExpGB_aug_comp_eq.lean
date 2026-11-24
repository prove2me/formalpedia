-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB.aug_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:44:18.103848+00:00
-- url     : https://prove2.me/submissions/5b764f61-7b82-4ad4-bafc-2be8817d48e1

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ScaleGenIsGen
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBPrim
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
section Jet
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
private theorem jetAug_mk_lemma (P : MvPolynomial κ S) :
    (jetAug : Jet S κ 0 →ₐ[S] S) (Ideal.Quotient.mk (orig S κ ^ (0 + 1)) P) =
      MvPolynomial.constantCoeff P := by
  show MvPolynomial.aeval (fun _ => (0 : S)) P = _
  simp [MvPolynomial.aeval_zero']
private theorem jet0_eq_lemma (x : Jet S κ 0) :
    x = algebraMap S (Jet S κ 0) ((jetAug : Jet S κ 0 →ₐ[S] S) x) := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (0 + 1)) x
  rw [jetAug_mk_lemma]
  show (Ideal.Quotient.mk (orig S κ ^ (0 + 1))) P =
    Ideal.Quotient.mk (orig S κ ^ (0 + 1)) (MvPolynomial.C (MvPolynomial.constantCoeff P))
  rw [Ideal.Quotient.eq]
  have h := sub_const_mem_orig P
  simpa using h
end Jet
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
theorem _root_.solution (f : Jet S κ 0 →ₐ[S] Jet S κ' 0) :
    (jetAug : Jet S κ' 0 →ₐ[S] S).comp f = jetAug := by
  refine AlgHom.ext fun x => ?_
  have hx := jet0_eq_lemma x
  rw [AlgHom.comp_apply, hx]
  simp only [AlgHom.commutes]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGB
