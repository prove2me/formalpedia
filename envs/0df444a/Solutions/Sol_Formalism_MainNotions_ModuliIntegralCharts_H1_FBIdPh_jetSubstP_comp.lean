-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.jetSubstP_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:46:55.405285+00:00
-- url     : https://prove2.me/submissions/8bcd231a-4fdc-4ae9-8d20-e20566304f23

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdPh_cc_aeval
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
section Jet
variable {S : Type} [CommRing S]
private theorem jetSubstP_mk_eq_mk_aeval_sub_C {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by
  rfl
end Jet
section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
end Pts
section Gen
end Gen
section Ser
variable {S : Type} [CommRing S] (d : ℕ)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
end Ser
section Comm
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)
end Comm
section AxTools
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
end AxTools
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
theorem _root_.solution {κ κ' κ'' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (ψ : κ' → MvPolynomial κ'' S)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (hψ : ∀ i, constantCoeff (ψ i) = 0) :
    (jetSubstP m ψ).comp (jetSubstP m φ) = jetSubstP m (fun i => aeval ψ (φ i)) := by
  refine DFunLike.ext _ _ fun x => ?_
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S κ ^ (m + 1)) x
  show jetSubstP m ψ (jetSubstP m φ (Ideal.Quotient.mk _ P)) =
    jetSubstP m (fun i => aeval ψ (φ i)) (Ideal.Quotient.mk _ P)
  simp only [jetSubstP_mk_eq_mk_aeval_sub_C, hφ, hψ, cc_aeval ψ hψ, map_zero, sub_zero]
  exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext (f := (aeval ψ).comp (aeval φ))
    (g := aeval fun i => aeval ψ (φ i)) fun i => by simp) P)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
