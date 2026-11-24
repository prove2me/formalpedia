-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.subst_jpt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:44.423159+00:00
-- url     : https://prove2.me/submissions/a5d8ec51-2136-4849-81da-09e94de5412e

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdLB
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdSy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThetaSwapFirstTwo
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp

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
private theorem jetMap_mk_lemma {κ κ' : Type} (m : ℕ) (f : κ → MvPolynomial κ' S) (hf : ∀ i, f i ∈ orig S κ')
    (P : MvPolynomial κ S) :
    jetMap (m := m) f hf (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval f P) := by
  rfl
private theorem jetSubstP_mk_eq_mk_aeval_sub_C {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (P : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) P) =
      Ideal.Quotient.mk (orig S κ' ^ (m + 1)) (aeval (fun i => φ i - C (constantCoeff (φ i))) P) := by
  rfl
end Jet
section Pts
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
private theorem subst_jpt_lemma_3 {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (i : Fin n) (k : Fin n') (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have key : (jetSubstP m ψ).comp (jetCopy d m i) = jetCopy d m k := by
    refine DFunLike.ext _ _ fun y => ?_
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig S (Fin 1 × Fin d) ^ (m + 1)) y
    show jetSubstP m ψ (jetCopy d m i (Ideal.Quotient.mk _ P)) = jetCopy d m k (Ideal.Quotient.mk _ P)
    simp only [jetCopy, jetMap_mk_lemma, jetSubstP_mk_eq_mk_aeval_sub_C]
    exact congrArg _ (DFunLike.congr_fun (MvPolynomial.algHom_ext
      (f := (aeval fun p => ψ p - C (constantCoeff (ψ p))).comp
        (aeval fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)))
      (g := aeval fun p : Fin 1 × Fin d => (X (k, p.2) : MvPolynomial (Fin n' × Fin d) S))
      fun p => by simp [h]) P)
  unfold jptG
  rw [← Category.assoc, homAt_comp, key]
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
theorem _root_.solution {n n' : ℕ} (m : ℕ) (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = X (k, j)) :
    homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  exact subst_jpt_lemma_3 t x0 d x m ψ i k h
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh
