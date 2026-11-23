-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.formEq_eL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:30:35.12664+00:00
-- url     : https://prove2.me/submissions/654eb9a4-660e-46b6-ba7c-0631ef0446d2

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDVal
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDPf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_comp
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_GermD_homAt_id
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
namespace GermD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
private lemma formEq_eL_lemma (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (0 : Fin 2)) = AlgHom.id S _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp
private lemma formEq_eL_lemma_2 (m : ℕ) (g : Fin d → MvPowerSeries (Fin 1 × Fin d) S) :
    (sL m g).comp (jetCopy d m (1 : Fin 2)) = jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (g p.2) := by
  have hq : ∀ q : MvPolynomial (Fin 1 × Fin d) S,
      MvPolynomial.rename (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) q = q := by
    intro q
    rw [show (fun p : Fin 1 × Fin d => ((0 : Fin 1), p.2)) = id from
      funext fun p => Prod.ext (Subsingleton.elim _ _) rfl]
    simp
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, j⟩
  fin_cases i
  simp [sL, jetCopy, jetMap, jetSubstP, liftJet, Ideal.Quotient.liftₐ_apply]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]
  erw [Ideal.Quotient.lift_mk]
  simp [psIn, hq]
end GermD
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
variable {t x0 d x}
variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {κ : Type} [Fintype κ] {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
theorem _root_.solution (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ) (I : ULift (Finset (Fin 2))) :
    (x m).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (homAt x0 (sL m (act H.w0))).left ≫ cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I := by
  have hp : ∀ {T T' : Over X0} (f : T' ⟶ T) (a b : T ⟶ t.G),
      f ≫ padd t.G a b = padd t.G (f ≫ a) (f ≫ b) := by
    intro T T' f a b
    simp only [padd, ← Category.assoc, comp_lift]
  have nat : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (l : List (Fin 2)),
      f ≫ l.foldr (fun k acc => padd t.G (xs k) acc) (pzero t.G T) =
        l.foldr (fun k acc => padd t.G (f ≫ xs k) acc) (pzero t.G T') := by
    intro T T' f xs l
    induction l with
    | nil => simp only [List.foldr_nil, pzero, ← Category.assoc, comp_toUnit]
    | cons k l ih => simp only [List.foldr_cons, hp, ih]
  have natp : ∀ {T T' : Over X0} (f : T' ⟶ T) (xs : Fin 2 → (T ⟶ t.G)) (J : Finset (Fin 2)),
      f ≫ psum t.G xs J = psum t.G (fun i => f ≫ xs i) J := by
    intro T T' f xs J
    unfold psum
    exact nat f xs _
  simp only [cφG]
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  rw [natp, natp]
  congr 1
  funext i
  fin_cases i
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_id]
  · simp [jptG, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp, formEq_eL_lemma_2, hch.act m H.w0]
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
