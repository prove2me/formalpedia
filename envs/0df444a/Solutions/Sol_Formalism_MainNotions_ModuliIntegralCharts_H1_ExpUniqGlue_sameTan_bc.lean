-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue.sameTan_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:34:12.571839+00:00
-- url     : https://prove2.me/submissions/b06776e7-0797-4952-a937-df6150fa6841

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpUniqGlue
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_ring
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_nat_over
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpUniqGlue_dual_comp

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqJet
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (x0 : Sp S ⟶ Xo.X) {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
theorem _root_.solution {x x' : ∀ m, overAt x0 (Jet S (Fin 1 × Fin d) m) ⟶ Xo.univ.t.G} (ht : SameTanR x0 d x x') :
    SameTanR (x0T f x0) d (xT f x0 x) (xT f x0 x') := by
  intro j
  have e := nat_ring f
    (ψ := (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S))
    (ψ' := (jetTan ((0 : Fin 1), j) : Jet T (Fin 1 × Fin d) (0 + 1) →ₐ[T] DualNumber T))
    (bB := ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) (fun s => RingHom.congr_fun (dual_comp f) s) (fun q => by
      show aeval _ (X q) = ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f (aeval _ (X q))
      simp only [aeval_X]
      split_ifs <;> ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR])
  have k := nat_over f x0 (bcJ f _ 1) (bcJ_comp f _ 1) (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) (dual_comp f) _ _ e
  unfold xT
  simp only [← Category.assoc, k]
  simp only [Category.assoc, ht j]
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqGlue
