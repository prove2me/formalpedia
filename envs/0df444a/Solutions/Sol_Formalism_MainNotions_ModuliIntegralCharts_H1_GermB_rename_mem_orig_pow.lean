-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermB.rename_mem_orig_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:46:58.53723+00:00
-- url     : https://prove2.me/submissions/883e2103-1267-4a9b-a648-328b355481c0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBFr
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermBSer

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] {κ κ' : Type}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
theorem _root_.solution {κ'' : Type} (f : κ' → κ'') (n : ℕ) {p : MvPolynomial κ' S} (hp : p ∈ orig S κ' ^ n) :
    MvPolynomial.rename f p ∈ orig S κ'' ^ n := by
  have hle : Ideal.map (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) (orig S κ') ≤
      orig S κ'' := by
    unfold orig
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨f j, (MvPolynomial.rename_X f j).symm⟩
  have hm := Ideal.mem_map_of_mem (MvPolynomial.rename f : MvPolynomial κ' S →ₐ[S] MvPolynomial κ'' S) hp
  rw [Ideal.map_pow] at hm
  exact Ideal.pow_right_mono hle n hm
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
