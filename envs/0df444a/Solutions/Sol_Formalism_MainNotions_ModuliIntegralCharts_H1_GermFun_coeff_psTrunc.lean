-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun.coeff_psTrunc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:47.423675+00:00
-- url     : https://prove2.me/submissions/58cea5b4-d782-4c0b-8f1c-62c06f43bc0b

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFun
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermFunPf

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
theorem _root_.solution {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : MvPowerSeries ι R) (e : ι →₀ ℕ) (he : e.degree ≤ m) :
    MvPolynomial.coeff e (psTrunc m f) = MvPowerSeries.coeff e f := by
  unfold psTrunc
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single e]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro d _ hde
    rw [MvPolynomial.coeff_monomial, if_neg hde]
  · intro he'
    exfalso
    apply he'
    have hdeg : e.sum (fun _ k => k) = e.degree := by
      rfl
    unfold degLE
    rw [Finset.mem_filter, Finset.mem_image]
    refine ⟨⟨fun i => ⟨e i, ?_⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · have hle : e i ≤ e.sum (fun _ k => k) := by
        by_cases hi : i ∈ e.support
        · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hi
        · simp only [Finsupp.mem_support_iff, not_not] at hi
          rw [hi]
          exact Nat.zero_le _
      omega
    · ext i
      simp
    · omega
end Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
