-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.mk_psTrunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:17:19.97569+00:00
-- url     : https://prove2.me/submissions/add9588e-ee7b-4c48-a212-605947800ed0

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ChartSer
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ChartDataPf
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
private theorem mem_degLE_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (e : κ →₀ ℕ) :
    e ∈ degLE m ↔ Finsupp.degree e ≤ m := by
  constructor
  · intro he
    simp [degLE] at he
    exact he.2
  · intro hd
    have hle : ∀ i, e i ≤ m := by
      intro i
      refine le_trans ?_ hd
      by_cases hi : i ∈ e.support
      · exact Finset.single_le_sum (f := fun j => e j) (fun j _ => Nat.zero_le _) hi
      · have h0 : e i = 0 := by simpa using hi
        omega
    simp [degLE]
    refine ⟨⟨fun i => ⟨e i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, hd⟩
    ext i
    simp
end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB.Canon
open scoped CategoryTheory.Obj
namespace Formalism.MainNotions.ModuliIntegralCharts.H1
theorem _root_.solution {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    Chart.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by
  have h0 : MvPolynomial.constantCoeff (psTrunc m f) = 0 := by
    simp only [psTrunc, map_sum, MvPolynomial.constantCoeff_monomial]
    refine Finset.sum_eq_zero fun x _ => ?_
    split_ifs with hx
    · rw [hx, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    · rfl
  rw [h0, map_zero, sub_zero]
  unfold Chart.pj
  congr 1
  ext e
  simp only [psTrunc, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with he
  · have hd : Finsupp.degree e ≤ m := (mem_degLE_lemma m e).1 he
    rw [MvPowerSeries.coeff_truncTotal]
    omega
  · have hd : ¬ Finsupp.degree e ≤ m := fun h => he ((mem_degLE_lemma m e).2 h)
    first
      | rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega
      | simp [MvPowerSeries.truncTotal, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]; omega
end Formalism.MainNotions.ModuliIntegralCharts.H1
