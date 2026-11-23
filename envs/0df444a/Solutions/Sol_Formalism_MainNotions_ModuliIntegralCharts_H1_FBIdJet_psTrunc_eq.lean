-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:21.027825+00:00
-- url     : https://prove2.me/submissions/97ddabec-2aa3-4d02-8fc9-f7b71c3ba9df

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermDJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) :
    psTrunc m f = MvPowerSeries.truncTotal (m + 1) f := by
  ext e
  have hle : ∀ i, e i ≤ e.degree := fun i => by
    first
    | exact Finsupp.le_degree i e
    | exact Finsupp.le_degree e i
    | (by_cases hi : e i = 0
       · omega
       · exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
           (Finsupp.mem_support_iff.2 hi))
  have hdeg : (e.sum fun _ k => k) = e.degree := by
    first
    | rfl
    | simp [Finsupp.degree, Finsupp.sum]
  have hmem : e ∈ degLE m ↔ e.degree < m + 1 := by
    unfold degLE
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_, h⟩
      omega
    · intro h
      refine ⟨⟨fun i => ⟨e i, by have := hle i; omega⟩, ?_⟩, by omega⟩
      ext i
      simp
  have hL : MvPolynomial.coeff e (psTrunc m f) =
      if e ∈ degLE m then MvPowerSeries.coeff e f else 0 := by
    unfold psTrunc
    rw [MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    first
    | exact Finset.sum_ite_eq' (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | exact Finset.sum_ite_eq (degLE m) e (fun x => MvPowerSeries.coeff x f)
    | simp
  rw [hL]
  by_cases h : e.degree < m + 1
  · rw [if_pos (hmem.2 h), MvPowerSeries.coeff_truncTotal]
    exact h
  · rw [if_neg (fun h' => h (hmem.1 h'))]
    first
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero (by omega)).symm
    | exact (MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)).symm
    | (rw [MvPowerSeries.coeff_truncTotal_eq_zero]; omega)
    | exact (MvPowerSeries.coeff_truncTotal_of_le (by omega)).symm
    | simp [MvPowerSeries.truncTotal, MvPowerSeries.truncTotalFun, MvPolynomial.coeff_sum, h]
    | (simp [MvPowerSeries.truncTotal, h]; done)
end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
