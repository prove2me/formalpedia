-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:18.344163+00:00
-- url     : https://prove2.me/submissions/4a20b6e4-4f66-42f5-8331-558c5a6f03e8

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_snd_tp_psJet_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_sum_coeff_X
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_lin_unit

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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
variable {R : Type} [CommRing R]
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
theorem _root_.solution {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  set h : Fin 2 × Fin d → R := fun q => if q.1 = 0 then u q.2 else 0 with hh
  have h_0 : ∀ j, h ((0 : Fin 2), j) = u j := fun j => by simp [hh]
  have h_1 : ∀ j, h ((1 : Fin 2), j) = 0 := fun j => by simp [hh]
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst h
    (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) ha (G.F k)
  have hc : MvPowerSeries.subst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) (G.F k) = G.F k :=
    G.comm k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 0 i) = 0 :=
    fun i => (sum_coeff_X h ((1 : Fin 2), i)).trans (h_1 i)
  have inner1 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 1 i) = u i :=
    fun i => (sum_coeff_X h ((0 : Fin 2), i)).trans (h_0 i)
  rw [hc, tp_psJet] at key
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at key
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, h_0, h_1, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at key
  rw [key]
  exact lin_unit G u k
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
