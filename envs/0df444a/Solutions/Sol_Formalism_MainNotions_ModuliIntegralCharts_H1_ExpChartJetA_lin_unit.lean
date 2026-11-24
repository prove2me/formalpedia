-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA.lin_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:53:02.860081+00:00
-- url     : https://prove2.me/submissions/a71ab285-9ca0-4ac7-88f1-1c22c80ba830

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ExpChartJetA
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_tp_psJet
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_snd_tp_psJet_subst
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_ExpChartJetA_sum_coeff_X

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
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst (fun q : Fin 1 × Fin d => u q.2)
    (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) ha (G.F k)
  have hu : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2)
      (G.F k) = MvPowerSeries.X ((0 : Fin 1), k) := G.unit k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 0 i) = 0 := by
    intro i
    simp
  have inner1 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 1 i) = u i :=
    fun i => sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), i)
  rw [hu, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, zero_mul, Finset.sum_const_zero, zero_add] at key
  rw [← key, tp_psJet]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), k)
end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
