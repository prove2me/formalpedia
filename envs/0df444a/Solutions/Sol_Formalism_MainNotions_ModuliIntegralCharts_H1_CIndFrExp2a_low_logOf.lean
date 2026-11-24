-- Prove2me | solution 1 for Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a.low_logOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:18.521627+00:00
-- url     : https://prove2.me/submissions/9c10f3da-b008-4f0e-bca8-d74d98a960ca

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndFrFix
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_Models_FiniteGeneration_FiniteGenerationProofs_SolveV
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_LogLowOrderOne
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_dLin_logOf
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp2a_cc_logOf
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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
private lemma low_two_of_lemma {σ : Type} {f : MvPowerSeries σ S} (h0 : constantCoeff f = 0)
    (h1 : ∀ w, coeff (Finsupp.single w 1) f = 0) : Low 2 f := by
  classical
  intro e he
  by_cases hz : e = 0
  · subst hz
    rw [coeff_zero_eq_constantCoeff_apply]
    exact h0
  · obtain ⟨w, hw⟩ := Finsupp.support_nonempty_iff.mpr hz
    have hdeg : e.degree = ∑ s ∈ e.support, e s := rfl
    rw [hdeg] at he
    have hw1 : 1 ≤ e w := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hw)
    have hwle : e w ≤ ∑ s ∈ e.support, e s := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw
    have hew : e w = 1 := by omega
    have hv : ∀ v, v ≠ w → e v = 0 := by
      intro v hvw
      by_contra hne
      have hvs : v ∈ e.support := Finsupp.mem_support_iff.mpr hne
      have hsub : ({v, w} : Finset σ) ⊆ e.support :=
        Finset.insert_subset_iff.mpr ⟨hvs, Finset.singleton_subset_iff.mpr hw⟩
      have hle := Finset.sum_le_sum_of_subset (f := fun s => e s) hsub
      rw [Finset.sum_pair hvw] at hle
      have hv1 : 1 ≤ e v := Nat.one_le_iff_ne_zero.mpr hne
      omega
    have he1 : e = Finsupp.single w 1 := by
      ext v
      by_cases hvw : v = w
      · subst hvw
        simp [hew]
      · rw [hv v hvw, Finsupp.single_apply, if_neg (Ne.symm hvw)]
    rw [he1]
    exact h1 w
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.FG.SolveVAux Formalism.L2.Pj
variable {S : Type} [CommRing S]
variable [Algebra ℚ S] {d : ℕ}
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
theorem _root_.solution (G : FGLaw S d) (i : Fin d) :
    Low 2 (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i - X ((0 : Fin 1), i)) := by
  apply low_two_of_lemma
  · rw [map_sub, cc_logOf, constantCoeff_X, sub_zero]
  · intro w
    obtain ⟨a, j⟩ := w
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    have h : ReciprocityTheory.ChartRestriction.G.TB.dLin (fun i => ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) i j =
        (1 : Matrix (Fin d) (Fin d) S) i j := by
      rw [dLin_logOf G]
    change coeff (Finsupp.single ((0 : Fin 1), j) 1) (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) =
      (1 : Matrix (Fin d) (Fin d) S) i j at h
    rw [map_sub, coeff_X, h, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij, Finsupp.single_left_inj Nat.one_ne_zero]
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp2a
