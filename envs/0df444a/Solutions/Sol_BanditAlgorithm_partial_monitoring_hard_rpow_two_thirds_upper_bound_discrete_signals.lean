-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_hard_rpow_two_thirds_upper_bound_discrete_signals
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T20:22:57.567598+00:00
-- url     : https://prove2.me/submissions/fb12c04b-87e0-4230-8237-632e898f0260

import Theorems.Thm_BanditAlgorithm_partial_monitoring_exists_unit_affine_normalization
import Theorems.Thm_BanditAlgorithm_partial_monitoring_globally_observable_unit_hard_upper
import Theorems.Thm_BanditAlgorithm_pm_minimax_regret_of_affine_loss

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : GloballyObservable G ∧ ¬ LocallyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  classical
  have hneigh : HasNeighbouringActions G := by
    by_contra hn
    apply h.2
    intro a b hab
    exact (hn ⟨a, b, hab⟩).elim
  obtain ⟨a, b, hab⟩ := hneigh
  have habne : a ≠ b := by
    intro heq
    subst b
    have hdim1 := hab.1.2
    have hdim2 := hab.2.2.2
    rw [Set.inter_self] at hdim2
    omega
  have hk : 2 ≤ k := by
    have hc : 1 < Fintype.card (Fin k) :=
      Fintype.one_lt_card_iff.mpr ⟨a, b, habne⟩
    rw [Fintype.card_fin] at hc
    omega
  have hd : 0 < d := by
    have := hab.2.2.2
    omega
  obtain ⟨G', lam, c, hlam, hunit, hloc, hL, hΦ⟩ :=
    partial_monitoring_exists_unit_affine_normalization G
  have hcell (a : Fin k) : pmCell G' a = pmCell G a := by
    ext u
    simp only [pmCell, Set.mem_setOf_eq]
    constructor
    · intro hu
      refine ⟨hu.1, ?_⟩
      intro b
      have hb := hu.2 b
      have hsum :
          ∑ i, (G'.L a i - G'.L b i) * u i =
            lam * ∑ i, (G.L a i - G.L b i) * u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hL a i, hL b i]
        ring
      rw [hsum] at hb
      nlinarith
    · intro hu
      refine ⟨hu.1, ?_⟩
      intro b
      have hb := hu.2 b
      have hsum :
          ∑ i, (G'.L a i - G'.L b i) * u i =
            lam * ∑ i, (G.L a i - G.L b i) * u i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hL a i, hL b i]
        ring
      rw [hsum]
      exact mul_nonpos_of_nonneg_of_nonpos hlam.le hb
  have hglo' : GloballyObservable G' := by
    intro x y hxy
    have hxyG : NeighbouringActions G x y := by
      simpa only [NeighbouringActions, ParetoOptimalAction, hcell] using hxy
    obtain ⟨f, hf⟩ := h.1 x y hxyG
    refine ⟨fun z => lam * f z, ?_⟩
    intro i
    rw [hΦ, ← Finset.mul_sum, hf i, hL x i, hL y i]
    ring
  obtain ⟨D, hD, hupper⟩ :=
    partial_monitoring_globally_observable_unit_hard_upper G' hk hd hunit hglo'
  refine ⟨D / lam, div_pos hD hlam, 1, ?_⟩
  intro n hn
  have hu := hupper n hn
  have heq := pm_minimax_regret_of_affine_loss G G' lam hlam.le c hL hΦ n
  rw [heq] at hu
  rw [show D / lam * (n : ℝ) ^ ((2 : ℝ) / 3) =
      (D * (n : ℝ) ^ ((2 : ℝ) / 3)) / lam by ring]
  exact (le_div_iff₀ hlam).mpr (by simpa [mul_comm] using hu)

end
end BanditAlgorithm
