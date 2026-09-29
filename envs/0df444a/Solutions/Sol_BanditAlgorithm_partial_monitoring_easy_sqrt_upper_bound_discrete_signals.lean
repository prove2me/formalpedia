-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_easy_sqrt_upper_bound_discrete_signals
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T17:50:25.641549+00:00
-- url     : https://prove2.me/submissions/2bb07d46-86fb-40a5-8761-2a8ef05464b4

import Theorems.Thm_BanditAlgorithm_partial_monitoring_exists_unit_affine_normalization
import Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_upper_bound_discrete_signals
import Theorems.Thm_BanditAlgorithm_pm_minimax_regret_of_affine_loss

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (h : LocallyObservable G ∧ HasNeighbouringActions G) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      pmMinimaxRegret G n ≤ C * Real.sqrt n := by
  classical
  obtain ⟨a, b, hab⟩ := h.2
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
  obtain ⟨G', lam, c, hlam, hunit, hloc, hL, hΦ⟩ :=
    partial_monitoring_exists_unit_affine_normalization G
  obtain ⟨D, hD, hupper⟩ :=
    partial_monitoring_locally_observable_upper_bound_discrete_signals
      G' hk hunit (hloc h.1)
  have hkR : (1 : ℝ) < k := by exact_mod_cast hk
  have hlog : 0 < Real.log k := Real.log_pos hkR
  let E := D * max 1 (pmLocObsConst G') * (k : ℝ) ^ ((3 : ℝ) / 2) *
    Real.sqrt (Real.log k)
  have hE : 0 < E := by
    dsimp [E]
    have : (0 : ℝ) < (k : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_pos_of_pos (by positivity) _
    positivity
  refine ⟨E / lam, div_pos hE hlam, 0, ?_⟩
  intro n hn
  have hsqrtmul : Real.sqrt (n * Real.log k) =
      Real.sqrt n * Real.sqrt (Real.log k) := by
    rw [Real.sqrt_mul (by positivity)]
  have hu := hupper n
  rw [hsqrtmul] at hu
  have hu' : pmMinimaxRegret G' n ≤ E * Real.sqrt n := by
    simpa [E, mul_assoc, mul_left_comm, mul_comm] using hu
  have heq := pm_minimax_regret_of_affine_loss G G' lam hlam.le c hL hΦ n
  rw [heq] at hu'
  rw [show E / lam * Real.sqrt n = (E * Real.sqrt n) / lam by ring]
  exact (le_div_iff₀ hlam).mpr (by simpa [mul_comm] using hu')

end
end BanditAlgorithm
