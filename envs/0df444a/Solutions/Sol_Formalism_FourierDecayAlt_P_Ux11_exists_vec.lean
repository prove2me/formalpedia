-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.exists_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:54.179777+00:00
-- url     : https://prove2.me/submissions/802cf0ba-97fa-4614-bf77-e8f1e1c7b750

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux11_Norming_nonempty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {lam : I → V →L[ℝ] E} (hN : Norming lam) {Φ : X → V} {x₀ : X} {r M : ℝ} (hr : 0 < r)
    (D : I → X →L[ℝ] E)
    (hT : ∀ i, ∀ h : X, ‖h‖ < r → ‖lam i (Φ (x₀ + h)) - lam i (Φ x₀) - D i h‖ ≤ M * ‖h‖ ^ 2)
    (h : X) : ∃ v : V, ∀ i, lam i v = D i h := by
  obtain ⟨i₀⟩ := hN.nonempty
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = r / (2 * (‖h‖ + 1)) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεh : ε * ‖h‖ < r := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg h]
  obtain ⟨t, ht⟩ : ∃ t : ℕ → ℝ, ∀ n, t n = ε * (1 / 2) ^ n := ⟨_, fun _ => rfl⟩
  have ht0 : ∀ n, 0 < t n := fun n => by rw [ht]; positivity
  have htε : ∀ n, t n ≤ ε := fun n => by
    rw [ht]; exact mul_le_of_le_one_right hε0.le (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨q, hq⟩ : ∃ q : ℕ → V, ∀ n, q n = (t n)⁻¹ • (Φ (x₀ + t n • h) - Φ x₀) := ⟨_, fun _ => rfl⟩
  have key : ∀ i n, ‖lam i (q n) - D i h‖ ≤ M * ‖h‖ ^ 2 * t n := by
    intro i n
    have htn := (ht0 n).ne'
    have hn : ‖t n • h‖ < r := by
      rw [norm_smul, Real.norm_of_nonneg (ht0 n).le]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (htε n) (norm_nonneg h)) hεh
    have e : lam i (q n) - D i h =
        (t n)⁻¹ • (lam i (Φ (x₀ + t n • h)) - lam i (Φ x₀) - D i (t n • h)) := by
      rw [hq, map_smul, map_sub, map_smul, smul_sub, smul_sub, inv_smul_smul₀ htn, smul_sub]
    rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 (ht0 n).le)]
    calc (t n)⁻¹ * ‖lam i (Φ (x₀ + t n • h)) - lam i (Φ x₀) - D i (t n • h)‖
        ≤ (t n)⁻¹ * (M * ‖t n • h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hT i _ hn) (inv_nonneg.2 (ht0 n).le)
      _ = M * ‖h‖ ^ 2 * t n := by
          rw [norm_smul, Real.norm_of_nonneg (ht0 n).le]; field_simp
  have hMh : 0 ≤ M * ‖h‖ ^ 2 := by
    have := (norm_nonneg _).trans (key i₀ 0)
    nlinarith [ht0 0]
  have hdist : ∀ n, dist (q n) (q (n + 1)) ≤ (2 * (M * ‖h‖ ^ 2) * ε) * (1 / 2) ^ n := by
    intro n
    rw [dist_eq_norm]
    refine hN _ _ (fun i => ?_)
    have e : lam i (q n - q (n + 1)) = (lam i (q n) - D i h) - (lam i (q (n + 1)) - D i h) := by
      rw [map_sub]; abel
    rw [e]
    have hp : 0 ≤ ε * (1 / 2 : ℝ) ^ n := by positivity
    calc _ ≤ ‖lam i (q n) - D i h‖ + ‖lam i (q (n + 1)) - D i h‖ := norm_sub_le _ _
      _ ≤ M * ‖h‖ ^ 2 * t n + M * ‖h‖ ^ 2 * t (n + 1) := add_le_add (key i n) (key i (n + 1))
      _ ≤ _ := by
        rw [ht, ht, pow_succ (1 / 2 : ℝ) n]
        nlinarith [mul_nonneg hMh hp]
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric (1 / 2) _ (by norm_num) hdist)
  refine ⟨v, fun i => ?_⟩
  have h1 : Tendsto (fun n => lam i (q n)) atTop (𝓝 (lam i v)) := ((lam i).continuous.tendsto v).comp hv
  have h2 : Tendsto (fun n => lam i (q n)) atTop (𝓝 (D i h)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => key i n) ?_
    have : Tendsto (fun n : ℕ => M * ‖h‖ ^ 2 * (ε * (1 / 2 : ℝ) ^ n)) atTop (𝓝 (M * ‖h‖ ^ 2 * (ε * 0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
    rw [mul_zero, mul_zero] at this
    simpa only [ht] using this
  exact tendsto_nhds_unique h1 h2
end Formalism.FourierDecayAlt.P.Ux11
