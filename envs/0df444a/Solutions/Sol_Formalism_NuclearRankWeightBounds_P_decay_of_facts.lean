-- Prove2me | solution 1 for Formalism.NuclearRankWeightBounds.P.decay_of_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:11:15.175151+00:00
-- url     : https://prove2.me/submissions/fad002ec-3f83-490d-9555-b08a093c6424

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DecayAsm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Formalism.NuclearRankWeightBounds.D
namespace Formalism.NuclearRankWeightBounds.P
theorem _root_.solution : Formalism.NuclearRankWeightBounds.D.CBWeights → Formalism.NuclearRankWeightBounds.D.NuclearBound → Formalism.NuclearRankWeightBounds.D.RankBlock →
    Formalism.NuclearRankWeightBounds.D.LogSumExp → Formalism.NuclearRankWeightBounds.D.WeightedOff → Formalism.NuclearRankWeightBounds.D.Decay := by
  intro hCB hNB hRB hLSE hWO N s ep h Y hs0 hY hzero hh
  have hW := hWO N s ep h Y hY hzero hh
  set H := hs Y with hH
  set r := Real.sqrt (2 * (q0 ep : ℝ)) with hr
  set c := min 1 (r * H)⁻¹ with hc
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := le_min zero_le_one (inv_nonneg.mpr (mul_nonneg hr0 hH0))
  have hbound : ∑ j, |hY.eigenvalues j| ≤ r * H := by
    refine (hNB N Y hY).trans ?_
    apply mul_le_mul_of_nonneg_right _ hH0
    apply Real.sqrt_le_sqrt
    exact_mod_cast hRB N ep Y hzero
  have key : ∀ i ∈ Ico 1 N, 0 < (lead (NormedSpace.exp Y) i).re ∧
      c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4
        ≤ Real.log (lead (NormedSpace.exp Y) i).re := by
    intro i hi
    have hiN : i ≤ N := (mem_Ico.mp hi).2.le
    obtain ⟨w, hw0, hw1, hlead, hmean, hsec⟩ := hCB N Y hY i hiN
    have hdiag : ∑ a ∈ univ.filter (fun a : Fin N => a.val < i), (Y a a).re = 0 := by
      apply Finset.sum_eq_zero
      intro a _
      simp [hzero a a rfl]
    rw [hdiag] at hmean hsec
    have hre : (lead (NormedSpace.exp Y) i).re = ∑ J ∈ powersetCard i (univ : Finset (Fin N)),
        w J * Real.exp (∑ j ∈ J, hY.eigenvalues j) := by
      rw [hlead, Complex.ofReal_re]
    have hy : ∀ J : Finset (Fin N), |∑ j ∈ J, hY.eigenvalues j| ≤ r * H := by
      intro J
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ hbound
      exact Finset.sum_le_sum_of_subset_of_nonneg (subset_univ J) (fun _ _ _ => abs_nonneg _)
    rw [hre]
    constructor
    · calc (0:ℝ) < Real.exp (-(r * H)) := Real.exp_pos _
        _ = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), w J * Real.exp (-(r * H)) := by
          rw [← Finset.sum_mul, hw1, one_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro J _
          apply mul_le_mul_of_nonneg_left _ (hw0 J)
          exact Real.exp_le_exp.mpr (neg_le_of_abs_le (hy J))
    · have e : ∀ f : Finset (Fin N) → ℝ,
          ∑ J : ↥(powersetCard i (univ : Finset (Fin N))), f J.1
            = ∑ J ∈ powersetCard i (univ : Finset (Fin N)), f J :=
        fun f => Finset.sum_coe_sort _ f
      have e1 := e (fun J => w J)
      have e2 := e (fun J => w J * (∑ j ∈ J, hY.eigenvalues j))
      have e3 := e (fun J => w J * (∑ j ∈ J, hY.eigenvalues j) ^ 2)
      have e4 := e (fun J => w J * Real.exp (∑ j ∈ J, hY.eigenvalues j))
      have := hLSE (↥(powersetCard i (univ : Finset (Fin N)))) (fun J => w J.1)
        (fun J => ∑ j ∈ J.1, hY.eigenvalues j) (r * H) (fun J => hw0 _)
        (by rw [e1, hw1]) (by rw [e2, hmean]) (fun J => hy _)
      rw [e3, e4, hsec, zero_pow two_ne_zero, zero_add] at this
      exact this
  have hprod : ∏ i ∈ Ico 1 N, (lead (NormedSpace.exp Y) i).re ^ (-(s i))
      = Real.exp (∑ i ∈ Ico 1 N, Real.log (lead (NormedSpace.exp Y) i).re * (-(s i))) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i hi
    exact Real.rpow_def_of_pos (key i hi).1 _
  rw [hprod, Real.exp_le_exp]
  have h1 : ∑ i ∈ Ico 1 N, Real.log (lead (NormedSpace.exp Y) i).re * (-(s i))
      ≤ ∑ i ∈ Ico 1 N, (c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4) * (-(s i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonpos_right (key i hi).2 (neg_nonpos.mpr (hs0 i))
  have h2 : ∑ i ∈ Ico 1 N, (c * (∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2) / 4) * (-(s i))
      = -(c / 4) * ∑ i ∈ Ico 1 N, s i * ∑ a ∈ univ.filter (fun a : Fin N => a.val < i),
        ∑ b ∈ univ.filter (fun b : Fin N => i ≤ b.val), ‖Y a b‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h3 : c * H ^ 2 = min (H ^ 2) (H / r) := by
    rw [hc, min_mul_of_nonneg _ _ (sq_nonneg H), one_mul]
    congr 1
    rcases eq_or_lt_of_le hH0 with h0 | h0
    · rw [← h0]; simp
    · rcases eq_or_lt_of_le hr0 with r0 | r0
      · rw [← r0]; simp
      · field_simp
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ -(c / 4) * (h * H ^ 2 / 2) := mul_le_mul_of_nonpos_left hW (by linarith)
    _ = -(h * (c * H ^ 2)) / 8 := by ring
    _ = _ := by rw [h3]
end Formalism.NuclearRankWeightBounds.P
