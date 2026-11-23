-- Prove2me | solution 1 for Formalism.CountingSumsFrames.mean_share_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:13.716791+00:00
-- url     : https://prove2.me/submissions/5506b81c-bce7-4630-afdd-499b2920eaaa

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_sum_update_swap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution : MeanShareA := by
  intro s As Ap U top bad rk m X eps epsP K hAs hAp htop hbad hX hm hK hXavg hbadavg
  have hSne : (Fintype.piFinset As).Nonempty := Fintype.piFinset_nonempty.mpr hAs
  have hSc : (0 : ℝ) < (Fintype.piFinset As).card := by exact_mod_cast hSne.card_pos
  have hApc : (0 : ℝ) < Ap.card := by exact_mod_cast hAp.card_pos
  have hA : ∀ aa ∈ Fintype.piFinset As, ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤
      2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := by
    intro aa haa
    obtain ⟨hm0, hmrk⟩ := hm aa haa
    have hmne : m aa ≠ 0 := hm0.ne'
    have h1 : ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤ ∑ ap ∈ Ap, bad aa ap * 2 / m aa := by
      refine Finset.sum_le_sum fun ap hap => ?_
      calc bad aa ap / rk aa ap ≤ bad aa ap / (m aa / 2) :=
            div_le_div_of_nonneg_left (hbad aa haa ap hap) (by positivity) (hmrk ap hap)
        _ = bad aa ap * 2 / m aa := by rw [div_div_eq_mul_div]
    have h2 := hbadavg aa haa
    rw [div_le_iff₀ hApc] at h2
    calc ∑ ap ∈ Ap, bad aa ap / rk aa ap ≤ ∑ ap ∈ Ap, bad aa ap * 2 / m aa := h1
      _ = (∑ ap ∈ Ap, bad aa ap) * 2 / m aa := by rw [← Finset.sum_div, ← Finset.sum_mul]
      _ ≤ ((∑ i ∈ U, X i aa + epsP * m aa) * Ap.card) * 2 / m aa :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by norm_num)) hm0.le
      _ = 2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := by
          rw [← Finset.sum_div]
          field_simp
  have hB : ∀ i ∈ U, ∑ aa ∈ Fintype.piFinset As, X i aa / m aa ≤
      (Fintype.piFinset As).card * K * eps i := by
    intro i hi
    have hAsc : (0 : ℝ) < (As i).card := by exact_mod_cast (hAs i).card_pos
    have hupd : ∀ aa ∈ Fintype.piFinset As, ∀ x ∈ As i, Function.update aa i x ∈ Fintype.piFinset As := by
      intro aa haa x hx
      rw [Fintype.mem_piFinset] at haa ⊢
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simpa using hx
      · rw [Function.update_of_ne hj]
        exact haa j
    have hinner : ∀ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, X i (Function.update aa i x) /
        m (Function.update aa i x) ≤ K * (As i).card * eps i := by
      intro aa haa
      have hT := (hm _ (hupd aa haa _ (htop i hi))).1
      have hTne : m (Function.update aa i (top i)) ≠ 0 := hT.ne'
      have hK0 : 0 ≤ K := by
        have hh := hK i hi _ (hupd aa haa _ (htop i hi))
        rw [Function.update_idem] at hh
        nlinarith
      have hle : ∀ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x) ≤
          X i (Function.update aa i x) * K / m (Function.update aa i (top i)) := by
        intro x hx
        have hmx := (hm _ (hupd aa haa x hx)).1
        have hKx := hK i hi _ (hupd aa haa x hx)
        rw [Function.update_idem] at hKx
        rw [div_le_div_iff₀ hmx hT]
        have hXx := hX i hi _ (hupd aa haa x hx)
        nlinarith [mul_le_mul_of_nonneg_left hKx hXx]
      have havg := hXavg i hi aa haa
      rw [div_le_iff₀ hAsc] at havg
      calc ∑ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x)
          ≤ ∑ x ∈ As i, X i (Function.update aa i x) * K / m (Function.update aa i (top i)) :=
            Finset.sum_le_sum hle
        _ = (∑ x ∈ As i, X i (Function.update aa i x)) * K / m (Function.update aa i (top i)) := by
            rw [← Finset.sum_div, ← Finset.sum_mul]
        _ ≤ (eps i * m (Function.update aa i (top i)) * (As i).card) * K /
              m (Function.update aa i (top i)) := by
            apply div_le_div_of_nonneg_right _ hT.le
            exact mul_le_mul_of_nonneg_right havg hK0
        _ = K * (As i).card * eps i := by
            field_simp
    have hswap := sum_update_swap As i (fun aa => X i aa / m aa)
    beta_reduce at hswap
    have htot : ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, X i aa / m aa ≤
        ((As i).card : ℝ) * ((Fintype.piFinset As).card * K * eps i) := by
      rw [← hswap]
      calc ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, X i (Function.update aa i x) / m (Function.update aa i x)
          ≤ ∑ aa ∈ Fintype.piFinset As, K * (As i).card * eps i := Finset.sum_le_sum hinner
        _ = ((As i).card : ℝ) * ((Fintype.piFinset As).card * K * eps i) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    exact le_of_mul_le_mul_left htot hAsc
  rw [div_le_iff₀ (by positivity)]
  calc ∑ aa ∈ Fintype.piFinset As, ∑ ap ∈ Ap, bad aa ap / rk aa ap
      ≤ ∑ aa ∈ Fintype.piFinset As, 2 * Ap.card * (∑ i ∈ U, X i aa / m aa + epsP) := Finset.sum_le_sum hA
    _ = 2 * Ap.card * (∑ i ∈ U, ∑ aa ∈ Fintype.piFinset As, X i aa / m aa +
          (Fintype.piFinset As).card * epsP) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * Ap.card * (∑ i ∈ U, (Fintype.piFinset As).card * K * eps i +
          (Fintype.piFinset As).card * epsP) := by
        gcongr with i hi
        exact hB i hi
    _ = (2 * K * (∑ i ∈ U, eps i) + 2 * epsP) * ((Fintype.piFinset As).card * Ap.card) := by
        rw [← Finset.mul_sum]
        ring
end Formalism.CountingSumsFrames
