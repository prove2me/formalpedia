-- Prove2me | solution 1 for ContJRP.Align.lemma_2_1_easy_regime
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:07:29.595199+00:00
-- url     : https://prove2.me/submissions/e7be3bce-d7c1-4cf9-9368-0746d5c05d6d

import Mathlib
import Definitions.Def_ContJRP_Align_Model
import Definitions.Def_ContJRP_Align_Alignment
import Definitions.Def_ContJRP_Align_Policy
import Theorems.Thm_ContJRP_Align_lemma_1_2_density

open ContJRP.Align
open Classical

theorem jrp21_min (K H T : ℝ) (hK : 0 < K) (hH : 0 < H) (hT : 0 < T) :
    eoqCost K H (Real.sqrt (K / H)) ≤ eoqCost K H T := by
  set s := Real.sqrt (K / H) with hsdef
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos hK hH)
  have hss : s * s = K / H := Real.mul_self_sqrt (div_nonneg hK.le hH.le)
  have hKs : K = H * (s * s) := by rw [hss]; field_simp
  unfold eoqCost
  rw [hKs]
  have e1 : H * (s * s) / s = H * s := by field_simp
  rw [e1, div_add' _ _ _ hT.ne', le_div_iff₀ hT]
  nlinarith [mul_nonneg hH.le (sq_nonneg (T - s))]

theorem jrp21_density_tendsto {ι : Type*} (s : Finset ι) (T : ι → ℝ) (hT : ∀ i ∈ s, 0 < T i) :
    Filter.Tendsto (fun Δ : ℝ => (numOrders s T Δ : ℝ) / Δ) Filter.atTop
      (nhds (orderDensity s T)) := by
  have h := lemma_1_2_density s T hT
  unfold orderDensity
  rw [h.limUnder_eq]
  exact h

theorem jrp21_card_multiples (t Δ : ℝ) (ht : 0 < t) :
    (multiplesUpTo t Δ).card = ⌊Δ / t⌋₊ + 1 := by
  unfold multiplesUpTo
  rw [Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  have := mul_right_cancel₀ (ne_of_gt ht) hab
  exact_mod_cast this

theorem solution {n : ℕ} [NeZero n] (K0 : ℝ) (K H : Fin n → ℝ) (hK0 : 0 < K0)
    (hK : ∀ i, 0 < K i) (hH : ∀ i, 0 < H i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (Tstar : Fin n → ℝ) (hTstar : ∀ i, 0 < Tstar i)
    (OPT : ℝ) (hOPT1 : totalCost K0 K H Tstar ≤ OPT) (hOPT2 : OPT ≤ 2 * totalCost K0 K H Tstar)
    (heasy : (n : ℝ) / ε * (K0 / OPT) ≤ tmin Tstar) :
    totalCost K0 K H (easyPolicy K0 K H) ≤
        ∑ i, eoqCost (K0 + K i) (H i) (easyPolicy K0 K H i) ∧
      ∑ i, eoqCost (K0 + K i) (H i) (easyPolicy K0 K H i) ≤
        (1 + 2 * ε) * totalCost K0 K H Tstar := by
  set E := easyPolicy K0 K H with hE
  have hEpos : ∀ i, 0 < E i := fun i =>
    Real.sqrt_pos.mpr (div_pos (by linarith [hK i]) (hH i))
  have hplus : ∀ i (T : ℝ), eoqCost (K0 + K i) (H i) T = K0 * (1 / T) + eoqCost (K i) (H i) T := by
    intro i T; unfold eoqCost; ring
  have hsplit : ∀ T : Fin n → ℝ, ∑ i, eoqCost (K0 + K i) (H i) (T i) =
      K0 * ∑ i, 1 / T i + ∑ i, eoqCost (K i) (H i) (T i) := by
    intro T
    simp_rw [hplus, Finset.sum_add_distrib, Finset.mul_sum]
  have htmin_pos : 0 < tmin Tstar := by
    unfold tmin
    rw [Finset.lt_inf'_iff]
    intro i _; exact hTstar i
  have heoq_pos : ∀ i (T : ℝ), 0 < T → 0 < eoqCost (K i) (H i) T := by
    intro i T hT
    unfold eoqCost
    have := hK i; have := hH i
    positivity
  refine ⟨?_, ?_⟩
  · -- `J(E) ≤ K₀ Σ 1/E_i`
    have hdE := jrp21_density_tendsto Finset.univ E (fun i _ => hEpos i)
    have hup : Filter.Tendsto (fun Δ : ℝ => ∑ i, 1 / E i + (n : ℝ) / Δ) Filter.atTop
        (nhds (∑ i, 1 / E i)) := by
      have := (tendsto_const_nhds (x := (n : ℝ))).div_atTop Filter.tendsto_id
      simpa using (tendsto_const_nhds (x := ∑ i, 1 / E i)).add this
    have hle : orderDensity Finset.univ E ≤ ∑ i, 1 / E i := by
      apply le_of_tendsto_of_tendsto hdE hup
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
      have h1 : numOrders Finset.univ E Δ ≤ ∑ i, (multiplesUpTo (E i) Δ).card := by
        unfold numOrders; exact Finset.card_biUnion_le
      have h2 : ((numOrders Finset.univ E Δ : ℕ) : ℝ) ≤ ∑ i, (Δ / E i + 1) := by
        refine le_trans (b := ((∑ i, (multiplesUpTo (E i) Δ).card : ℕ) : ℝ))
          (by exact_mod_cast h1) ?_
        push_cast
        apply Finset.sum_le_sum
        intro i _
        rw [jrp21_card_multiples _ _ (hEpos i)]
        push_cast
        have := Nat.floor_le (div_nonneg hΔ.le (hEpos i).le)
        linarith
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] at h2
      rw [div_le_iff₀ hΔ, add_mul, div_mul_cancel₀ _ hΔ.ne', Finset.sum_mul]
      have : ∑ i, Δ / E i = ∑ i, 1 / E i * Δ := by
        apply Finset.sum_congr rfl; intro i _; ring
      linarith
    rw [hsplit]
    unfold totalCost jointCost
    have := mul_le_mul_of_nonneg_left hle hK0.le
    linarith
  · -- second inequality
    have hdT := jrp21_density_tendsto Finset.univ Tstar (fun i _ => hTstar i)
    have hod_nonneg : 0 ≤ orderDensity Finset.univ Tstar := by
      apply ge_of_tendsto hdT
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with Δ hΔ
      positivity
    have hsum_pos : 0 < ∑ i, eoqCost (K i) (H i) (Tstar i) :=
      Finset.sum_pos (fun i _ => heoq_pos i _ (hTstar i)) Finset.univ_nonempty
    have hF : totalCost K0 K H Tstar =
        K0 * orderDensity Finset.univ Tstar + ∑ i, eoqCost (K i) (H i) (Tstar i) := rfl
    have hFpos : 0 < totalCost K0 K H Tstar := by
      rw [hF]; have := mul_nonneg hK0.le hod_nonneg; linarith
    have hOPT : 0 < OPT := lt_of_lt_of_le hFpos hOPT1
    -- each `E_i` minimizes the overloaded cost
    have h1 : ∑ i, eoqCost (K0 + K i) (H i) (E i) ≤ ∑ i, eoqCost (K0 + K i) (H i) (Tstar i) := by
      apply Finset.sum_le_sum
      intro i _
      exact jrp21_min (K0 + K i) (H i) (Tstar i) (by linarith [hK i]) (hH i) (hTstar i)
    have h2 : ∑ i, 1 / Tstar i ≤ (n : ℝ) / tmin Tstar := by
      have : ∀ i, 1 / Tstar i ≤ 1 / tmin Tstar := by
        intro i
        apply one_div_le_one_div_of_le htmin_pos
        unfold tmin; exact Finset.inf'_le _ (Finset.mem_univ i)
      calc ∑ i, 1 / Tstar i ≤ ∑ _i : Fin n, 1 / tmin Tstar := Finset.sum_le_sum (fun i _ => this i)
        _ = (n : ℝ) / tmin Tstar := by simp [div_eq_mul_inv]
    have h3 : K0 * ((n : ℝ) / tmin Tstar) ≤ ε * OPT := by
      have := heasy
      rw [div_mul_div_comm, div_le_iff₀ (mul_pos hε0 hOPT)] at this
      rw [mul_div_assoc', div_le_iff₀ htmin_pos]
      nlinarith
    rw [hsplit, hsplit] at h1
    rw [hsplit]
    have h6 : ε * OPT ≤ ε * (2 * totalCost K0 K H Tstar) := mul_le_mul_of_nonneg_left hOPT2 hε0.le
    have h4 := mul_le_mul_of_nonneg_left h2 hK0.le
    have h5 : ∑ i, eoqCost (K i) (H i) (Tstar i) ≤ totalCost K0 K H Tstar := by
      rw [hF]; have := mul_nonneg hK0.le hod_nonneg; linarith
    linarith
