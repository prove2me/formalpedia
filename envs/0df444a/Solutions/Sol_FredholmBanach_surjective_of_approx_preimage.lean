-- Prove2me | solution 1 for FredholmBanach.surjective_of_approx_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:10:57.458975+00:00
-- url     : https://prove2.me/submissions/0640f120-712d-4895-b6cd-19ca6f989d90

import Definitions.Def_FredholmBanach_Setting

open Filter Topology Function


theorem solution {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (f : X →L[𝕜] Y) {C : ℝ} (hf : ∀ y : Y, ‖y‖ ≤ 1 → ∃ x, ‖x‖ ≤ C ∧ ‖f x - y‖ ≤ 1 / 2) :
    Surjective f := by
  -- homogeneous form
  have hC : ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ max C 0 * ‖y‖ := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set c : 𝕜 := ((‖y‖ : ℝ) : 𝕜) with hc
    have hcn : ‖c‖ = ‖y‖ := by simp [hc]
    have hc0 : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hcn; linarith
    obtain ⟨x', hx', hfx'⟩ := hf (c⁻¹ • y) (by rw [norm_smul, norm_inv, hcn, inv_mul_cancel₀ hny.ne'])
    refine ⟨c • x', ?_, ?_⟩
    · have : f (c • x') - y = c • (f x' - c⁻¹ • y) := by
        rw [map_smul, smul_sub, smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [dist_eq_norm, this, norm_smul, hcn]
      nlinarith
    · rw [norm_smul, hcn]
      nlinarith [le_max_left C 0]
  obtain C0 := le_max_right C 0
  set C := max C 0
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp only [one_div, one_mul, iterate_zero_apply, pow_zero, le_rfl]
    | succ n IH =>
      rw [iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C * ‖y‖) := fun n ↦ by
    apply le_trans (hg _).2
    calc
      C * ‖h^[n] y‖ ≤ C * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hnle n
      _ = (1 / 2) ^ n * (C * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  let x := tsum u
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp [f.map_zero]
    | succ n IH => rw [Finset.sum_range_succ, f.map_add, IH, iterate_succ_apply', sub_add]
  have : Tendsto (fun n => ∑ i ∈ Finset.range n, u i) atTop (𝓝 x) := su.hasSum.tendsto_sum_nat
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f x)) :=
    (f.continuous.tendsto _).comp this
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  have feq : f x = y - 0 := tendsto_nhds_unique L₁ L₂
  rw [sub_zero] at feq
  exact ⟨x, feq⟩

