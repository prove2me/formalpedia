-- Prove2me | solution 1 for ConvexRMDP.fixed_point_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:11:31.519257+00:00
-- url     : https://prove2.me/submissions/a1ddcb7c-755a-4a10-8f5e-e4839887e75a

import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Theorems.Thm_ConvexRMDP_lemma_3_1
import Theorems.Thm_ConvexRMDP_proposition_4_1_item_1
import Theorems.Thm_ConvexRMDP_display_4_3

open ConvexRMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (vt : S → ℝ) (hvt : M.regOp b vt = vt) :
    0 ≤ vt ∧
      IsGreatest ((fun v : S → ℝ => ∑ s, expB b (v s)) '' {v | v ≤ M.regOp b v ∧ 0 ≤ v})
        (∑ s, expB b (vt s)) := by
  obtain ⟨hmono, hcontr⟩ := proposition_4_1_item_1 M b hb
  have hcard_pos : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have h0_feas : (0 : S → ℝ) ≤ M.regOp b 0 := by
    intro s
    rw [Pi.zero_apply, display_4_3 M b hb 0 s]
    have hworst0 : ∀ a : A, M.worst 0 s a = 0 := by
      intro a
      unfold RMDP.worst
      have hfun0 : (fun p : S → ℝ => ∑ s', p s' * (0 : S → ℝ) s') = fun _ => (0 : ℝ) := by
        funext p
        simp
      rw [hfun0, Set.Nonempty.image_const (M.U_nonempty s a) (0 : ℝ), csInf_singleton]
    have hsum_ge_one : 1 ≤ ∑ a : A, (1 / (Fintype.card A : ℝ)) *
        Real.exp (b * M.r s a + b * M.γ * M.worst 0 s a) := by
      have hunif : (∑ _ : A, (1 / (Fintype.card A : ℝ))) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard_pos.ne']
      have hle : (∑ _ : A, (1 / (Fintype.card A : ℝ))) ≤
          ∑ a : A, (1 / (Fintype.card A : ℝ)) *
            Real.exp (b * M.r s a + b * M.γ * M.worst 0 s a) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [hworst0 a, mul_zero, add_zero]
        have hexp1 : 1 ≤ Real.exp (b * M.r s a) :=
          Real.one_le_exp (mul_nonneg hb.le (M.r_nonneg s a))
        calc 1 / (Fintype.card A : ℝ)
            = (1 / (Fintype.card A : ℝ)) * 1 := (mul_one _).symm
          _ ≤ (1 / (Fintype.card A : ℝ)) * Real.exp (b * M.r s a) :=
              mul_le_mul_of_nonneg_left hexp1 (div_nonneg zero_le_one hcard_pos.le)
      rwa [hunif] at hle
    exact div_nonneg (Real.log_nonneg hsum_ge_one) hb.le
  have hvt_nonneg : 0 ≤ vt := by
    intro s
    let gs : (S → ℝ) → ℝ := fun v => v s
    have hgs : Monotone gs := fun u w huw => huw s
    have hgreat := (lemma_3_1 (M.regOp b) ⟨M.γ, M.γ_pos.le⟩ hmono hcontr gs hgs vt hvt).2.1
    exact hgreat.2 ⟨0, h0_feas, rfl⟩
  let g : (S → ℝ) → ℝ := fun v => ∑ s, expB b (v s)
  have hg_mono : Monotone g := by
    intro u w huw
    refine Finset.sum_le_sum fun s _ => ?_
    unfold expB
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (huw s) hb.le)
  have hgreat_unr := (lemma_3_1 (M.regOp b) ⟨M.γ, M.γ_pos.le⟩ hmono hcontr g hg_mono vt hvt).2.1
  refine ⟨hvt_nonneg, ⟨⟨vt, ⟨hvt.symm.le, hvt_nonneg⟩, rfl⟩, ?_⟩⟩
  rintro _ ⟨v, ⟨hv_le, -⟩, rfl⟩
  exact hgreat_unr.2 ⟨v, hv_le, rfl⟩
