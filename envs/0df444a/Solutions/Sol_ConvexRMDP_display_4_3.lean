-- Prove2me | solution 1 for ConvexRMDP.display_4_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-11T23:08:59.150268+00:00
-- url     : https://prove2.me/submissions/e56385e3-6fd3-4b2d-beb9-32354c81732d

import Definitions.Def_ConvexRMDP_RMDP_regOp
import Theorems.Thm_ConvexRMDP_lemma_4_1

open ConvexRMDP

theorem solution {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) (v : S → ℝ) (s : S) :
    M.regOp b v s = Real.log (∑ a, (1 / (Fintype.card A : ℝ)) *
      Real.exp (b * M.r s a + b * M.γ * M.worst v s a)) / b := by
  let q₀ : A → ℝ := fun _ => 1 / (Fintype.card A : ℝ)
  let y : A → ℝ := fun a => M.r s a + M.γ * M.worst v s a
  have hcard_pos : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hq₀ : q₀ ∈ stdSimplex ℝ A := by
    refine ⟨fun _ => div_nonneg zero_le_one hcard_pos.le, ?_⟩
    dsimp [q₀]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hcard_pos.ne']
  have hset : ((fun π : A → ℝ => ∑ a, π a * y a - kl π q₀ / b) '' stdSimplex ℝ A) =
      {t | ∃ q ∈ stdSimplex ℝ A, AbsCont q q₀ ∧ t = ∑ a, q a * y a - kl q q₀ / b} := by
    ext t
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q, hq, fun _ ha => False.elim ((div_pos one_pos hcard_pos).ne' ha), rfl⟩
    · rintro ⟨q, hq, -, rfl⟩
      exact ⟨q, hq, rfl⟩
  have hdv := lemma_4_1 b hb q₀ hq₀ y
  unfold RMDP.regOp
  change sSup ((fun π : A → ℝ => ∑ a, π a * y a - kl π q₀ / b) '' stdSimplex ℝ A) = _
  rw [hset, hdv.isLUB.csSup_eq ⟨_, hdv.1⟩]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  dsimp [q₀, y]
  congr 2
  ring
