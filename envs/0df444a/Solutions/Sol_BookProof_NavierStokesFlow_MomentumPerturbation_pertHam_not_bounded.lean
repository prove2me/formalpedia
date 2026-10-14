-- Prove2me | solution 1 for BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:08.808661+00:00
-- url     : https://prove2.me/submissions/03c1f4ad-e72e-479d-87e8-a83c27954ddf

-- Generated from ChapterNavierStokesMomentumPerturbation.lean — solution of BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_rankTwo_norm_le
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_eState_mem_maxDom
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_norm_eState
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_diagMax_eState
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation





open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}

variable {ι : Type*}


@[simp] private theorem pertHam_apply (c : ι → ℝ) (u w : L2I ι) (x : maxDom c) :
    pertHam c u w x = diagMax c x + rankTwo u w (x : L2I ι) := rfl

set_option maxHeartbeats 1000000 in
theorem solution :
    ¬ ∃ C : ℝ, ∀ x : maxDom linSymbol,
      ‖pertHam linSymbol (eState 0) (eState 1) x‖ ≤ C * ‖(x : L2I ℕ)‖ := by

  rintro ⟨C, hC⟩
  obtain ⟨k, hk⟩ := exists_nat_gt (C + 2)
  have hx := hC ⟨eState k, eState_mem_maxDom k⟩
  have hnorm : ‖((⟨eState k, eState_mem_maxDom k⟩ : maxDom linSymbol) : L2I ℕ)‖ = 1 :=
    norm_eState k
  rw [hnorm, mul_one, pertHam_apply] at hx
  have hlow : ‖(diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)‖
      ≤ ‖(diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)
          + rankTwo (eState 0) (eState 1) (eState k)‖
        + ‖rankTwo (eState 0) (eState 1) (eState k)‖ := by
    calc ‖(diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)‖
        = ‖((diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)
            + rankTwo (eState 0) (eState 1) (eState k))
            - rankTwo (eState 0) (eState 1) (eState k)‖ := by
          rw [add_sub_cancel_right]
      _ ≤ ‖(diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)
            + rankTwo (eState 0) (eState 1) (eState k)‖
          + ‖rankTwo (eState 0) (eState 1) (eState k)‖ := norm_sub_le _ _
  have hdiagnorm : ‖(diagMax linSymbol ⟨eState k, eState_mem_maxDom k⟩ : L2I ℕ)‖
      = (k : ℝ) + 1 := by
    rw [diagMax_eState, norm_smul, norm_eState, mul_one]
    simp only [linSymbol, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hpert : ‖rankTwo (eState 0) (eState 1) (eState k)‖ ≤ 2 := by
    have h := rankTwo_norm_le (eState 0) (eState 1) (eState k)
    rw [norm_eState, norm_eState, norm_eState] at h
    linarith
  rw [hdiagnorm] at hlow
  linarith
