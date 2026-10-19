-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:05:43.2859+00:00
-- url     : https://prove2.me/submissions/bae863e3-72c5-4ac9-80aa-07733ff93518

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.affH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_norm_basisState
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_coord_succ_succ
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_le_amp
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in
theorem solution {κ c : ℝ} (hκ : 0 < κ) (hc : 0 ≤ c) (C : ℝ) :
    ∃ n : ℕ, ‖(basisState κ c n : L2I ℕ)‖ = 1
      ∧ C < ‖(affH hκ.le hc (basisState κ c n) : L2I ℕ)‖ := by

  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|C| + 1) / κ)
  refine ⟨n, norm_basisState κ c n, ?_⟩
  have hb : ‖((affH hκ.le hc (basisState κ c n) : L2I ℕ) : ℕ → ℂ) (n + 2)‖
      ≤ ‖(affH hκ.le hc (basisState κ c n) : L2I ℕ)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ _
  rw [affH_coord_succ_succ] at hb
  have hnv : ‖Complex.I * ((amp κ n : ℝ) : ℂ)‖ = amp κ n := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (amp_nonneg hκ.le n)]
  rw [hnv] at hb
  have hlow := le_amp hκ.le n
  have hgt : 2 * (|C| + 1) / κ < (n : ℝ) := hn
  have hmul : 2 * (|C| + 1) < κ * (n : ℝ) := by
    rw [div_lt_iff₀ hκ] at hgt
    linarith [hgt]
  have hC : C ≤ |C| := le_abs_self C
  nlinarith
