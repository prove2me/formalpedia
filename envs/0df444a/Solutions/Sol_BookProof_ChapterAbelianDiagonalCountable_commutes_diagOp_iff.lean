-- Prove2me | solution 1 for BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T12:01:10.516304+00:00
-- url     : https://prove2.me/submissions/a3a965d7-15b6-4a97-bf85-66d7cb5556c1

-- Generated from ChapterAbelianDiagonalCountable.lean — solution of BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff
import Mathlib
import Definitions.Def_ChapterAbelianDiagonalCountable
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_comm
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_coordUnit_apply
import Theorems.Thm_BookProof_ChapterAbelianDiagonalCountable_diagOp_coordUnit_eq
import Definitions.Def_ChapterAtomicDiagonalModel
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
open BookProof.ChapterAtomicDiagonalModel
open BookProof.ChapterAbelianDiagonalCountable



open scoped ENNReal

noncomputable section


@[simp] private theorem norm_atom (i : ℕ) : ‖atom i‖ = 1 := by
  rw [atom, lp.norm_single (by norm_num)]
  simp

set_option maxHeartbeats 1000000 in

@[simp] private theorem diagOp_apply (d : EllInf) (f : Ell2C) (i : ℕ) :
    ((diagOp d f : Ell2C) : ℕ → ℂ) i = (d : ℕ → ℂ) i * (f : ℕ → ℂ) i := rfl

theorem solution (T : Ell2C →L[ℂ] Ell2C) :
    (∀ d : EllInf, T.comp (diagOp d) = (diagOp d).comp T) ↔ ∃ d : EllInf, T = diagOp d := by
  constructor
  · intro hT
    -- the diagonal entries
    set c : ℕ → ℂ := fun i => ((T (atom i) : Ell2C) : ℕ → ℂ) i with hc
    have hbdd : ∀ i, ‖c i‖ ≤ ‖T‖ := by
      intro i
      calc ‖c i‖ ≤ ‖T (atom i)‖ := lp.norm_apply_le_norm (by simp) _ i
        _ ≤ ‖T‖ * ‖atom i‖ := T.le_opNorm _
        _ = ‖T‖ := by rw [norm_atom, mul_one]
    have hmem : Memℓp c ∞ := by
      refine memℓp_infty ⟨‖T‖, ?_⟩
      rintro x ⟨i, rfl⟩
      exact hbdd i
    refine ⟨⟨c, hmem⟩, ?_⟩
    ext f i
    -- restrict to the `i`-th coordinate using the projection `coordUnit i`
    have hcomm := congrArg (fun S => ((S f : Ell2C) : ℕ → ℂ) i) (hT (coordUnit i))
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hcomm
    have hleft : T (diagOp (coordUnit i) f) = (f : ℕ → ℂ) i • T (atom i) := by
      rw [diagOp_coordUnit_eq, map_smul]
    rw [hleft] at hcomm
    have hright : ((diagOp (coordUnit i) (T f) : Ell2C) : ℕ → ℂ) i
        = ((T f : Ell2C) : ℕ → ℂ) i := by
      rw [diagOp_coordUnit_apply]; simp
    rw [hright] at hcomm
    have hval : ((f : ℕ → ℂ) i • T (atom i) : Ell2C) i = (f : ℕ → ℂ) i * c i := rfl
    rw [hval] at hcomm
    rw [← hcomm, diagOp_apply]
    simp [mul_comm]
  · rintro ⟨d, rfl⟩
    exact fun e => diagOp_comm d e
