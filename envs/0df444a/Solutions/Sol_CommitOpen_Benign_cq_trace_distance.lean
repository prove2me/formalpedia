-- Prove2me | solution 1 for CommitOpen.Benign.cq_trace_distance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:57:40.484651+00:00
-- url     : https://prove2.me/submissions/277f0140-2da9-45e3-9dda-e30ddc8c9bb5

import Mathlib
import Definitions.Def_CommitOpen_Benign_Model

set_option linter.unusedSectionVars false

namespace X5CO

open CommitOpen.Benign Matrix
open scoped MatrixOrder ComplexOrder

variable {T ι : Type} [Fintype T] [DecidableEq T] [Fintype ι] [DecidableEq ι]

def bd (X : T → Matrix ι ι ℂ) : Matrix (T × ι) (T × ι) ℂ :=
  Matrix.of fun p q => if p.1 = q.1 then X p.1 p.2 q.2 else 0

theorem bd_mul (X Y : T → Matrix ι ι ℂ) : bd X * bd Y = bd (fun t => X t * Y t) := by
  ext ⟨t, a⟩ ⟨u, c⟩
  simp only [bd, mul_apply, of_apply, Fintype.sum_prod_type]
  by_cases h : t = u
  · subst h; simp
  · simp [h]

theorem bd_ct (X : T → Matrix ι ι ℂ) : (bd X)ᴴ = bd (fun t => (X t)ᴴ) := by
  ext p q
  simp only [bd, conjTranspose_apply, of_apply]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

theorem bd_trace (X : T → Matrix ι ι ℂ) : trace (bd X) = ∑ t, trace (X t) := by
  simp [bd, trace, Fintype.sum_prod_type]

theorem bd_psd (X : T → Matrix ι ι ℂ) (h : ∀ t, (X t).PosSemidef) : (bd X).PosSemidef := by
  have hR : bd X = (bd fun t => CFC.sqrt (X t))ᴴ * bd fun t => CFC.sqrt (X t) := by
    rw [bd_ct, bd_mul]
    congr 1; funext t
    have h0 : (0 : Matrix ι ι ℂ) ≤ X t := Matrix.nonneg_iff_posSemidef.mpr (h t)
    have hsa : (CFC.sqrt (X t))ᴴ = CFC.sqrt (X t) := (CFC.sqrt_nonneg (X t)).isSelfAdjoint.star_eq
    rw [hsa, CFC.sqrt_mul_sqrt_self (X t) h0]
  rw [hR]; exact Matrix.posSemidef_conjTranspose_mul_self _

theorem traceNorm_bd (X : T → Matrix ι ι ℂ) :
    WildeQIT.traceNorm (bd X) = ∑ t, WildeQIT.traceNorm (X t) := by
  unfold WildeQIT.traceNorm
  have hs : CFC.sqrt ((bd X)ᴴ * bd X) = bd fun t => CFC.sqrt ((X t)ᴴ * X t) := by
    refine CFC.sqrt_unique ?_ ?_
    · rw [bd_mul, bd_ct, bd_mul]
      congr 1; funext t
      exact CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr
        (Matrix.posSemidef_conjTranspose_mul_self _))
    · exact Matrix.nonneg_iff_posSemidef.mpr (bd_psd _ fun t =>
        Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
  rw [hs, bd_trace, Complex.re_sum]

theorem traceNorm_smul {n : Type} [Fintype n] [DecidableEq n] (r : ℝ) (hr : 0 ≤ r)
    (Y : Matrix n n ℂ) : WildeQIT.traceNorm ((r : ℂ) • Y) = r * WildeQIT.traceNorm Y := by
  unfold WildeQIT.traceNorm
  have hs : CFC.sqrt (((r : ℂ) • Y)ᴴ * ((r : ℂ) • Y)) = (r : ℂ) • CFC.sqrt (Yᴴ * Y) := by
    refine CFC.sqrt_unique ?_ ?_
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, CFC.sqrt_mul_sqrt_self _
        (Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self _))]
      rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1; simp [Complex.conj_ofReal]
    · rw [Matrix.nonneg_iff_posSemidef]
      exact (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).smul (by exact_mod_cast hr)
  rw [hs, trace_smul, smul_eq_mul, Complex.re_ofReal_mul]

theorem cq_eq {m k : ℕ} (ψ : Test m k → EuclideanSpace ℂ ι) :
    cqState ψ = bd fun t => (testProb m k t : ℂ) • pureState (ψ t) := by
  ext p q; simp only [cqState, bd, of_apply]; split_ifs with h
  · rfl
  · rfl

theorem cq_td {m k : ℕ} (ψ ψ' : Test m k → EuclideanSpace ℂ ι) :
    traceDistance (cqState ψ) (cqState ψ') =
      ∑ t, testProb m k t * traceDistance (pureState (ψ t)) (pureState (ψ' t)) := by
  have hp : ∀ t, 0 ≤ testProb m k t := fun t => by unfold testProb; positivity
  unfold traceDistance
  rw [cq_eq, cq_eq]
  have : (bd fun t => (testProb m k t : ℂ) • pureState (ψ t)) -
      (bd fun t => (testProb m k t : ℂ) • pureState (ψ' t)) =
      bd fun t => (testProb m k t : ℂ) • (pureState (ψ t) - pureState (ψ' t)) := by
    ext p q; simp only [bd, of_apply, Matrix.sub_apply]; split_ifs <;> simp [mul_sub]
  rw [this, traceNorm_bd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [traceNorm_smul _ (hp t)]; ring

end X5CO

open CommitOpen.Benign in
theorem solution {m k : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (ψ ψ' : Test m k → EuclideanSpace ℂ ι) :
    traceDistance (cqState ψ) (cqState ψ') =
      ∑ t, testProb m k t * traceDistance (pureState (ψ t)) (pureState (ψ' t)) :=
  X5CO.cq_td ψ ψ'
