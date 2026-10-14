-- Prove2me | solution 1 for BookProof.ChapterH5.shift_pow_sub_pow_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T16:58:54.561692+00:00
-- url     : https://prove2.me/submissions/8b58926f-468c-499f-a9d9-6059167b295c

-- Generated from ChapterH5.lean — solution of BookProof.ChapterH5.shift_pow_sub_pow_mem
import Mathlib
import Definitions.Def_ChapterH5
import Theorems.Thm_BookProof_ChapterH5_pow_apply_mem_krylovSpan
import Theorems.Thm_BookProof_ChapterH5_krylovSpan_mono
import Theorems.Thm_BookProof_ChapterH5_krylovSpan_map_le
open BookProof.ChapterH5



noncomputable section



variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

set_option maxHeartbeats 1000000 in
theorem solution (H : E →ₗ[K] E) (γ : K) (v : E) (m : ℕ) :
    (((H - γ • 1) ^ m) v) - ((H ^ m) v) ∈ krylovSpan H v m := by

  induction m with
  | zero => simp
  | succ m ih =>
    set A : E →ₗ[K] E := H - γ • 1 with hA
    have hAstep : ((A ^ (m + 1)) v) = A ((A ^ m) v) := by
      rw [pow_succ']; rfl
    have hHstep : ((H ^ (m + 1)) v) = H ((H ^ m) v) := by
      rw [pow_succ']; rfl
    set w : E := ((A ^ m) v) - ((H ^ m) v) with hw
    have hwmem : w ∈ krylovSpan H v m := ih
    have hAeq : A ((A ^ m) v) = H ((H ^ m) v) + (H w - γ • ((A ^ m) v)) := by
      have hAapply : ∀ y : E, A y = H y - γ • y := by
        intro y; rw [hA]; simp
      rw [hAapply, hw]
      simp only [map_sub]
      abel
    rw [hAstep, hHstep, hAeq]
    have h1 : H w ∈ krylovSpan H v (m + 1) :=
      krylovSpan_map_le m ⟨w, hwmem, rfl⟩
    have h2 : ((A ^ m) v) ∈ krylovSpan H v (m + 1) := by
      have : ((A ^ m) v) = w + ((H ^ m) v) := by rw [hw]; abel
      rw [this]
      exact Submodule.add_mem _
        (krylovSpan_mono (Nat.le_succ m) hwmem)
        (pow_apply_mem_krylovSpan (Nat.lt_succ_self m))
    have : H ((H ^ m) v) + (H w - γ • ((A ^ m) v)) - H ((H ^ m) v)
        = H w - γ • ((A ^ m) v) := by abel
    rw [this]
    exact Submodule.sub_mem _ h1 (Submodule.smul_mem _ _ h2)
