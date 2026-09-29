-- Prove2me | solution 2 for BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:28:45.151984+00:00
-- url     : https://prove2.me/submissions/a232acd8-e009-487c-9fcd-1c078f4b008c

import Definitions.Def_ChapterSirkMultiShift
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace SirkMultiAux
open BookProof.ChapterH5 BookProof.ChapterSirkMultiShift
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {H : E →ₗ[K] E} {v : E}

private theorem pow_apply_mem_krylovSpan {i m : ℕ} (hi : i < m) :
    (H ^ i) v ∈ krylovSpan H v m :=
  Submodule.subset_span ⟨i, hi, rfl⟩

private theorem krylovSpan_mono {m n : ℕ} (hmn : m ≤ n) :
    krylovSpan H v m ≤ krylovSpan H v n :=
  Submodule.span_mono fun _ ⟨i, hi, hx⟩ => ⟨i, lt_of_lt_of_le hi hmn, hx⟩

private theorem krylovSpan_map_le (m : ℕ) :
    Submodule.map H (krylovSpan H v m) ≤ krylovSpan H v (m + 1) := by
  rw [Submodule.map_le_iff_le_comap, krylovSpan]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, hi, rfl⟩
  have : H ((H ^ i) v) = (H ^ (i + 1)) v := by
    rw [pow_succ']
    rfl
  have hx : H ((H ^ i) v) ∈ krylovSpan H v (m + 1) := by
    rw [this]
    exact pow_apply_mem_krylovSpan (Nat.succ_lt_succ hi)
  exact hx

private theorem mem_seqSpan (u : ℕ → E) {i m : ℕ} (hi : i < m) :
    u i ∈ seqSpan (K := K) u m :=
  Submodule.subset_span ⟨i, hi, rfl⟩

private theorem seqSpan_mono (u : ℕ → E) {m n : ℕ} (hmn : m ≤ n) :
    seqSpan (K := K) u m ≤ seqSpan (K := K) u n :=
  Submodule.span_mono fun _ ⟨i, hi, hx⟩ => ⟨i, lt_of_lt_of_le hi hmn, hx⟩

private theorem seqSpan_le_krylovSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) :
    seqSpan (K := K) u m ≤ krylovSpan H v m := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, hi, rfl⟩
  have hsplit : u i = (u i - (H ^ i) v) + (H ^ i) v := by abel
  rw [hsplit]
  exact Submodule.add_mem _
    (krylovSpan_mono (le_of_lt hi) (hu i))
    (pow_apply_mem_krylovSpan hi)

private theorem pow_mem_seqSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (i : ℕ) :
    (H ^ i) v ∈ seqSpan (K := K) u (i + 1) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hlow : krylovSpan H v i ≤ seqSpan (K := K) u (i + 1) := by
      refine Submodule.span_le.mpr ?_
      rintro x ⟨j, hj, rfl⟩
      exact seqSpan_mono u (by omega) (ih j hj)
    have h1 : u i ∈ seqSpan (K := K) u (i + 1) := mem_seqSpan u (Nat.lt_succ_self i)
    have h2 : u i - (H ^ i) v ∈ seqSpan (K := K) u (i + 1) := hlow (hu i)
    have : (H ^ i) v = u i - (u i - (H ^ i) v) := by abel
    rw [this]
    exact Submodule.sub_mem _ h1 h2

private theorem triangularSpan_eq_krylovSpan (u : ℕ → E)
    (hu : ∀ i, u i - (H ^ i) v ∈ krylovSpan H v i) (m : ℕ) :
    seqSpan (K := K) u m = krylovSpan H v m := by
  refine le_antisymm (seqSpan_le_krylovSpan u hu m) ?_
  refine Submodule.span_le.mpr ?_
  rintro x ⟨i, hi, rfl⟩
  exact seqSpan_mono u (by omega) (pow_mem_seqSpan u hu i)

@[simp] private theorem multiShiftSeq_zero (H : E →ₗ[K] E) (z : ℕ → K) (v : E) :
    multiShiftSeq H z v 0 = v := rfl

private theorem multiShiftSeq_succ (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) :
    multiShiftSeq H z v (k + 1) = H (multiShiftSeq H z v k) - z k • multiShiftSeq H z v k := by
  change (H - z k • 1) (multiShiftSeq H z v k) = _
  simp

private theorem multiShiftSeq_sub_pow_mem (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (k : ℕ) :
    multiShiftSeq H z v k - (H ^ k) v ∈ krylovSpan H v k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hHstep : ((H ^ (k + 1)) v) = H ((H ^ k) v) := by rw [pow_succ']; rfl
    set d : E := multiShiftSeq H z v k - (H ^ k) v with hd
    have hdmem : d ∈ krylovSpan H v k := ih
    have hwmem : multiShiftSeq H z v k ∈ krylovSpan H v (k + 1) := by
      have : multiShiftSeq H z v k = d + (H ^ k) v := by rw [hd]; abel
      rw [this]
      exact Submodule.add_mem _
        (krylovSpan_mono (Nat.le_succ k) hdmem)
        (pow_apply_mem_krylovSpan (Nat.lt_succ_self k))
    have hHd : H d ∈ krylovSpan H v (k + 1) := krylovSpan_map_le k ⟨d, hdmem, rfl⟩
    have hrw : multiShiftSeq H z v (k + 1) - (H ^ (k + 1)) v
        = H d - z k • multiShiftSeq H z v k := by
      rw [multiShiftSeq_succ, hHstep, hd, map_sub]
      abel
    rw [hrw]
    exact Submodule.sub_mem _ hHd (Submodule.smul_mem _ _ hwmem)

private theorem krylov_multiShift_eq_standard (H : E →ₗ[K] E) (z : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i} = krylovSpan H v m :=
  triangularSpan_eq_krylovSpan (H := H) (v := v) (multiShiftSeq H z v)
    (multiShiftSeq_sub_pow_mem H z v) m

private theorem krylov_multiShift_span_eq_of_shifts (H : E →ₗ[K] E) (z z' : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i}
      = Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z' v i} := by
  rw [krylov_multiShift_eq_standard, krylov_multiShift_eq_standard]

private theorem multiShiftSeq_const (H : E →ₗ[K] E) (γ : K) (v : E) (k : ℕ) :
    multiShiftSeq H (fun _ => γ) v k = noInversionSeq H γ v k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [multiShiftSeq, ih]; rfl

end SirkMultiAux

-- Generated from ChapterSirkMultiShift.lean — theorem BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
open BookProof.ChapterSirkMultiShift










noncomputable section


open BookProof.ChapterH5

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]





variable {H : E →ₗ[K] E} {v : E}
open SirkMultiAux

theorem solution (H : E →ₗ[K] E) (z z' : ℕ → K) (v : E) (m : ℕ) :
    Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z v i}
      = Submodule.span K {x | ∃ i < m, x = multiShiftSeq H z' v i} := by
  rw [krylov_multiShift_eq_standard, krylov_multiShift_eq_standard]

#print axioms solution
