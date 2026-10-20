-- Prove2me | solution 2 for BookProof.BrstUnboundedLeakage.leakage_le_of_physical
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:29:43.847441+00:00
-- url     : https://prove2.me/submissions/867173a6-c9ca-4f8a-bca2-ad7607d53d7f

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.leakage_le_of_physical
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_hasDerivAt_stoneU_const_sub_apply
import Theorems.Thm_BookProof_ChapterStoneResolvent_UnboundedSelfAdjoint_stoneU_op
import Theorems.Thm_BookProof_BrstUnboundedLeakage_hasDerivAt_flow
import Theorems.Thm_BookProof_BrstUnboundedLeakage_norm_omega_stoneU_eq
import Theorems.Thm_BookProof_BrstUnboundedLeakage_defect_orbit_le
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem aux_duhamel (B : H →L[ℂ] H) (t : ℝ) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (s : ℝ) :
    HasDerivAt (fun u : ℝ => T.stoneU (t - u) (flow B u x))
      (T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩))) s := by
  have h := BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply (t := t) T
    (BookProof.BrstUnboundedLeakage.hasDerivAt_flow B x s) (hdom s)
  convert h using 1
  have h2 := T.stoneU_op (t - s) ⟨flow B s x, hdom s⟩
  simp only at h2
  rw [h2, ← map_smul, ← map_add]
  congr 1
  rw [smul_sub]
  simp only [neg_smul, sub_neg_eq_add]
  abel

theorem aux_flow_zero (B : H →L[ℂ] H) (x : H) : flow B 0 x = x := by
  simp [flow]

theorem aux_norm_le {B : H →L[ℂ] H} (t : ℝ) (ht : 0 ≤ t) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖flow B t x - T.stoneU t x‖ ≤ K * t := by
  have key := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun u : ℝ => T.stoneU (t - u) (flow B u x))
    (f' := fun s => T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩)))
    (a := 0) (b := t) (C := K)
    (fun s _ => (aux_duhamel T B t x hdom s).hasDerivWithinAt)
    (fun s hs => by
      rw [T.norm_stoneU_apply, norm_smul, norm_neg, Complex.norm_I, one_mul, norm_sub_rev]
      exact hK s (Set.Ico_subset_Icc_self hs))
    t ⟨ht, le_rfl⟩
  simpa [aux_flow_zero] using key

theorem aux_leakage_le {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K) :
    ‖Om (flow B t x)‖ ≤ ‖Om x‖ + ‖Om‖ * (K * t) := by
  have h1 : Om (flow B t x) = Om (T.stoneU t x) + Om (flow B t x - T.stoneU t x) := by
    rw [map_sub]; abel
  rw [h1]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [BookProof.BrstUnboundedLeakage.norm_omega_stoneU_eq T hcomm]
  · exact (Om.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (aux_norm_le T t ht x hdom K hK) (norm_nonneg _))


open BookProof BookProof.BrstUnboundedLeakage in
theorem solution {B Om : H →L[ℂ] H}
    (hcomm : ∀ (s : ℝ) (y : H), Om (T.stoneU s y) = T.stoneU s (Om y))
    (t : ℝ) (ht : 0 ≤ t) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (K : ℝ)
    (hK : ∀ s ∈ Set.Icc (0 : ℝ) t, ‖T.op ⟨flow B s x, hdom s⟩ - B (flow B s x)‖ ≤ K)
    (hOm : Om x = 0) :
    ‖Om (flow B t x)‖ ≤ ‖Om‖ * (K * t) :=
  by simpa [hOm] using aux_leakage_le T hcomm t ht x hdom K hK
