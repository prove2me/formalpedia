-- Prove2me | solution 1 for BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:30:03.89436+00:00
-- url     : https://prove2.me/submissions/639d805e-e188-4807-b313-ea300d854205

-- Generated from ChapterSirkTrotterKato.lean — solution of BookProof.ChapterSirkTrotterKato.trotterKato_uniform_of_mem_range
import Mathlib
import Definitions.Def_ChapterSirkTrotterKato
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_norm_res_stoneU_sub_stoneU_res_le
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_tendsto_uniformly_on_isCompact_of_tendsto
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_norm_resDiff_apply_le
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_tendsto_resDiff
import Theorems.Thm_BookProof_ChapterSirkTrotterKato_isCompact_orbit
open BookProof.ChapterSirkTrotterKato











noncomputable section

open Filter Topology Asymptotics
open scoped InnerProductSpace


open BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]













variable (T : UnboundedSelfAdjoint H) (S : ℕ → UnboundedSelfAdjoint H)

set_option maxHeartbeats 1000000 in
theorem solution (hres : StrongResolventConvergence T S)
    (w : T.domain) {T₀ : ℝ} (hT₀ : 0 ≤ T₀) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t : ℝ, |t| ≤ T₀ →
      ‖(S n).stoneU t (T.resCLM 1 (w : H)) - T.stoneU t (T.resCLM 1 (w : H))‖ ≤ ε := by

  set eps : ℝ := ε / (2 + T₀) with heps
  have hepspos : 0 < eps := by
    have : (0 : ℝ) < 2 + T₀ := by linarith
    positivity
  have hK1 := isCompact_orbit T (w : H) T₀
  have hK2 := isCompact_orbit T (T.shift 1 w) T₀
  have hb1 := tendsto_uniformly_on_isCompact_of_tendsto (norm_resDiff_apply_le T S)
    (tendsto_resDiff T S hres) hK1 hepspos
  have hb2 := tendsto_uniformly_on_isCompact_of_tendsto (norm_resDiff_apply_le T S)
    (tendsto_resDiff T S hres) hK2 hepspos
  filter_upwards [hb1, hb2] with n hn1 hn2 t ht
  -- the three terms
  have hmem0 : (w : H) ∈ (fun s : ℝ => T.stoneU s (w : H)) '' Set.Icc (-T₀) T₀ := by
    refine ⟨0, ⟨by linarith, hT₀⟩, ?_⟩
    simp
  have hmemt : T.stoneU t (w : H) ∈ (fun s : ℝ => T.stoneU s (w : H)) '' Set.Icc (-T₀) T₀ :=
    ⟨t, ⟨by cases abs_le.mp ht with | intro h1 _ => linarith,
      by cases abs_le.mp ht with | intro _ h2 => linarith⟩, rfl⟩
  -- term 1
  have hterm1 : ‖(S n).stoneU t (resDiff T S n (w : H))‖ ≤ eps := by
    rw [(S n).norm_stoneU_apply]
    exact hn1 _ hmem0
  -- term 2 (Duhamel)
  have hterm2 : ‖(S n).resCLM 1 (T.stoneU t (w : H))
      - (S n).stoneU t ((S n).resCLM 1 (w : H))‖ ≤ eps * |t| := by
    refine norm_res_stoneU_sub_stoneU_res_le T (S n) w t ?_
    intro s hs
    have hsmem : T.stoneU s (T.shift 1 w) ∈
        (fun s : ℝ => T.stoneU s (T.shift 1 w)) '' Set.Icc (-T₀) T₀ := by
      have hb := abs_le.mp ht
      rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨s, ⟨by linarith [hb.1], by linarith [hb.2]⟩, rfl⟩
      · exact ⟨s, ⟨by linarith [hb.1], by linarith [hb.2]⟩, rfl⟩
    exact hn2 _ hsmem
  -- term 3
  have hterm3 : ‖resDiff T S n (T.stoneU t (w : H))‖ ≤ eps := hn1 _ hmemt
  -- assemble
  have hcomm : T.stoneU t (T.resCLM 1 (w : H)) = T.resCLM 1 (T.stoneU t (w : H)) :=
    T.stoneU_commute_resCLM t 1 (w : H)
  have hsplit : (S n).stoneU t (T.resCLM 1 (w : H)) - T.stoneU t (T.resCLM 1 (w : H))
      = (S n).stoneU t (resDiff T S n (w : H))
        + ((S n).stoneU t ((S n).resCLM 1 (w : H)) - (S n).resCLM 1 (T.stoneU t (w : H)))
        - resDiff T S n (T.stoneU t (w : H)) := by
    rw [hcomm]
    simp only [resDiff, ContinuousLinearMap.sub_apply, map_sub]
    abel
  have hb1' : ‖(S n).stoneU t (resDiff T S n (w : H))
      + ((S n).stoneU t ((S n).resCLM 1 (w : H)) - (S n).resCLM 1 (T.stoneU t (w : H)))‖
      ≤ eps + eps * |t| := by
    refine le_trans (norm_add_le _ _) (add_le_add hterm1 ?_)
    rw [norm_sub_rev]
    exact hterm2
  have hfinal : eps + eps * |t| + eps ≤ ε := by
    have h1 : eps * |t| ≤ eps * T₀ := by
      exact mul_le_mul_of_nonneg_left ht (le_of_lt hepspos)
    have h2 : eps + eps * T₀ + eps = ε := by
      rw [heps]
      field_simp
      ring
    linarith
  calc ‖(S n).stoneU t (T.resCLM 1 (w : H)) - T.stoneU t (T.resCLM 1 (w : H))‖
      ≤ ‖(S n).stoneU t (resDiff T S n (w : H))
          + ((S n).stoneU t ((S n).resCLM 1 (w : H)) - (S n).resCLM 1 (T.stoneU t (w : H)))‖
        + ‖resDiff T S n (T.stoneU t (w : H))‖ := by
        rw [hsplit]; exact norm_sub_le _ _
    _ ≤ (eps + eps * |t|) + eps := add_le_add hb1' hterm3
    _ ≤ ε := hfinal
