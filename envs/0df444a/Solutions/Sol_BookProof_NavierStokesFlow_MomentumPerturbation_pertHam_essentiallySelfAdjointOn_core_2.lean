-- Prove2me | solution 2 for BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:11:17.29598+00:00
-- url     : https://prove2.me/submissions/22517520-2d0b-4589-a402-9a9f1d826df6

import Mathlib
import Definitions.Def_ChapterNavierStokesMomentumPerturbation
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_MomentumPerturbation_pertHam_relative_bound
import Theorems.Thm_BookProof_FarisLavine_commForm_eq
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_symmetricOn
import Theorems.Thm_BookProof_NavierStokesFlow_IkebeKato_diagMax_hasSum_quadForm
-- Generated from ChapterNavierStokesMomentumPerturbation.lean — theorem BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.MomentumPerturbation




open LpNat BookProof.FarisLavine IkebeKato

variable {ι : Type*}
theorem h44_norm_sq_le_quad {ι : Type*} (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (x : maxDom c) :
    ‖(x : L2I ι)‖ ^ 2 ≤ quadForm (diagMax c) x := by
  have h1 := Complex.reCLM.hasSum (lp.hasSum_inner (𝕜 := ℂ) (x : L2I ι) (x : L2I ι))
  have h2 := diagMax_hasSum_quadForm c x
  have hn : (Complex.reCLM (inner ℂ (x : L2I ι) (x : L2I ι))) = ‖(x : L2I ι)‖ ^ 2 := by
    simp [Complex.reCLM_apply, ← Complex.ofReal_pow]
  rw [hn] at h1
  refine hasSum_le (fun k => ?_) h1 h2
  have : (Complex.reCLM (inner ℂ (((x : L2I ι) : ι → ℂ) k) (((x : L2I ι) : ι → ℂ) k)))
      = ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2 := by simp [Complex.reCLM_apply, ← Complex.ofReal_pow]
  rw [this]
  nlinarith [hc k, sq_nonneg ‖((x : L2I ι) : ι → ℂ) k‖]

theorem h44_pert_comm (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k) (u w : maxDom c)
    (x : maxDom c) :
    |commForm (pertHam c (u : L2I ι) (w : L2I ι)) (diagMax c) x|
      ≤ (2 * (‖(u : L2I ι)‖ * ‖diagMax c w‖ + ‖(w : L2I ι)‖ * ‖diagMax c u‖))
        * quadForm (diagMax c) x := by
  set N := diagMax c
  have hsym := diagMax_symmetricOn c
  have hHx : pertHam c (u : L2I ι) (w : L2I ι) x
      = N x + ((inner ℂ (u : L2I ι) (x : L2I ι) : ℂ) • (w : L2I ι)
          + (inner ℂ (w : L2I ι) (x : L2I ι) : ℂ) • (u : L2I ι)) := rfl
  have h0 : (inner ℂ (N x) (N x)).im = 0 := by
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  rw [commForm_eq, hHx, inner_add_left, Complex.add_im, h0, zero_add,
    inner_add_left, inner_smul_left, inner_smul_left]
  rw [← hsym w x, ← hsym u x]
  set z := (starRingEnd ℂ) (inner ℂ (u : L2I ι) (x : L2I ι)) * inner ℂ (N w) (x : L2I ι)
      + (starRingEnd ℂ) (inner ℂ (w : L2I ι) (x : L2I ι)) * inner ℂ (N u) (x : L2I ι) with hz
  have hzb : ‖z‖ ≤ (‖(u : L2I ι)‖ * ‖N w‖ + ‖(w : L2I ι)‖ * ‖N u‖) * ‖(x : L2I ι)‖ ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj]
    have a1 := norm_inner_le_norm (𝕜 := ℂ) (u : L2I ι) (x : L2I ι)
    have a2 := norm_inner_le_norm (𝕜 := ℂ) (N w) (x : L2I ι)
    have a3 := norm_inner_le_norm (𝕜 := ℂ) (w : L2I ι) (x : L2I ι)
    have a4 := norm_inner_le_norm (𝕜 := ℂ) (N u) (x : L2I ι)
    calc _ ≤ (‖(u : L2I ι)‖ * ‖(x : L2I ι)‖) * (‖N w‖ * ‖(x : L2I ι)‖)
          + (‖(w : L2I ι)‖ * ‖(x : L2I ι)‖) * (‖N u‖ * ‖(x : L2I ι)‖) :=
          add_le_add (mul_le_mul a1 a2 (norm_nonneg _) (by positivity))
            (mul_le_mul a3 a4 (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have him : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hq := h44_norm_sq_le_quad c hc x
  have hK : 0 ≤ ‖(u : L2I ι)‖ * ‖N w‖ + ‖(w : L2I ι)‖ * ‖N u‖ := by positivity
  rw [abs_mul, abs_neg, abs_two]
  have := mul_le_mul_of_nonneg_left hq hK
  nlinarith

theorem solution (c : ι → ℝ) (hc : ∀ k, 1 ≤ c k)
    (u w : maxDom c) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((pertHam c (u : L2I ι) (w : L2I ι)).comp
        (Submodule.inclusion (finiteModes_le_maxDom c))) := by
  exact essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds c
    (fun k => le_trans zero_le_one (hc k)) (pertHam c (u : L2I ι) (w : L2I ι)) 2
    (2 * (2 * (‖(u : L2I ι)‖ * ‖(w : L2I ι)‖)) ^ 2)
    (2 * (‖(u : L2I ι)‖ * ‖diagMax c w‖ + ‖(w : L2I ι)‖ * ‖diagMax c u‖))
    (MomentumPerturbation.pertHam_symmetricOn c _ _) (by positivity)
    (MomentumPerturbation.pertHam_relative_bound c _ _) (h44_pert_comm c hc u w)

