-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T13:16:53.209986+00:00
-- url     : https://prove2.me/submissions/eb8fbc42-3983-4433-a34f-40ff21d394c1

-- Generated from ChapterNavierStokesIkebeKato.lean — solution of BookProof.NavierStokesFlow.IkebeKato.diagMax_hasSum_quadForm
import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato



open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (c : ι → ℝ) (x : maxDom c) :
    HasSum (fun k => c k * ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2) (quadForm (diagMax c) x) := by

  have h := Complex.hasSum_re (lp.hasSum_inner (𝕜 := ℂ) ((x : L2I ι)) (diagMax c x))
  refine h.congr_fun fun k => ?_
  have hcc : (starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) k) * ((x : L2I ι) : ι → ℂ) k
      = ((‖((x : L2I ι) : ι → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    norm_cast
  have hz : (inner ℂ (((x : L2I ι) : ι → ℂ) k) (((diagMax c x : L2I ι) : ι → ℂ) k) : ℂ)
      = ((c k * ‖((x : L2I ι) : ι → ℂ) k‖ ^ 2 : ℝ) : ℂ) := by
    have hstep : (inner ℂ (((x : L2I ι) : ι → ℂ) k) (((diagMax c x : L2I ι) : ι → ℂ) k) : ℂ)
        = (c k : ℂ) * ((starRingEnd ℂ) (((x : L2I ι) : ι → ℂ) k) * ((x : L2I ι) : ι → ℂ) k) := by
      simp only [RCLike.inner_apply, diagMax_coe]
      ring
    rw [hstep, hcc, ← Complex.ofReal_mul]
  rw [hz, Complex.ofReal_re]
