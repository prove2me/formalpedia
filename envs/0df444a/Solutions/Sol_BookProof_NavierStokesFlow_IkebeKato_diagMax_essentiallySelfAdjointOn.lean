-- Prove2me | solution 1 for BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-22T05:35:39.100283+00:00
-- url     : https://prove2.me/submissions/4a105f82-177a-47e0-bec9-a9f7d0a29533

import Mathlib
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.IkebeKato


open scoped ENNReal



open LpNat BookProof.FarisLavine

variable {ι : Type*}

theorem dmx_key (c : ι → ℝ) (z : ℂ) (hz : ∀ k : ι, (c k : ℂ) ≠ z) :
    DeficiencyTrivialAt (maxDom c) (diagMax c) z := by
  classical
  intro w hw
  ext k
  have hmem : (lp.single 2 k (1 : ℂ) : L2I ι) ∈ maxDom c := by
    change Memℓp (fun j => (c j : ℂ) * ((lp.single 2 k (1 : ℂ) : L2I ι) : ι → ℂ) j) 2
    have : (fun j => (c j : ℂ) * ((lp.single 2 k (1 : ℂ) : L2I ι) : ι → ℂ) j)
        = ((lp.single 2 k ((c k : ℂ)) : L2I ι) : ι → ℂ) := by
      funext j
      simp only [lp.single_apply, Pi.single_apply]
      split_ifs with hj
      · subst hj; simp
      · simp
    rw [this]
    exact (lp.single 2 k ((c k : ℂ)) : L2I ι).2
  have h := hw ⟨_, hmem⟩
  have hd : (diagMax c ⟨_, hmem⟩ : L2I ι) = lp.single 2 k ((c k : ℂ)) := by
    refine lp.ext (funext fun j => ?_)
    change (c j : ℂ) * ((lp.single 2 k (1 : ℂ) : L2I ι) : ι → ℂ) j = _
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs with hj
    · subst hj; simp
    · simp
  rw [hd] at h
  change (inner ℂ (lp.single 2 k ((c k : ℂ))) w : ℂ) = z * inner ℂ (lp.single 2 k (1 : ℂ)) w at h
  rw [lp.inner_single_left, lp.inner_single_left] at h
  simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one, one_mul] at h
  have h2 : ((c k : ℂ) - z) * w k = 0 := by
    have : w k * (c k : ℂ) = z * w k := by simpa [mul_comm] using h
    linear_combination this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) (hz k)
  · simpa using h3

theorem solution (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) :
    EssentiallySelfAdjointOn (maxDom c) (diagMax c) :=
  ⟨dmx_key c _ (fun k h => by simpa using congrArg Complex.im h),
   dmx_key c _ (fun k h => by simpa using congrArg Complex.im h)⟩
