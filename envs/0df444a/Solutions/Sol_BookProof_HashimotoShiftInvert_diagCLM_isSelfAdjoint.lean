-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.diagCLM_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T02:21:07.430782+00:00
-- url     : https://prove2.me/submissions/4628b17a-d204-4383-9fcc-9be79a2b872f

import Definitions.Def_ChapterHashimotoShiftInvert

open BookProof.HashimotoShiftInvert

-- Direct proof from the registered statement using Mathlib.
theorem solution {c : ℕ → ℝ} (hc : ∀ n, |c n| ≤ 1) :
    IsSelfAdjoint (diagCLM hc) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (diagCLM hc x) y = inner ℂ x (diagCLM hc y)
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [diagCLM_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
