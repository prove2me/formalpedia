-- Prove2me | solution 1 for BookProof.HermiteLadder.exists_ladderOrd_hamPolyL
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:53:52.146264+00:00
-- url     : https://prove2.me/submissions/46c7902d-a9a3-47be-991a-89844502443f

import Definitions.Def_ChapterHermiteLadderOrder

open BookProof.HermiteLadder
open BookProof.QgHermiteFriedrichs BookProof.DegSchrodinger
open MvPolynomial

noncomputable section

variable {d : ℕ}

theorem solution (S : Finset (Fin d)) (q : MvPolynomial (Fin d) ℂ) :
    ∃ n, LadderOrd (hamPolyL S q) n := by
  let K : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
    -∑ j ∈ S, (coreDL j) ∘ₗ (coreDL j)
  have hK : LadderOrd K 2 := by
    apply LadderOrd.neg
    apply LadderOrd.sum
    intro j hj
    simpa only [Nat.reduceAdd] using
      (ladderOrd_coreDL j).comp (ladderOrd_coreDL j)
  obtain ⟨n, hn⟩ := exists_ladderOrd_mulL q
  refine ⟨max 2 n, ?_⟩
  have heq : hamPolyL S q = K + mulL q := by
    apply LinearMap.ext
    intro p
    simp [K, hamPolyL, kinPolyS, coreDL_apply, mulL_apply]
  rw [heq]
  exact (hK.mono (le_max_left 2 n)).add (hn.mono (le_max_right 2 n))
