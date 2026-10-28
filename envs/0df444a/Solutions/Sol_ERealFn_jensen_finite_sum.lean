-- Prove2me | solution 1 for ERealFn.jensen_finite_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T16:24:38.22311+00:00
-- url     : https://prove2.me/submissions/6f6c1d2a-acf1-4d6c-872f-4579945d61b5

import Mathlib

set_option autoImplicit false

-- carved from submission af8c70db-6fa0-4580-9851-54457c202aeb, lines 72-81

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hconv : Convex ℝ {p : H × ℝ | f p.1 ≤ (p.2 : EReal)})
    (s : Finset ℕ) (w : ℕ → ℝ) (y : ℕ → H) (a : ℕ → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, f (y i) = a i) :
    f (∑ i ∈ s, w i • y i) ≤ ((∑ i ∈ s, w i * a i : ℝ) : EReal) := by
  have hmem := hconv.sum_mem hw0 hw1 (z := fun i => (y i, a i)) (fun i hi => by
    simp only [Set.mem_ofPred_eq]; rw [ha i hi])
  simp only [Set.mem_ofPred_eq, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hmem
  exact hmem
