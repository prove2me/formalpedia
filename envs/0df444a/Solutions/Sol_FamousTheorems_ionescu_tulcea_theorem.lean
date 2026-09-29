-- Prove2me | solution 1 for FamousTheorems.ionescu_tulcea_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:11:17.794505+00:00
-- url     : https://prove2.me/submissions/fcfd5940-239f-473c-b238-5f9e08390384

import Mathlib

theorem solution {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (κ : (n : ℕ) → ProbabilityTheory.Kernel ((i : Finset.Iic n) → X i) (X (n + 1)))
    [∀ n, ProbabilityTheory.IsMarkovKernel (κ n)] (a : ℕ) :
    ∃ η : ProbabilityTheory.Kernel ((i : Finset.Iic a) → X i) ((n : ℕ) → X n),
      ∀ b : ℕ, η.map (Preorder.frestrictLe b) = ProbabilityTheory.Kernel.partialTraj κ a b :=
  ⟨ProbabilityTheory.Kernel.traj κ a, ProbabilityTheory.Kernel.traj_map_frestrictLe a⟩
