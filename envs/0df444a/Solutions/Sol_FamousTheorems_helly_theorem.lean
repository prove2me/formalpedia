-- Prove2me | solution 1 for FamousTheorems.helly_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:11:21.87981+00:00
-- url     : https://prove2.me/submissions/138c77e1-c7fb-46fb-85a8-c6dcce3768ea

import Mathlib

theorem solution {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [FiniteDimensional 𝕜 E] {F : ι → Set E} {s : Finset ι} (h_card : Module.finrank 𝕜 E + 1 ≤ s.card)
    (h_convex : ∀ i ∈ s, Convex 𝕜 (F i))
    (h_inter : ∀ I ⊆ s, I.card = Module.finrank 𝕜 E + 1 → (⋂ i ∈ I, F i).Nonempty) : (⋂ i ∈ s, F i).Nonempty :=
  Convex.helly_theorem h_card h_convex h_inter
