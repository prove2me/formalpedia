-- Prove2me | solution 1 for FamousTheorems.kummer_cyclic_extension_tfae_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:07:49.157274+00:00
-- url     : https://prove2.me/submissions/c9285227-db32-4eff-b485-72079e628109

import Mathlib

open Polynomial IntermediateField

theorem solution (K L : Type*) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    [IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L),
      ∃ a : K, Irreducible (X ^ Module.finrank K L - C a) ∧
        IsSplittingField K L (X ^ Module.finrank K L - C a),
      ∃ α : L, α ^ Module.finrank K L ∈ Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤].TFAE :=
  isCyclic_tfae K L hK
