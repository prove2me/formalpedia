-- Prove2me | solution 1 for FiniteGraph.exists_maximal_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:31:39.26614+00:00
-- url     : https://prove2.me/submissions/4c8c58d4-767a-4372-86b1-c1907bde1232

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
      ∀ J : SimpleGraph V, K ≤ J → P J → J = K := by
  classical
  let Q : SimpleGraph V → Prop := fun G => H ≤ G ∧ P G
  obtain ⟨K, dK, hK⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists Q).2 ⟨H, le_rfl, hH⟩
  refine ⟨K, hK.prop.1, hK.prop.2, ?_⟩
  intro J hKJ hPJ
  have hQ : Q J := ⟨hK.prop.1.trans hKJ, hPJ⟩
  exact ((hK.le_iff_eq hQ).mp hKJ).symm