-- Prove2me | solution 1 for DirKECC1549.Main.sec2_kecc_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:03:04.507194+00:00
-- url     : https://prove2.me/submissions/30d21033-069c-47b9-b793-87b2bcffdb1a

import Theorems.Thm_DirKECC1549_Main_disjoint_paths_trans
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (k : ℕ) (D : Fin m → Fin n × Fin n) :
    Equivalence (KEdgeConnected k D) := by
  constructor
  · intro x
    exact Or.inl rfl
  · intro x y h
    rcases h with h | ⟨hxy, hyx⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hyx, hxy⟩
  · intro x y z hxy hyz
    rcases hxy with h | ⟨hxy, hyx⟩
    · subst y
      exact hyz
    rcases hyz with h | ⟨hyz, hzy⟩
    · subst z
      exact Or.inr ⟨hxy, hyx⟩
    · exact Or.inr ⟨disjoint_paths_trans D k x y z hxy hyz,
        disjoint_paths_trans D k z y x hzy hyx⟩
