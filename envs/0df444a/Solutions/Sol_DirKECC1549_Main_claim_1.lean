-- Prove2me | solution 1 for DirKECC1549.Main.claim_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T05:11:23.383771+00:00
-- url     : https://prove2.me/submissions/736431aa-6ca2-40c9-a6ef-bfb57849786c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DirKECC1549_Main_scc_disjoint_paths
set_option autoImplicit false
open DirKECC1549.Main

theorem solution {n m : ℕ} (k : ℕ) (hk : 1 ≤ k) (G : Fin m → Fin n × Fin n)
    (u v : Fin n) :
    KEdgeConnected k G u v ↔
      StronglyConn G u v ∧
        liftRel (sccOf G u) (KEdgeConnected k (induced G (sccOf G u))) u v := by
  have huu : StronglyConn G u u := ⟨⟨[], IsWalk.nil u⟩, ⟨[], IsWalk.nil u⟩⟩
  have hs : KEdgeConnected k G u v → StronglyConn G u v := by
    intro h
    rcases h with h | ⟨⟨P, hP, _⟩, ⟨Q, hQ, _⟩⟩
    · subst v
      exact huu
    · exact ⟨⟨P ⟨0, hk⟩, (hP ⟨0, hk⟩).1⟩, ⟨Q ⟨0, hk⟩, (hQ ⟨0, hk⟩).1⟩⟩
  constructor
  · intro h
    have huv := hs h
    have hu : u ∈ sccOf G u := by simpa [sccOf] using huu
    have hv : v ∈ sccOf G u := by simpa [sccOf] using huv
    refine ⟨huv, hu, hv, ?_⟩
    rcases h with h | ⟨h₁, h₂⟩
    · subst v
      exact Or.inl rfl
    · right
      obtain ⟨_, _, h₁'⟩ := (scc_disjoint_paths G u u v k huu huv).mp h₁
      obtain ⟨_, _, h₂'⟩ := (scc_disjoint_paths G u v u k huv huu).mp h₂
      exact ⟨h₁', h₂'⟩
  · rintro ⟨huv, hu, hv, h⟩
    rcases h with h | ⟨h₁, h₂⟩
    · left
      have hh := congrArg (vertexOf (sccOf G u)) h
      simpa [vertexOf, posIn] using hh
    · right
      exact ⟨(scc_disjoint_paths G u u v k huu huv).mpr ⟨hu, hv, h₁⟩,
        (scc_disjoint_paths G u v u k huv huu).mpr ⟨hv, hu, h₂⟩⟩
