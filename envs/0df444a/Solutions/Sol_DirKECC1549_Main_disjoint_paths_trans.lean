-- Prove2me | solution 1 for DirKECC1549.Main.disjoint_paths_trans
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:06:46.727287+00:00
-- url     : https://prove2.me/submissions/35553b91-5a78-499c-9d2a-dd7e89c192a2

import Theorems.Thm_DirKECC1549_Main_edge_menger_avoid
set_option autoImplicit false
open DirKECC1549.Main

private theorem append_walk {n m : ℕ} {D : Fin m → Fin n × Fin n}
    {x y z : Fin n} {p q : List (Fin m)} (hp : IsWalk D x p y) (hq : IsWalk D y q z) :
    IsWalk D x (p ++ q) z := by
  induction hp with
  | nil => simpa using hq
  | cons e p ht hw ih => exact IsWalk.cons e (p ++ q) ht (ih hq)

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y z : Fin n) (hxy : HasDisjointPaths D k x y) (hyz : HasDisjointPaths D k y z) :
    HasDisjointPaths D k x z := by
  apply (edge_menger_avoid D k x z).mpr
  intro F hF
  obtain ⟨p, hp, ha⟩ := (edge_menger_avoid D k x y).mp hxy F hF
  obtain ⟨q, hq, hb⟩ := (edge_menger_avoid D k y z).mp hyz F hF
  refine ⟨p ++ q, append_walk hp hq, ?_⟩
  intro e he
  simp only [List.mem_append] at he
  rcases he with he | he
  · exact ha e he
  · exact hb e he
