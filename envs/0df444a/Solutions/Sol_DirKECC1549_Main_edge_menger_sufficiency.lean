-- Prove2me | solution 1 for DirKECC1549.Main.edge_menger_sufficiency
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T10:14:23.095196+00:00
-- url     : https://prove2.me/submissions/57b59af2-8f3d-4ee4-9c94-9d29268c8110

import Theorems.Thm_DirKECC1549_Main_edge_menger_cut
set_option autoImplicit false
open DirKECC1549.Main

private theorem walk_stays {n m : ℕ} {D : Fin m → Fin n × Fin n}
    (S : Finset (Fin n)) {x y : Fin n} {p : List (Fin m)}
    (hp : IsWalk D x p y) (hx : x ∈ S)
    (ha : ∀ e ∈ p, e ∉ outEdges D S) : y ∈ S := by
  classical
  induction hp with
  | nil => exact hx
  | @cons u v e p ht hw ih =>
    have he : e ∉ outEdges D S := ha e (by simp)
    have hu : (D e).1 ∈ S := by simpa [ht] using hx
    have hv : (D e).2 ∈ S := by
      by_contra hn
      apply he
      simp [outEdges, hu, hn]
    apply ih hv
    intro f hf
    exact ha f (by simp [hf])

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n) (k : ℕ)
    (x y : Fin n) (h : ∀ F : Finset (Fin m), F.card < k →
      ∃ p, IsWalk D x p y ∧ ∀ e ∈ p, e ∉ F) : HasDisjointPaths D k x y := by
  classical
  by_cases hxy : x = y
  · subst y
    refine ⟨fun _ ↦ [], ?_, ?_⟩
    · intro i
      exact ⟨IsWalk.nil x, List.nodup_nil⟩
    · intro i j hij
      simp
  · apply edge_menger_cut D k x y hxy
    intro S hx hy
    by_contra hn
    have hsmall : (outEdges D S).card < k := by
      change outCount D S < k
      omega
    obtain ⟨p, hp, ha⟩ := h (outEdges D S) hsmall
    exact hy (walk_stays S hp hx ha)
