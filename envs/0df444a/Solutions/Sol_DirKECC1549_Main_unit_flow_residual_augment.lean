-- Prove2me | solution 1 for DirKECC1549.Main.unit_flow_residual_augment
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-12T11:17:58.76722+00:00
-- url     : https://prove2.me/submissions/30b98813-ad7a-4d99-9750-21550012d0db

import Theorems.Thm_DirKECC1549_Main_unit_flow_toggle_residual_trail
set_option autoImplicit false
open DirKECC1549.Main

private theorem walk_suffix {n m : ℕ} (D : Fin m → Fin n × Fin n)
    {u v : Fin n} {p : List (Fin m)} (hp : IsWalk D u p v) (e : Fin m) (he : e ∈ p) :
    ∃ q : List (Fin m), IsWalk D (D e).1 q v ∧ List.Sublist q p := by
  classical
  induction hp with
  | nil => simp at he
  | @cons a b f p ht hw ih =>
    simp only [List.mem_cons] at he
    rcases he with h | h
    · subst f
      exact ⟨e :: p, by simpa [ht] using IsWalk.cons e p ht hw, List.Sublist.refl _⟩
    · obtain ⟨q, hq, hs⟩ := ih h
      exact ⟨q, hq, hs.cons _⟩

private theorem shorten_walk {n m : ℕ} (D : Fin m → Fin n × Fin n)
    {u v : Fin n} {p : List (Fin m)} (hp : IsWalk D u p v) :
    ∃ q : List (Fin m), IsTrail D u q v ∧ List.Sublist q p := by
  classical
  induction hp with
  | nil => exact ⟨[], ⟨IsWalk.nil _, List.nodup_nil⟩, List.Sublist.refl _⟩
  | @cons a b e p ht hw ih =>
    obtain ⟨q, ⟨hq, hn⟩, hsub⟩ := ih
    by_cases he : e ∈ q
    · obtain ⟨r, hr, hrs⟩ := walk_suffix D hq e he
      refine ⟨r, ⟨?_, hn.sublist hrs⟩, hrs.trans (hsub.cons _)⟩
      simpa [ht] using hr
    · refine ⟨e :: q, ⟨IsWalk.cons e q ht hq, List.nodup_cons.mpr ⟨he, hn⟩⟩, ?_⟩
      exact hsub.cons_cons _

theorem solution {n m : ℕ} (D : Fin m → Fin n × Fin n)
    (u v : Fin n) (huv : u ≠ v) (q : ℕ) (F : Finset (Fin m))
    (hF : IsUnitFlow D F u v q) (hr : Reach (flipEdges D F) u v) :
    ∃ F' : Finset (Fin m), IsUnitFlow D F' u v (q + 1) := by
  classical
  obtain ⟨p, hp⟩ := hr
  obtain ⟨r, hr, _⟩ := shorten_walk (flipEdges D F) hp
  exact ⟨(F \ r.toFinset) ∪ (r.toFinset \ F),
    unit_flow_toggle_residual_trail D u v q F hF r hr⟩
