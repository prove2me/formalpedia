-- Prove2me | solution 1 for BSUMConv.BSUM.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:02:56.297344+00:00
-- url     : https://prove2.me/submissions/a5d7b167-c918-4671-a70e-16a24ebc89a8

import Mathlib
import Definitions.Def_TsengBCD_Stationary_Setting
import Definitions.Def_BSUMConv_BSUM_Setting
set_option autoImplicit false
open TsengBCD.Stationary Filter Topology
open BSUMConv.BSUM

theorem kk_bsum_mem {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x) : ∀ r, x r ∈ Xset Xs := by
  intro r
  induction r with
  | zero => exact hx.1
  | succ r ih =>
    have h1 := (hx.2 r).1
    have h3 := (hx.2 r).2.2
    unfold Xset at ih ⊢
    rw [Set.mem_pi] at ih ⊢
    intro k _
    by_cases hk : k = s r
    · subst hk; exact h1
    · rw [h3 k hk]; exact ih k (Set.mem_univ _)

theorem kk_bsum_update {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ)
    (s : ℕ → Fin N) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x) (r : ℕ) :
    x (r + 1) = Function.update (x r) (s r) (x (r + 1) (s r)) := by
  funext k
  by_cases hk : k = s r
  · subst hk; simp
  · rw [Function.update_of_ne hk]; exact (hx.2 r).2.2 k hk

theorem solution {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x) :
    Antitone (fun r => f (x r)) := by
  apply antitone_nat_of_succ_le
  intro r
  have hmem := kk_bsum_mem Xs u s x hx
  have hxr := hmem r
  have h1 := (hx.2 r).1
  have h2 := (hx.2 r).2.1
  have hxs : x r (s r) ∈ Xs (s r) := by
    have := hxr; unfold Xset at this; rw [Set.mem_pi] at this; exact this _ (Set.mem_univ _)
  calc f (x (r + 1)) = f (Function.update (x r) (s r) (x (r + 1) (s r))) := by
        rw [← kk_bsum_update Xs u s x hx r]
    _ ≤ u (s r) (x (r + 1) (s r)) (x r) := hA2.B2 (s r) _ h1 (x r) hxr
    _ ≤ u (s r) (x r (s r)) (x r) := h2 _ hxs
    _ = f (x r) := hA2.B1 (x r) hxr (s r)
