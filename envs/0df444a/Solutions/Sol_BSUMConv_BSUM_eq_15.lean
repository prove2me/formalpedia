-- Prove2me | solution 1 for BSUMConv.BSUM.eq_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:03:31.986174+00:00
-- url     : https://prove2.me/submissions/3f74c684-add7-4a3b-bab2-7d718e922fe1

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

theorem kk_bsum_anti {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (f : X n → ℝ)
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (s : ℕ → Fin N) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x) :
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

theorem solution {N : ℕ} {n : Fin N → ℕ}
    (Xs : (i : Fin N) → Set (EuclideanSpace ℝ (Fin (n i))))
    (hXconv : ∀ i, Convex ℝ (Xs i)) (hXclosed : ∀ i, IsClosed (Xs i))
    (f : X n → ℝ) (hf : ContinuousOn f (Xset Xs))
    (u : (i : Fin N) → EuclideanSpace ℝ (Fin (n i)) → X n → ℝ) (hA2 : Assumption2 Xs f u)
    (s : ℕ → Fin N) (hs : IsCyclic s) (x : ℕ → X n) (hx : IsBSUMRun Xs u s x)
    (z : X n) (hz : MapClusterPt z atTop x) :
    Tendsto (fun r => f (x r)) atTop (𝓝 (f z)) := by
  have hmem := kk_bsum_mem Xs u s x hx
  have hanti := kk_bsum_anti Xs f u hA2 s x hx
  have hclosed : IsClosed (Xset Xs) := by
    unfold Xset; exact isClosed_set_pi (fun i _ => hXclosed i)
  obtain ⟨ψ, hψ, hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hz
  have hzX : z ∈ Xset Xs := hclosed.mem_of_tendsto hlim (Eventually.of_forall (fun j => hmem _))
  have hcw : ContinuousWithinAt f (Xset Xs) z := hf z hzX
  have hlim2 : Tendsto (x ∘ ψ) atTop (𝓝[Xset Xs] z) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall (fun j => hmem _)⟩
  have hsub : Tendsto ((fun r => f (x r)) ∘ ψ) atTop (𝓝 (f z)) := hcw.tendsto.comp hlim2
  have hbdd : BddBelow (Set.range (fun r => f (x r))) := by
    refine ⟨f z, ?_⟩
    rintro _ ⟨r, rfl⟩
    exact le_of_tendsto hsub (eventually_atTop.2 ⟨r, fun j hj => hanti (le_trans hj (hψ.id_le j))⟩)
  have hT := tendsto_atTop_ciInf hanti hbdd
  have hT2 : Tendsto ((fun r => f (x r)) ∘ ψ) atTop (𝓝 (⨅ r, f (x r))) :=
    hT.comp hψ.tendsto_atTop
  have := tendsto_nhds_unique hT2 hsub
  rw [this] at hT
  exact hT
