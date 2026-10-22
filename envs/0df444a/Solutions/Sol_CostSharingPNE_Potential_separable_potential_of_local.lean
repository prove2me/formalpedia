-- Prove2me | solution 1 for CostSharingPNE.Potential.separable_potential_of_local
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:05:04.222025+00:00
-- url     : https://prove2.me/submissions/c8578a69-e0bb-47d5-a2ff-5e1642805159

import Mathlib
import Definitions.Def_CostSharingPNE_Potential_Setting

set_option autoImplicit false
open CostSharingPNE.Potential

theorem solution
    (n m : ℕ) (hn : 1 < n) (hm : 1 < m)
    (A : Fin n → Finset (Finset (Fin m)))
    (F : Fin m → CostSharingPNE.Char.Rule n) {K : ℕ}
    (φ : Fin m → Finset (Fin n) → Fin K → ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (idx : Fin n → Fin K)
    (hloc : ∀ r i S, i ∈ S →
      (∀ c, c < idx i → φ r S c = φ r (S.erase i) c) ∧
      F r i S = w i * (φ r S (idx i) - φ r (S.erase i) (idx i))) :
    IsGenWeightedPotential A (fun i a => utility F a i)
      (fun a => ∑ r, φ r (CostSharingPNE.Char.players a r)) w := by
  refine ⟨Fin.pos (idx ⟨0, by omega⟩), hw, idx, ?_⟩
  intro i a _ b' _ b'' _
  have hmem : ∀ (b : Finset (Fin m)) r,
      i ∈ CostSharingPNE.Char.players (Function.update a i b) r ↔ r ∈ b := by
    intro b r
    simp [CostSharingPNE.Char.players]
  have herase : ∀ (b : Finset (Fin m)) r,
      (CostSharingPNE.Char.players (Function.update a i b) r).erase i =
        (CostSharingPNE.Char.players a r).erase i := by
    intro b r
    ext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [CostSharingPNE.Char.players, hj, Function.update_of_ne hj]
  have hsum : ∀ (b : Finset (Fin m)) (g : Fin m → ℝ),
      ∑ r ∈ b, g r = ∑ r, if r ∈ b then g r else 0 := by
    intro b g
    rw [← Finset.sum_filter]
    congr 1
    ext r; simp
  have key : ∀ r : Fin m,
      (∀ c, c < idx i →
        φ r (CostSharingPNE.Char.players (Function.update a i b') r) c =
          φ r (CostSharingPNE.Char.players (Function.update a i b'') r) c) ∧
      ((if r ∈ b' then F r i (CostSharingPNE.Char.players (Function.update a i b') r) else 0) -
        (if r ∈ b'' then F r i (CostSharingPNE.Char.players (Function.update a i b'') r) else 0)
        = w i * (φ r (CostSharingPNE.Char.players (Function.update a i b') r) (idx i) -
          φ r (CostSharingPNE.Char.players (Function.update a i b'') r) (idx i))) := by
    intro r
    set S' := CostSharingPNE.Char.players (Function.update a i b') r with hS'
    set S'' := CostSharingPNE.Char.players (Function.update a i b'') r with hS''
    have he : S'.erase i = S''.erase i := (herase b' r).trans (herase b'' r).symm
    by_cases h1 : r ∈ b' <;> by_cases h2 : r ∈ b''
    · have i1 : i ∈ S' := (hmem b' r).2 h1
      have i2 : i ∈ S'' := (hmem b'' r).2 h2
      have : S' = S'' := by rw [← Finset.insert_erase i1, ← Finset.insert_erase i2, he]
      rw [this]
      simp [h1, h2]
    · have i1 : i ∈ S' := (hmem b' r).2 h1
      have i2 : i ∉ S'' := fun h => h2 ((hmem b'' r).1 h)
      have : S'' = S'.erase i := by rw [he, Finset.erase_eq_of_notMem i2]
      obtain ⟨hc, hF⟩ := hloc r i S' i1
      rw [this]
      simp only [h1, h2, if_true, if_false, sub_zero]
      exact ⟨hc, hF⟩
    · have i2 : i ∈ S'' := (hmem b'' r).2 h2
      have i1 : i ∉ S' := fun h => h1 ((hmem b' r).1 h)
      have : S' = S''.erase i := by rw [← he, Finset.erase_eq_of_notMem i1]
      obtain ⟨hc, hF⟩ := hloc r i S'' i2
      rw [this]
      simp only [h1, h2, if_true, if_false, zero_sub]
      refine ⟨fun c hc' => (hc c hc').symm, ?_⟩
      rw [hF]; ring
    · have i1 : i ∉ S' := fun h => h1 ((hmem b' r).1 h)
      have i2 : i ∉ S'' := fun h => h2 ((hmem b'' r).1 h)
      have : S' = S'' := by
        rw [← Finset.erase_eq_of_notMem i1, ← Finset.erase_eq_of_notMem i2, he]
      rw [this]
      simp [h1, h2]
  constructor
  · intro c hc
    beta_reduce
    rw [Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl (fun r _ => (key r).1 c hc)
  · unfold utility
    simp only [Function.update_self]
    beta_reduce
    rw [Finset.sum_apply, Finset.sum_apply, hsum b', hsum b'', ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun r _ => (key r).2)
