-- Prove2me | solution 1 for DiscreteConvex.MConvexSetsB.base_polyhedron_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:25:34.436545+00:00
-- url     : https://prove2.me/submissions/4492c95d-42c4-4d82-ac17-54037907638b

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexSetsB_SubmodularSetFunction
import Definitions.Def_DiscreteConvex_MConvexSetsB_BasePolyhedron

open DiscreteConvex.MConvexSetsB

namespace BasePolyNonemptyCore

lemma ne_top_of_add_ne_top {a b : WithTop ℝ} (h : a + b ≠ ⊤) : a ≠ ⊤ ∧ b ≠ ⊤ := by
  refine ⟨fun ha => h (by simp [ha]), fun hb => h (by simp [hb])⟩

/-- Submodularity at two finite values, read off in `ℝ`. -/
lemma submod_real {a b c d : WithTop ℝ} (h : a + b ≥ c + d) (ha : a ≠ ⊤) (hb : b ≠ ⊤) :
    ∃ hc : c ≠ ⊤, ∃ hd : d ≠ ⊤, c.untop hc + d.untop hd ≤ a.untop ha + b.untop hb := by
  have hab : a + b ≠ ⊤ := by simp [ha, hb]
  have hcd : c + d ≠ ⊤ := ne_top_of_lt (lt_of_le_of_lt h (lt_top_iff_ne_top.mpr hab))
  obtain ⟨hc, hd⟩ := ne_top_of_add_ne_top hcd
  refine ⟨hc, hd, ?_⟩
  have e1 : a = ((a.untop ha : ℝ) : WithTop ℝ) := (WithTop.coe_untop a ha).symm
  have e2 : b = ((b.untop hb : ℝ) : WithTop ℝ) := (WithTop.coe_untop b hb).symm
  have e3 : c = ((c.untop hc : ℝ) : WithTop ℝ) := (WithTop.coe_untop c hc).symm
  have e4 : d = ((d.untop hd : ℝ) : WithTop ℝ) := (WithTop.coe_untop d hd).symm
  rw [e1, e2, e3, e4, ← WithTop.coe_add, ← WithTop.coe_add, ge_iff_le, WithTop.coe_le_coe] at h
  exact h

theorem core {V : Type*} [Fintype V] [DecidableEq V] :
    ∀ (n : ℕ) (W : Finset V), W.card = n → ∀ σ : Finset V → WithTop ℝ, σ ∅ = 0 → σ W ≠ ⊤ →
      (∀ X Y : Finset V, σ X + σ Y ≥ σ (X ∪ Y) + σ (X ∩ Y)) →
      ∃ x : V → ℝ, (∀ X ⊆ W, ((∑ v ∈ X, x v : ℝ) : WithTop ℝ) ≤ σ X) ∧
        ((∑ v ∈ W, x v : ℝ) : WithTop ℝ) = σ W := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW σ hσ0 hσW hsub
  rcases W.eq_empty_or_nonempty with hWe | hWne
  · subst hWe
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro X hX
      rw [Finset.subset_empty.mp hX, hσ0]; simp
    · rw [hσ0]; simp
  -- a minimal nonempty finite-valued subset `S1` of `W`
  set F := W.powerset.filter (fun S => S.Nonempty ∧ σ S ≠ ⊤) with hF
  have hWF : W ∈ F := by simp [hF, hWne, hσW]
  obtain ⟨S1, hS1F, hS1min⟩ := Finset.exists_min_image F Finset.card ⟨W, hWF⟩
  simp only [hF, Finset.mem_filter, Finset.mem_powerset] at hS1F
  obtain ⟨hS1W, hS1ne, hS1top⟩ := hS1F
  have hmin : ∀ T ⊆ S1, T.Nonempty → σ T ≠ ⊤ → T = S1 := by
    intro T hT hTne hTtop
    have hTF : T ∈ F := by
      simp only [hF, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hT.trans hS1W, hTne, hTtop⟩
    exact Finset.eq_of_subset_of_card_le hT (hS1min T hTF)
  set r : ℝ := (σ S1).untop hS1top with hr
  have hσS1 : σ S1 = (r : WithTop ℝ) := (WithTop.coe_untop _ hS1top).symm
  -- the contracted function on `W \ S1`
  set σ' : Finset V → WithTop ℝ := fun Y => σ (S1 ∪ Y) + ((-r : ℝ) : WithTop ℝ) with hσ'
  have hσ'0 : σ' ∅ = 0 := by
    simp only [hσ', Finset.union_empty, hσS1, ← WithTop.coe_add]; simp
  set W' := W \ S1 with hW'
  have hS1W' : S1 ∪ W' = W := Finset.union_sdiff_of_subset hS1W
  have hσ'W : σ' W' ≠ ⊤ := by
    simp only [hσ', hS1W']; simp [hσW]
  have hsub' : ∀ X Y : Finset V, σ' X + σ' Y ≥ σ' (X ∪ Y) + σ' (X ∩ Y) := by
    intro X Y
    have h1 := hsub (S1 ∪ X) (S1 ∪ Y)
    have hu : (S1 ∪ X) ∪ (S1 ∪ Y) = S1 ∪ (X ∪ Y) := by
      ext a; simp only [Finset.mem_union]; tauto
    have hi : (S1 ∪ X) ∩ (S1 ∪ Y) = S1 ∪ (X ∩ Y) := (Finset.union_inter_distrib_left _ _ _).symm
    rw [hu, hi] at h1
    simp only [hσ', ge_iff_le]
    calc σ (S1 ∪ (X ∪ Y)) + ((-r : ℝ) : WithTop ℝ) + (σ (S1 ∪ (X ∩ Y)) + ((-r : ℝ) : WithTop ℝ))
        = (σ (S1 ∪ (X ∪ Y)) + σ (S1 ∪ (X ∩ Y))) + (((-r : ℝ) : WithTop ℝ) + ((-r : ℝ) : WithTop ℝ)) := by
          rw [add_add_add_comm]
      _ ≤ (σ (S1 ∪ X) + σ (S1 ∪ Y)) + (((-r : ℝ) : WithTop ℝ) + ((-r : ℝ) : WithTop ℝ)) := by
          gcongr
      _ = σ (S1 ∪ X) + ((-r : ℝ) : WithTop ℝ) + (σ (S1 ∪ Y) + ((-r : ℝ) : WithTop ℝ)) := by
          rw [add_add_add_comm]
  have hcard : W'.card < n := by
    rw [← hW, hW', Finset.card_sdiff_of_subset hS1W]
    have := hS1ne.card_pos
    have := Finset.card_le_card hS1W
    omega
  obtain ⟨x', hx'1, hx'2⟩ := ih W'.card hcard W' rfl σ' hσ'0 hσ'W hsub'
  obtain ⟨t, ht⟩ := hS1ne
  set x : V → ℝ := fun v => if v ∈ S1 then (if v = t then r else 0) else x' v with hx
  -- sums of `x`
  have hsumS1 : ∀ X : Finset V, X ∩ S1 = S1 → ∑ v ∈ X ∩ S1, x v = r := by
    intro X hX
    rw [hX, Finset.sum_congr rfl (g := fun v => if v = t then r else 0)
      (fun v hv => by simp only [hx, if_pos hv])]
    rw [Finset.sum_ite_eq' S1 t (fun _ => r)]; simp [ht]
  have hsumE : ∀ X : Finset V, X ∩ S1 = ∅ → ∑ v ∈ X ∩ S1, x v = 0 := by
    intro X hX; rw [hX]; simp
  have hsumD : ∀ X : Finset V, ∑ v ∈ X \ S1, x v = ∑ v ∈ X \ S1, x' v := by
    intro X
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have : v ∉ S1 := (Finset.mem_sdiff.mp hv).2
    simp [hx, this]
  have hsplit : ∀ X : Finset V, ∑ v ∈ X, x v = ∑ v ∈ X ∩ S1, x v + ∑ v ∈ X \ S1, x' v := by
    intro X; rw [← hsumD, Finset.sum_inter_add_sum_sdiff]
  refine ⟨x, ?_, ?_⟩
  · intro X hXW
    by_cases hXtop : σ X = ⊤
    · rw [hXtop]; exact le_top
    have hsX := hsub X S1
    obtain ⟨hU, hI, hreal⟩ := submod_real hsX hXtop hS1top
    have hXS1W' : X \ S1 ⊆ W' := Finset.sdiff_subset_sdiff hXW le_rfl
    have hx'X := hx'1 (X \ S1) hXS1W'
    rcases (X ∩ S1).eq_empty_or_nonempty with hE | hNE
    · -- `X` misses `S1`
      have hXd : X \ S1 = X := by
        ext a; simp only [Finset.mem_sdiff]
        constructor
        · exact fun h => h.1
        · intro ha; refine ⟨ha, fun hb => ?_⟩
          have : a ∈ X ∩ S1 := Finset.mem_inter.mpr ⟨ha, hb⟩
          rw [hE] at this; simp at this
      rw [hsplit, hsumE X hE, zero_add]
      rw [hXd] at hx'X ⊢
      simp only [hσ'] at hx'X
      have hU' : σ (S1 ∪ X) ≠ ⊤ := by rwa [Finset.union_comm]
      rw [← WithTop.coe_untop _ hU', ← WithTop.coe_add, WithTop.coe_le_coe] at hx'X
      rw [← WithTop.coe_untop _ hXtop, WithTop.coe_le_coe]
      have hI0 : (σ (X ∩ S1)).untop hI = 0 := by
        have : σ (X ∩ S1) = 0 := by rw [hE, hσ0]
        simp [this]
      have hUeq : (σ (X ∪ S1)).untop hU = (σ (S1 ∪ X)).untop hU' := by
        simp [Finset.union_comm]
      have : (σ S1).untop hS1top = r := rfl
      linarith
    · -- `X` contains `S1`
      have hXS : X ∩ S1 = S1 := hmin _ Finset.inter_subset_right hNE hI
      have hS1X : S1 ⊆ X := by rw [← hXS]; exact Finset.inter_subset_left
      rw [hsplit, hsumS1 X hXS]
      have hUX : S1 ∪ (X \ S1) = X := Finset.union_sdiff_of_subset hS1X
      simp only [hσ', hUX] at hx'X
      rw [← WithTop.coe_untop _ hXtop, ← WithTop.coe_add, WithTop.coe_le_coe] at hx'X
      rw [← WithTop.coe_untop _ hXtop, WithTop.coe_le_coe]
      linarith
  · rw [hsplit, hsumS1 W (Finset.inter_eq_right.mpr hS1W)]
    have hW'eq : W \ S1 = W' := rfl
    rw [hW'eq, WithTop.coe_add, hx'2]
    simp only [hσ', hS1W']
    rw [← WithTop.coe_untop _ hσW, ← WithTop.coe_add, ← WithTop.coe_add]
    congr 1
    ring

end BasePolyNonemptyCore

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (ρ : Finset V → WithTop ℝ) (hρ : SubmodularSetFunction ρ) :
    (BasePolyhedron ρ).Nonempty := by
  obtain ⟨h0, hV, hsub⟩ := hρ
  obtain ⟨x, hx1, hx2⟩ := BasePolyNonemptyCore.core _ Finset.univ rfl ρ h0 hV hsub
  exact ⟨x, fun X => hx1 X (Finset.subset_univ X), hx2⟩

#print axioms solution
