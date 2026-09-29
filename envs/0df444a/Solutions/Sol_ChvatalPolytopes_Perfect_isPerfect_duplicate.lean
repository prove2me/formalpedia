-- Prove2me | solution 1 for ChvatalPolytopes.Perfect.isPerfect_duplicate
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:45:26.858012+00:00
-- url     : https://prove2.me/submissions/8340cba6-9052-437b-b62a-fdd5d4e6d52c

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect
import Definitions.Def_ChvatalPolytopes_Perfect_duplicate



namespace ChvatalPolytopes.Perfect

def GoodP {V : Type*} (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∃ S ⊆ A, G.IsIndepSet (S : Set V) ∧ ∃ F : Finset (Finset V),
    (∀ W ∈ F, G.IsClique (W : Set V)) ∧ (∀ x ∈ A, ∃ W ∈ F, x ∈ W) ∧ F.card ≤ S.card

theorem weak_dual_P {V : Type*} (G : SimpleGraph V) (s : Finset V)
    (hs : G.IsIndepSet (s : Set V)) (F : Finset (Finset V))
    (hF : ∀ W ∈ F, G.IsClique (W : Set V)) (hcov : ∀ x ∈ s, ∃ W ∈ F, x ∈ W) :
    s.card ≤ F.card := by
  classical
  choose! f hf1 hf2 using hcov
  apply Finset.card_le_card_of_injOn f (fun x hx => hf1 x hx)
  intro x hx y hy hxy
  by_contra hne
  have h1 := hf2 x hx
  have h2 := hf2 y hy
  rw [hxy] at h1
  exact hs hx hy hne (hF (f y) (hf1 y hy) h1 h2 hne)

theorem exists_maxClique_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (W : Finset V) (hW : G.IsClique (W : Set V)) : ∃ M ∈ maximalCliques G, W ⊆ M := by
  classical
  obtain ⟨b, hab, hb⟩ := Finset.exists_le_maximal
    (Finset.univ.filter (fun W : Finset V => G.IsClique (W : Set V))) (a := W) (by simpa using hW)
  refine ⟨b, ?_, hab⟩
  rw [mem_maximalCliques]
  refine ⟨by simpa using hb.1, fun y hy hby => hb.2 (by simpa using hy) hby⟩

theorem sum01_P {V : Type*} [DecidableEq V] (M : Finset (Finset V)) (lam : Finset V → ℝ)
    (h01 : ∀ W ∈ M, lam W = 0 ∨ lam W = 1) :
    ∑ W ∈ M, lam W = ((M.filter (fun W => lam W = 1)).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro W hW
  rcases h01 W hW with h | h <;> simp [h]

theorem cover01_P {V : Type*} [DecidableEq V] (M : Finset (Finset V)) (lam : Finset V → ℝ)
    (h01 : ∀ W ∈ M, lam W = 0 ∨ lam W = 1) (u : V)
    (h : 1 ≤ ∑ W ∈ M.filter (fun W => u ∈ W), lam W) : ∃ W ∈ M, u ∈ W ∧ lam W = 1 := by
  by_contra hc
  push_neg at hc
  have : ∑ W ∈ M.filter (fun W => u ∈ W), lam W = 0 := by
    apply Finset.sum_eq_zero
    intro W hW
    rw [Finset.mem_filter] at hW
    rcases h01 W hW.1 with h' | h'
    · exact h'
    · exact absurd h' (hc W hW.1 hW.2)
  linarith

theorem csum_P {V : Type*} [Fintype V] [DecidableEq V] (A s : Finset V) :
    ∑ u, (if u ∈ A then (1:ℝ) else 0) * incidenceVector s u = ((s.filter (· ∈ A)).card : ℝ) := by
  rw [Finset.card_filter, Nat.cast_sum]
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · apply Finset.sum_congr rfl
    intro u hu
    simp [incidenceVector, hu]
  · intro u _ hu
    simp [incidenceVector, hu]

theorem good_of_perfect_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsPerfect G) (A : Finset V) : GoodP G A := by
  classical
  obtain ⟨m, ⟨⟨x, ⟨s, hs, rfl⟩, hxm⟩, hmax⟩, ⟨lam, hlam01, hcov, hsum⟩, _⟩ :=
    hG (fun u => if u ∈ A then 1 else 0) (fun u => by by_cases h : u ∈ A <;> simp [h])
  rw [csum_P] at hxm
  rw [sum01_P _ _ hlam01] at hsum
  refine ⟨s.filter (· ∈ A), fun x hx => (Finset.mem_filter.mp hx).2, ?_, ?_⟩
  · intro a ha b hb hab
    exact hs (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab
  refine ⟨(maximalCliques G).filter (fun W => lam W = 1), ?_, ?_, ?_⟩
  · intro W hW
    rw [Finset.mem_filter, mem_maximalCliques] at hW
    exact hW.1.prop
  · intro y hy
    have := hcov y
    simp only [hy, if_true] at this
    obtain ⟨W, hW, hyW, hl⟩ := cover01_P _ lam hlam01 y this
    exact ⟨W, Finset.mem_filter.mpr ⟨hW, hl⟩, hyW⟩
  · have : (((maximalCliques G).filter (fun W => lam W = 1)).card : ℝ) =
        ((s.filter (· ∈ A)).card : ℝ) := by rw [hsum, hxm]
    exact_mod_cast this.le

theorem perfect_of_good_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : ∀ A, GoodP G A) : IsPerfect G := by
  classical
  intro c hc
  set A := Finset.univ.filter (fun u => c u = 1) with hA
  have hcA : c = fun u => if u ∈ A then 1 else 0 := by
    funext u
    rcases hc u with h | h <;> simp [hA, h]
  obtain ⟨S, hSA, hSi, F, hFc, hFcov, hFS⟩ := hG A
  choose! g hg1 hg2 using fun W (hW : W ∈ F) => exists_maxClique_P G W (hFc W hW)
  set F' := F.image g with hF'
  have hF'sub : F' ⊆ maximalCliques G := by
    intro M hM
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hM
    exact hg1 W hW
  have hF'c : ∀ W ∈ F', G.IsClique (W : Set V) := by
    intro W hW
    have := hF'sub hW
    rw [mem_maximalCliques] at this
    exact this.prop
  have hF'cov : ∀ x ∈ A, ∃ W ∈ F', x ∈ W := by
    intro x hx
    obtain ⟨W, hW, hxW⟩ := hFcov x hx
    exact ⟨g W, Finset.mem_image_of_mem g hW, hg2 W hW hxW⟩
  have hF'le : F'.card ≤ S.card := (Finset.card_image_le).trans hFS
  have hSF' : S.card ≤ F'.card := weak_dual_P G S hSi F' hF'c (fun x hx => hF'cov x (hSA hx))
  have hSA' : S.filter (· ∈ A) = S := Finset.filter_true_of_mem (fun x hx => hSA hx)
  refine ⟨S.card, ⟨⟨incidenceVector S, ⟨S, hSi, rfl⟩, ?_⟩, ?_⟩, ?_, ?_⟩
  · rw [hcA, csum_P, hSA']
  · rintro x ⟨s, hs, rfl⟩
    rw [hcA, csum_P]
    have h1 : (s.filter (· ∈ A)).card ≤ F'.card := by
      apply weak_dual_P G _ ?_ F' hF'c
      · intro x hx
        exact hF'cov x (Finset.mem_filter.mp hx).2
      · intro a ha b hb hab
        exact hs (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab
    exact_mod_cast h1.trans hF'le
  · refine ⟨fun W => if W ∈ F' then 1 else 0, ?_, ?_, ?_⟩
    · intro W _
      by_cases h : W ∈ F' <;> simp [h]
    · intro u
      rcases hc u with h | h
      · rw [h]
        apply Finset.sum_nonneg
        intro W _
        by_cases h' : W ∈ F' <;> simp [h']
      · have hu : u ∈ A := by simp [hA, h]
        obtain ⟨W, hW, huW⟩ := hF'cov u hu
        rw [h]
        have hmem : W ∈ (maximalCliques G).filter (fun W => u ∈ W) :=
          Finset.mem_filter.mpr ⟨hF'sub hW, huW⟩
        have := Finset.single_le_sum (f := fun W => if W ∈ F' then (1:ℝ) else 0)
          (fun W _ => by by_cases h' : W ∈ F' <;> simp [h']) hmem
        simpa [hW] using this
    · rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hF'sub]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast le_antisymm hF'le hSF'
  · intro lam hlam01 hcov
    rw [sum01_P _ _ hlam01]
    have : S.card ≤ ((maximalCliques G).filter (fun W => lam W = 1)).card := by
      apply weak_dual_P G S hSi
      · intro W hW
        rw [Finset.mem_filter, mem_maximalCliques] at hW
        exact hW.1.prop
      · intro x hx
        have h1 := hcov x
        have hx1 : c x = 1 := by simpa [hA] using hSA hx
        rw [hx1] at h1
        obtain ⟨W, hW, hxW, hl⟩ := cover01_P _ lam hlam01 x h1
        exact ⟨W, Finset.mem_filter.mpr ⟨hW, hl⟩, hxW⟩
    exact_mod_cast this

theorem good_of_map_P {V V' : Type*} [DecidableEq V] [DecidableEq V'] (G : SimpleGraph V)
    (G' : SimpleGraph V') (φ : V' → V) (hφ : ∀ x y, G'.Adj x y ↔ G.Adj (φ x) (φ y))
    (A' : Finset V') (hinj : Set.InjOn φ A') (hA : GoodP G (A'.image φ)) : GoodP G' A' := by
  obtain ⟨S, hSA, hSi, F, hFc, hFcov, hFS⟩ := hA
  refine ⟨A'.filter (fun x => φ x ∈ S), Finset.filter_subset _ _, ?_, ?_⟩
  · intro x hx y hy hxy hadj
    rw [Finset.coe_filter] at hx hy
    have hne : φ x ≠ φ y := fun h => hxy (hinj hx.1 hy.1 h)
    exact hSi hx.2 hy.2 hne ((hφ x y).mp hadj)
  refine ⟨F.image (fun W => A'.filter (fun x => φ x ∈ W)), ?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hW'
    intro x hx y hy hxy
    rw [Finset.coe_filter] at hx hy
    have hne : φ x ≠ φ y := fun h => hxy (hinj hx.1 hy.1 h)
    exact (hφ x y).mpr (hFc W hW hx.2 hy.2 hne)
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := hFcov (φ x) (Finset.mem_image_of_mem φ hx)
    exact ⟨_, Finset.mem_image_of_mem _ hW, Finset.mem_filter.mpr ⟨hx, hxW⟩⟩
  · have h1 : (A'.filter (fun x => φ x ∈ S)).image φ = S := by
      ext v
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hx⟩, rfl⟩; exact hx
      · intro hv
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hSA hv)
        exact ⟨x, ⟨hx, hv⟩, rfl⟩
    have h2 : ((A'.filter (fun x => φ x ∈ S)).image φ).card = (A'.filter (fun x => φ x ∈ S)).card :=
      Finset.card_image_of_injOn (hinj.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))
    rw [h1] at h2
    rw [← h2]
    exact Finset.card_image_le.trans hFS

theorem dup_adj_P {V : Type*} (G : SimpleGraph V) (u : V) (x y : Option V) :
    (duplicate G u).Adj x y ↔ G.Adj (x.getD u) (y.getD u) := by
  cases x <;> cases y <;> simp [duplicate]

theorem dup_good_P {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V)
    (hG : ∀ A, GoodP G A) (A' : Finset (Option V)) : GoodP (duplicate G u) A' := by
  classical
  have case1 : ∀ B : Finset (Option V), ¬ (none ∈ B ∧ some u ∈ B) → GoodP (duplicate G u) B := by
    intro B hB
    apply good_of_map_P G _ (fun x => x.getD u) (dup_adj_P G u) B ?_ (hG _)
    intro x hx y hy hxy
    cases x <;> cases y <;> simp_all
  by_cases hA : none ∈ A' ∧ some u ∈ A'
  swap
  · exact case1 A' hA
  obtain ⟨hn, hu⟩ := hA
  set H := A'.erase none with hH
  have huH : some u ∈ H := Finset.mem_erase.mpr ⟨by simp, hu⟩
  have hnH : none ∉ H := by simp [hH]
  have hAH : A' = insert none H := by rw [hH, Finset.insert_erase hn]
  obtain ⟨S, hSH, hSi, F, hFc, hFcov, hFS⟩ := case1 H (fun h => hnH h.1)
  by_cases h2a : ∃ T ⊆ H, (duplicate G u).IsIndepSet (T : Set (Option V)) ∧ some u ∈ T ∧
      F.card ≤ T.card
  · obtain ⟨T, hTH, hTi, huT, hFT⟩ := h2a
    have hnT : none ∉ T := fun h => hnH (hTH h)
    refine ⟨insert none T, ?_, ?_, insert {none} F, ?_, ?_, ?_⟩
    · rw [hAH]; exact Finset.insert_subset_insert _ hTH
    · rw [Finset.coe_insert, SimpleGraph.IsIndepSet, Set.pairwise_insert]
      refine ⟨hTi, ?_⟩
      intro y hy _
      have key : ¬ (duplicate G u).Adj none y := by
        intro hadj
        rcases y with _ | w
        · exact (duplicate G u).loopless.irrefl _ hadj
        · have : (duplicate G u).Adj (some u) (some w) := hadj
          have hne : some u ≠ some w := fun h => (duplicate G u).loopless.irrefl _ (h ▸ this)
          exact hTi huT hy hne this
      exact ⟨key, fun h => key h.symm⟩
    · intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · simp
      · exact hFc W hW
    · intro x hx
      rw [hAH] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨{none}, Finset.mem_insert_self _ _, Finset.mem_singleton_self _⟩
      · obtain ⟨W, hW, hxW⟩ := hFcov x hx
        exact ⟨W, Finset.mem_insert_of_mem hW, hxW⟩
    · rw [Finset.card_insert_of_notMem hnT]
      exact (Finset.card_insert_le _ _).trans (by omega)
  · push_neg at h2a
    obtain ⟨W0, hW0, huW0⟩ := hFcov (some u) huH
    set D := W0.erase (some u) with hD
    set H2 := H \ D with hH2
    have hnH2 : none ∉ H2 := fun h => hnH (Finset.mem_sdiff.mp h).1
    obtain ⟨S2, hS2H, hS2i, F2, hF2c, hF2cov, hF2S⟩ := case1 H2 (fun h => hnH2 h.1)
    have hS2lt : S2.card < F.card := by
      by_cases huS2 : some u ∈ S2
      · exact h2a S2 (hS2H.trans Finset.sdiff_subset) hS2i huS2
      · have hle : S2.card ≤ (F.erase W0).card := by
          apply weak_dual_P _ S2 hS2i
          · intro W hW; exact hFc W (Finset.mem_of_mem_erase hW)
          · intro x hx
            have hxH : x ∈ H := (Finset.mem_sdiff.mp (hS2H hx)).1
            obtain ⟨W, hW, hxW⟩ := hFcov x hxH
            refine ⟨W, Finset.mem_erase.mpr ⟨?_, hW⟩, hxW⟩
            rintro rfl
            have hxD : x ∈ D := Finset.mem_erase.mpr ⟨fun h => huS2 (h ▸ hx), hxW⟩
            exact (Finset.mem_sdiff.mp (hS2H hx)).2 hxD
        rw [Finset.card_erase_of_mem hW0] at hle
        have : 0 < F.card := Finset.card_pos.mpr ⟨W0, hW0⟩
        omega
    refine ⟨S, hSH.trans (by rw [hAH]; exact Finset.subset_insert _ _), hSi,
      insert (insert none D) F2, ?_, ?_, ?_⟩
    · intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · rw [Finset.coe_insert, SimpleGraph.isClique_insert]
        refine ⟨(hFc W0 hW0).subset (by intro x hx; exact Finset.mem_of_mem_erase hx), ?_⟩
        intro y hy hny
        have hyW0 : y ∈ W0 := Finset.mem_of_mem_erase hy
        have hyu : y ≠ some u := Finset.ne_of_mem_erase hy
        have hadj := hFc W0 hW0 huW0 hyW0 (Ne.symm hyu)
        rcases y with _ | w
        · exact absurd rfl hny
        · exact hadj
      · exact hF2c W hW
    · intro x hx
      rw [hAH] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_insert_self _ _⟩
      · by_cases hxD : x ∈ D
        · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hxD⟩
        · obtain ⟨W, hW, hxW⟩ := hF2cov x (Finset.mem_sdiff.mpr ⟨hx, hxD⟩)
          exact ⟨W, Finset.mem_insert_of_mem hW, hxW⟩
    · exact (Finset.card_insert_le _ _).trans (by omega)

theorem isPerfect_duplicate_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) (u : V) :
    IsPerfect (duplicate G u) :=
  perfect_of_good_P _ (dup_good_P G u (good_of_perfect_P G hG))

end ChvatalPolytopes.Perfect

open ChvatalPolytopes.Perfect


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPerfect G) (u : V) :
    IsPerfect (duplicate G u) := by
  exact isPerfect_duplicate_core G hG u
