-- Prove2me | solution 2 for ChvatalPolytopes.Perfect.clique_system_defines_iff_perfect
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:10:52.442303+00:00
-- url     : https://prove2.me/submissions/49e300c1-1cdf-48d1-be9d-2d95cbd13cad

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect
import Theorems.Thm_ChvatalPolytopes_Perfect_exists_induced_indepNum_mul_cliqueNum_lt

-- carved verbatim out of submission 877250d2-1524-4355-8146-accd2127e3a7, lines 963-968

section
open ChvatalPolytopes
open ChvatalPolytopes.Perfect

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

theorem card_inter_le_one_P {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S K : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (hK : G.IsClique (K : Set V)) : (S ∩ K).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  rw [Finset.mem_inter] at ha hb
  exact hS ha.1 hb.1 hab (hK ha.2 hb.2 hab)

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

theorem rep_step_P {X : Type*} [DecidableEq X] (H : SimpleGraph X) (A' : Finset X) (x0 x1 : X)
    (hx0 : x0 ∈ A') (hx1 : x1 ∈ A') (hne : x0 ≠ x1) (htw : ∀ z, H.Adj x1 z ↔ H.Adj x0 z)
    (case1 : ∀ B ⊆ A'.erase x1, GoodP H B) : GoodP H A' := by
  classical
  set Hs := A'.erase x1 with hHs
  have huH : x0 ∈ Hs := Finset.mem_erase.mpr ⟨hne, hx0⟩
  have hnH : x1 ∉ Hs := by simp [hHs]
  have hAH : A' = insert x1 Hs := by rw [hHs, Finset.insert_erase hx1]
  obtain ⟨S, hSH, hSi, F, hFc, hFcov, hFS⟩ := case1 Hs (subset_refl _)
  by_cases h2a : ∃ T ⊆ Hs, H.IsIndepSet (T : Set X) ∧ x0 ∈ T ∧ F.card ≤ T.card
  · obtain ⟨T, hTH, hTi, huT, hFT⟩ := h2a
    have hnT : x1 ∉ T := fun h => hnH (hTH h)
    refine ⟨insert x1 T, ?_, ?_, insert {x1} F, ?_, ?_, ?_⟩
    · rw [hAH]; exact Finset.insert_subset_insert _ hTH
    · rw [Finset.coe_insert, SimpleGraph.IsIndepSet, Set.pairwise_insert]
      refine ⟨hTi, ?_⟩
      intro y hy _
      have key : ¬ H.Adj x1 y := by
        intro hadj
        rw [htw] at hadj
        have hne' : x0 ≠ y := fun h => H.loopless.irrefl _ (h ▸ hadj)
        exact hTi huT hy hne' hadj
      exact ⟨key, fun h => key h.symm⟩
    · intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · simp
      · exact hFc W hW
    · intro x hx
      rw [hAH] at hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨{x}, Finset.mem_insert_self _ _, Finset.mem_singleton_self _⟩
      · obtain ⟨W, hW, hxW⟩ := hFcov x hx
        exact ⟨W, Finset.mem_insert_of_mem hW, hxW⟩
    · rw [Finset.card_insert_of_notMem hnT]
      exact (Finset.card_insert_le _ _).trans (by omega)
  · push_neg at h2a
    obtain ⟨W0, hW0, huW0⟩ := hFcov x0 huH
    set D := W0.erase x0 with hD
    set H2 := Hs \ D with hH2
    obtain ⟨S2, hS2H, hS2i, F2, hF2c, hF2cov, hF2S⟩ := case1 H2 Finset.sdiff_subset
    have hS2lt : S2.card < F.card := by
      by_cases huS2 : x0 ∈ S2
      · exact h2a S2 (hS2H.trans Finset.sdiff_subset) hS2i huS2
      · have hle : S2.card ≤ (F.erase W0).card := by
          apply weak_dual_P _ S2 hS2i
          · intro W hW; exact hFc W (Finset.mem_of_mem_erase hW)
          · intro x hx
            have hxH : x ∈ Hs := (Finset.mem_sdiff.mp (hS2H hx)).1
            obtain ⟨W, hW, hxW⟩ := hFcov x hxH
            refine ⟨W, Finset.mem_erase.mpr ⟨?_, hW⟩, hxW⟩
            rintro rfl
            have hxD : x ∈ D := Finset.mem_erase.mpr ⟨fun h => huS2 (h ▸ hx), hxW⟩
            exact (Finset.mem_sdiff.mp (hS2H hx)).2 hxD
        rw [Finset.card_erase_of_mem hW0] at hle
        have : 0 < F.card := Finset.card_pos.mpr ⟨W0, hW0⟩
        omega
    refine ⟨S, hSH.trans (by rw [hAH]; exact Finset.subset_insert _ _), hSi,
      insert (insert x1 D) F2, ?_, ?_, ?_⟩
    · intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · rw [Finset.coe_insert, SimpleGraph.isClique_insert]
        refine ⟨(hFc W0 hW0).subset (by intro x hx; exact Finset.mem_of_mem_erase hx), ?_⟩
        intro y hy _
        have hyW0 : y ∈ W0 := Finset.mem_of_mem_erase hy
        have hyu : y ≠ x0 := Finset.ne_of_mem_erase hy
        have hadj := hFc W0 hW0 huW0 hyW0 (Ne.symm hyu)
        exact (htw y).mpr hadj
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

theorem rep_good_P {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hG : ∀ B, GoodP G B) : ∀ A : Finset (V × ℕ), GoodP (G.comap Prod.fst) A := by
  classical
  intro A
  induction' hn : A.card using Nat.strong_induction_on with n ih generalizing A
  by_cases hinj : Set.InjOn Prod.fst (A : Set (V × ℕ))
  · exact good_of_map_P G _ Prod.fst (fun x y => by simp) A hinj (hG _)
  · simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨x0, hx0, x1, hx1, heq, hne⟩ := hinj
    apply rep_step_P _ A x0 x1 hx0 hx1 hne (fun z => by simp [heq])
    intro B hB
    apply ih B.card _ B rfl
    rw [← hn]
    exact lt_of_le_of_lt (Finset.card_le_card hB) (Finset.card_erase_lt_of_mem hx1)

theorem weighted_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : ∀ B, GoodP G B) (w : V → ℕ) :
    ∃ s : Finset V, G.IsIndepSet (s : Set V) ∧ ∃ lam : Finset V → ℝ, (∀ W, 0 ≤ lam W) ∧
      (∀ u, (w u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
      ∑ W ∈ maximalCliques G, lam W ≤ ∑ u ∈ s, (w u : ℝ) := by
  classical
  set Aw : Finset (V × ℕ) := Finset.univ.biUnion (fun u => (Finset.range (w u)).image (fun i => (u, i)))
    with hAw
  have hmem : ∀ p, p ∈ Aw ↔ p.2 < w p.1 := by
    intro p
    simp only [hAw, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_range]
    constructor
    · rintro ⟨u, i, hi, rfl⟩; exact hi
    · intro h; exact ⟨p.1, p.2, h, rfl⟩
  obtain ⟨S, hSA, hSi, F, hFc, hFcov, hFS⟩ := rep_good_P G hG Aw
  have himgc : ∀ W ∈ F, G.IsClique ((W.image Prod.fst : Finset V) : Set V) := by
    intro W hW a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    have hpq : p ≠ q := fun h => hab (h ▸ rfl)
    simpa using hFc W hW hp hq hpq
  choose! g hg1 hg2 using fun W (hW : W ∈ F) => exists_maxClique_P G _ (himgc W hW)
  refine ⟨S.image Prod.fst, ?_, fun M => ((F.filter (fun W => g W = M)).card : ℝ), ?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    have hpq : p ≠ q := fun h => hab (h ▸ rfl)
    simpa using hSi hp hq hpq
  · intro M; positivity
  · intro u
    choose! Wc hWc1 hWc2 using hFcov
    have h1 : w u ≤ (F.filter (fun W => u ∈ g W)).card := by
      have key := Finset.card_le_card_of_injOn (fun i => Wc (u, i)) (s := Finset.range (w u))
        (t := F.filter (fun W => u ∈ g W)) ?_ ?_
      · simpa using key
      · intro i hi
        rw [Finset.mem_coe]
        have hi' : (u, i) ∈ Aw := (hmem _).mpr (by simpa using hi)
        refine Finset.mem_filter.mpr ⟨hWc1 _ hi', hg2 _ (hWc1 _ hi') ?_⟩
        exact Finset.mem_image.mpr ⟨(u, i), hWc2 _ hi', rfl⟩
      · intro i hi j hj hij
        by_contra hne
        have hi' : (u, i) ∈ Aw := (hmem _).mpr (by simpa using hi)
        have hj' : (u, j) ∈ Aw := (hmem _).mpr (by simpa using hj)
        have a1 := hWc2 _ hi'
        have a2 := hWc2 _ hj'
        simp only at hij
        rw [hij] at a1
        have := hFc _ (hWc1 _ hj') a1 a2 (by simpa using hne)
        simp at this
    have h2 : (F.filter (fun W => u ∈ g W)).card =
        ∑ M ∈ (maximalCliques G).filter (fun W => u ∈ W), (F.filter (fun W => g W = M)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := g)
        (t := (maximalCliques G).filter (fun W => u ∈ W))]
      · apply Finset.sum_congr rfl
        intro M hM
        congr 1
        ext W
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩
          refine ⟨⟨h1, ?_⟩, h3⟩
          rw [h3]; exact (Finset.mem_filter.mp hM).2
      · intro W hW
        simp only [Finset.mem_coe, Finset.mem_filter] at hW ⊢
        exact ⟨hg1 W hW.1, hW.2⟩
    have : (w u : ℝ) ≤ ((F.filter (fun W => u ∈ g W)).card : ℝ) := by exact_mod_cast h1
    rw [h2] at this
    push_cast at this
    exact this
  · have e1 : F.card = ∑ M ∈ maximalCliques G, (F.filter (fun W => g W = M)).card :=
      Finset.card_eq_sum_card_fiberwise (fun W hW => hg1 W hW)
    have e2 : S.card = ∑ u ∈ S.image Prod.fst, (S.filter (fun p => p.1 = u)).card :=
      Finset.card_eq_sum_card_fiberwise (fun p hp => Finset.mem_image_of_mem _ hp)
    have e3 : ∀ u, (S.filter (fun p => p.1 = u)).card ≤ w u := by
      intro u
      have := Finset.card_le_card_of_injOn (fun p : V × ℕ => p.2)
        (s := S.filter (fun p => p.1 = u)) (t := Finset.range (w u)) ?_ ?_
      · simpa using this
      · intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter] at hp
        have := (hmem p).mp (hSA hp.1)
        rw [hp.2] at this
        simpa using this
      · intro p hp q hq hpq
        rw [Finset.coe_filter] at hp hq
        exact Prod.ext (hp.2.trans hq.2.symm) hpq
    have : F.card ≤ ∑ u ∈ S.image Prod.fst, w u :=
      hFS.trans (e2 ▸ Finset.sum_le_sum (fun u _ => e3 u))
    rw [e1] at this
    push_cast
    exact_mod_cast this

theorem inc_sum_P {V : Type*} [Fintype V] [DecidableEq V] (c : V → ℝ) (s : Finset V) :
    ∑ u, c u * incidenceVector s u = ∑ u ∈ s, c u := by
  simp [incidenceVector, mul_ite, Finset.sum_ite_mem]

theorem swap_P {V : Type*} [DecidableEq V] (M : Finset (Finset V)) (lam : Finset V → ℝ)
    (T : Finset V) (y : V → ℝ) :
    ∑ u ∈ T, y u * ∑ W ∈ M.filter (fun W => u ∈ W), lam W =
      ∑ W ∈ M, lam W * ∑ u ∈ T.filter (· ∈ W), y u := by
  simp only [Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W _
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> ring

theorem weak_real_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : V → ℝ)
    (s : Finset V) (hs : G.IsIndepSet (s : Set V)) (lam : Finset V → ℝ)
    (hl : ∀ W ∈ maximalCliques G, 0 ≤ lam W)
    (hcov : ∀ u, c u ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) :
    ∑ u ∈ s, c u ≤ ∑ W ∈ maximalCliques G, lam W := by
  calc ∑ u ∈ s, c u ≤ ∑ u ∈ s, 1 * ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W :=
        Finset.sum_le_sum (fun u _ => by rw [one_mul]; exact hcov u)
    _ = ∑ W ∈ maximalCliques G, lam W * ∑ u ∈ s.filter (· ∈ W), (1:ℝ) := swap_P _ _ _ _
    _ ≤ ∑ W ∈ maximalCliques G, lam W := by
        apply Finset.sum_le_sum
        intro W hW
        have hWc : G.IsClique (W : Set V) := ((mem_maximalCliques G W).mp hW).prop
        have h1 : (s.filter (· ∈ W)).card ≤ 1 := by
          rw [Finset.filter_mem_eq_inter]
          exact card_inter_le_one_P G s W hs hWc
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact mul_le_of_le_one_right (hl W hW) (by exact_mod_cast h1)

theorem stableMax_exists_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V → ℝ) : ∃ m, IsStableMax G c m := by
  classical
  set P := Finset.univ.filter (fun s : Finset V => G.IsIndepSet (s : Set V)) with hP
  have hPn : P.Nonempty := ⟨∅, by simp [hP]⟩
  obtain ⟨s, hs, hse⟩ := P.exists_mem_eq_sup' hPn (fun s => ∑ u ∈ s, c u)
  refine ⟨∑ u ∈ s, c u, ⟨incidenceVector s, ⟨s, (Finset.mem_filter.mp hs).2, rfl⟩,
    inc_sum_P c s⟩, ?_⟩
  rintro x ⟨t, ht, rfl⟩
  rw [inc_sum_P, ← hse]
  exact Finset.le_sup' (fun s => ∑ u ∈ s, c u) (by simp [hP, ht])

theorem ii_iii_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : IsPerfect G) (c : V → ℤ) : ∃ m : ℝ, IsStableMax G (fun u => (c u : ℝ)) m ∧
        (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) ∧
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
          ∑ W ∈ maximalCliques G, lam W = m) ∧
        (∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) →
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
          m ≤ ∑ W ∈ maximalCliques G, lam W) := by
  classical
  obtain ⟨m, ⟨⟨x, ⟨s0, hs0, rfl⟩, hm⟩, hmax⟩⟩ := stableMax_exists_P G (fun u => (c u : ℝ))
  rw [inc_sum_P] at hm
  have hlow : ∀ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) →
      (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) →
      m ≤ ∑ W ∈ maximalCliques G, lam W := fun lam hl hc =>
    hm ▸ weak_real_P G _ s0 hs0 lam hl hc
  obtain ⟨s, hs, lam, hl, hcov, hsum⟩ :=
    weighted_P G (good_of_perfect_P G hG) (fun u => (c u).toNat)
  have hcov' : ∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W := by
    intro u
    refine le_trans ?_ (hcov u)
    have := Int.self_le_toNat (c u)
    exact_mod_cast this
  refine ⟨m, ⟨⟨_, ⟨s0, hs0, rfl⟩, by rw [inc_sum_P]; exact hm⟩, hmax⟩,
    ⟨lam, fun W _ => hl W, hcov', ?_⟩, hlow⟩
  apply le_antisymm _ (hlow lam (fun W _ => hl W) hcov')
  refine hsum.trans ?_
  set s' := s.filter (fun u => 0 ≤ c u) with hs'
  have e : ∑ u ∈ s, (((c u).toNat : ℕ) : ℝ) = ∑ u ∈ s', (c u : ℝ) := by
    rw [hs', Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : 0 ≤ c u
    · rw [if_pos h]
      have : ((c u).toNat : ℤ) = c u := Int.toNat_of_nonneg h
      exact_mod_cast this
    · rw [if_neg h]
      have : (c u).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      simp [this]
  rw [e]
  have hs'i : G.IsIndepSet (s' : Set V) := by
    intro a ha b hb hab
    exact hs (Finset.mem_of_mem_filter a ha) (Finset.mem_of_mem_filter b hb) hab
  have := hmax (incidenceVector s') ⟨s', hs'i, rfl⟩
  rwa [inc_sum_P] at this

theorem sep_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h3 : ∀ c : V → ℤ, ∃ m : ℝ, IsStableMax G (fun u => (c u : ℝ)) m ∧
        (∃ lam : Finset V → ℝ, (∀ W ∈ maximalCliques G, 0 ≤ lam W) ∧
          (∀ u, (c u : ℝ) ≤ ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W) ∧
          ∑ W ∈ maximalCliques G, lam W = m)) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} ⊆
      stablePolytope G := by
  classical
  rintro y ⟨hy0, hyW⟩
  by_contra hny
  have hy1 : ∀ u, y u ≤ 1 := by
    intro u
    obtain ⟨M, hM, hsub⟩ := exists_maxClique_P G {u} (by simp)
    have := hyW M hM
    have h2 := Finset.single_le_sum (f := y) (fun v _ => hy0 v)
      (hsub (Finset.mem_singleton_self u))
    linarith
  have hfin : (stableVectors G).Finite :=
    (Set.finite_range (incidenceVector (V := V))).subset (by rintro x ⟨s, _, rfl⟩; exact ⟨s, rfl⟩)
  obtain ⟨f, a, b, hfa, hab, hfb⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ (stableVectors G)) (hfin.isCompact_convexHull ℝ) (convex_singleton (𝕜 := ℝ) y)
    isClosed_singleton (Set.disjoint_singleton_right.mpr hny)
  set c : V → ℝ := fun u => f (fun j => if u = j then 1 else 0) with hc
  have hrep : ∀ z, f z = ∑ u, c u * z u := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ (f : (V → ℝ) →ₗ[ℝ] ℝ) z
    simp only [ContinuousLinearMap.coe_coe, smul_eq_mul] at this
    rw [this]
    apply Finset.sum_congr rfl
    intro u _
    ring
  have hfy : b < f y := hfb y rfl
  set n := Fintype.card V with hn
  obtain ⟨N, hN⟩ := exists_nat_gt ((n : ℝ) / (b - a))
  have hba : 0 < b - a := by linarith
  have hNn : (n : ℝ) < N * (b - a) := by rw [div_lt_iff₀ hba] at hN; linarith
  have hN0 : (0 : ℝ) < N := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  set c' : V → ℤ := fun u => ⌊(N : ℝ) * c u⌋ with hc'
  obtain ⟨m, ⟨⟨z, ⟨s, hs, rfl⟩, hzm⟩, _⟩, lam, hl, hcov, hsum⟩ := h3 c'
  have hz0 : ∀ u, 0 ≤ incidenceVector s u := fun u => by
    unfold incidenceVector; split_ifs <;> norm_num
  have hmle : m ≤ N * a := by
    rw [← hzm]
    have hfz : f (incidenceVector s) < a := hfa _ (subset_convexHull ℝ _ ⟨s, hs, rfl⟩)
    rw [hrep] at hfz
    calc ∑ u, (c' u : ℝ) * incidenceVector s u ≤ ∑ u, ((N : ℝ) * c u) * incidenceVector s u :=
          Finset.sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (Int.floor_le _) (hz0 u))
      _ = N * ∑ u, c u * incidenceVector s u := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
      _ ≤ N * a := mul_le_mul_of_nonneg_left hfz.le (Nat.cast_nonneg N)
  have hylow : (N : ℝ) * f y - n ≤ ∑ u, (c' u : ℝ) * y u := by
    rw [hrep, Finset.mul_sum]
    have : (n : ℝ) = ∑ u : V, (1 : ℝ) := by simp [hn]
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro u _
    have h1 := Int.sub_one_lt_floor ((N : ℝ) * c u)
    have h2 := hy0 u
    have h3 := hy1 u
    have h4 := mul_nonneg (sub_nonneg.mpr h1.le) h2
    show (N : ℝ) * (c u * y u) - 1 ≤ (⌊(N : ℝ) * c u⌋ : ℝ) * y u
    nlinarith
  have hyup : ∑ u, (c' u : ℝ) * y u ≤ m := by
    calc ∑ u, (c' u : ℝ) * y u ≤
          ∑ u, y u * ∑ W ∈ (maximalCliques G).filter (fun W => u ∈ W), lam W :=
          Finset.sum_le_sum (fun u _ => by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hcov u) (hy0 u))
      _ = ∑ W ∈ maximalCliques G, lam W * ∑ u ∈ Finset.univ.filter (· ∈ W), y u :=
          swap_P _ _ _ _
      _ ≤ ∑ W ∈ maximalCliques G, lam W := by
          apply Finset.sum_le_sum
          intro W hW
          have : Finset.univ.filter (· ∈ W) = W := by ext; simp
          rw [this]
          exact mul_le_of_le_one_right (hl W hW) (hyW W hW)
      _ = m := hsum
  have : (N : ℝ) * a < N * f y - n := by nlinarith
  linarith

theorem hull_sub_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    stablePolytope G ⊆
      {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} := by
  classical
  apply convexHull_min
  · rintro x ⟨s, hs, rfl⟩
    refine ⟨fun u => by unfold incidenceVector; split_ifs <;> norm_num, ?_⟩
    intro W hW
    have hWc : G.IsClique (W : Set V) := ((mem_maximalCliques G W).mp hW).prop
    have h1 := card_inter_le_one_P G s W hs hWc
    have : ∑ u ∈ W, incidenceVector s u = ((W.filter (· ∈ s)).card : ℝ) := by
      simp [incidenceVector, Finset.filter_mem_eq_inter]
    rw [this, Finset.filter_mem_eq_inter, Finset.inter_comm]
    exact_mod_cast h1
  · rintro z1 ⟨h10, h11⟩ z2 ⟨h20, h21⟩ t1 t2 ht1 ht2 hsum
    refine ⟨fun u => ?_, fun W hW => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := h10 u; have := h20 u
      positivity
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have := h11 W hW; have := h21 W hW
      nlinarith

theorem i_ii_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (h : {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} =
      stablePolytope G) : IsPerfect G := by
  classical
  by_contra hG
  obtain ⟨A, hA⟩ := ChvatalPolytopes.Perfect.exists_induced_indepNum_mul_cliqueNum_lt G hG
  set a := (G.induce (A : Set V)).indepNum with ha
  set k := (G.induce (A : Set V)).cliqueNum with hk
  have hAne : A.Nonempty := by
    by_contra h'
    rw [Finset.not_nonempty_iff_eq_empty] at h'
    subst h'
    simp at hA
  obtain ⟨v, hv⟩ := hAne
  have hk1 : 1 ≤ k := by
    have := SimpleGraph.IsClique.card_le_cliqueNum (G := G.induce (A : Set V))
      (t := {⟨v, hv⟩}) (tc := by simp)
    simpa using this
  have hcl : ∀ W : Finset V, G.IsClique (W : Set V) → (W.filter (· ∈ A)).card ≤ k := by
    intro W hW
    have := SimpleGraph.IsClique.card_le_cliqueNum (G := G.induce (A : Set V))
      (t := W.subtype (· ∈ (A : Set V))) (tc := by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_subtype] at hx hy
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        exact hW hx hy (fun e => hxy (Subtype.ext e)))
    rw [Finset.card_subtype] at this
    simpa using this
  have hind : ∀ s : Finset V, G.IsIndepSet (s : Set V) → (s.filter (· ∈ A)).card ≤ a := by
    intro s hs
    have := SimpleGraph.IsIndepSet.card_le_indepNum (G := G.induce (A : Set V))
      (t := s.subtype (· ∈ (A : Set V))) (by
        intro x hx y hy hxy
        rw [Finset.mem_coe, Finset.mem_subtype] at hx hy
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        exact hs hx hy (fun e => hxy (Subtype.ext e)))
    rw [Finset.card_subtype] at this
    simpa using this
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  set x : V → ℝ := fun u => if u ∈ A then 1 / (k : ℝ) else 0 with hx
  have hsumx : ∀ T : Finset V, ∑ u ∈ T, x u = (T.filter (· ∈ A)).card * (1 / (k : ℝ)) := by
    intro T
    rw [hx, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hxf : x ∈ {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} := by
    refine ⟨fun u => by simp only [hx]; split_ifs <;> positivity, fun W hW => ?_⟩
    have hWc : G.IsClique (W : Set V) := ((mem_maximalCliques G W).mp hW).prop
    rw [hsumx]
    have h1 : ((W.filter (· ∈ A)).card : ℝ) ≤ k := by exact_mod_cast hcl W hWc
    rw [mul_one_div, div_le_one hkpos]
    exact h1
  rw [h] at hxf
  have hT : stablePolytope G ⊆ {z : V → ℝ | ∑ u ∈ A, z u ≤ a} := by
    apply convexHull_min
    · rintro z ⟨s, hs, rfl⟩
      simp only [Set.mem_setOf_eq]
      have : ∑ u ∈ A, incidenceVector s u = ((s.filter (· ∈ A)).card : ℝ) := by
        simp only [incidenceVector, Finset.sum_boole]
        rw [Finset.filter_mem_eq_inter, Finset.filter_mem_eq_inter, Finset.inter_comm]
      rw [this]
      exact_mod_cast hind s hs
    · intro z1 hz1 z2 hz2 t1 t2 ht1 ht2 hsum
      simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hz1 hz2 ⊢
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      nlinarith
  have := hT hxf
  simp only [Set.mem_setOf_eq] at this
  rw [hsumx, Finset.filter_true_of_mem (fun u hu => hu)] at this
  rw [mul_one_div, div_le_iff₀ hkpos] at this
  have h2 : A.card ≤ a * k := by exact_mod_cast this
  omega

theorem clique_system_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} = stablePolytope G ↔
      IsPerfect G :=
  ⟨i_ii_P G, fun hG => Set.Subset.antisymm
    (sep_P G (fun c => by
      obtain ⟨m, h1, h2, _⟩ := ii_iii_P G hG c
      exact ⟨m, h1, h2⟩)) (hull_sub_P G)⟩

end

section
open ChvatalPolytopes.Perfect

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) :
    {x : V → ℝ | (∀ u, 0 ≤ x u) ∧ ∀ W ∈ maximalCliques G, ∑ u ∈ W, x u ≤ 1} = stablePolytope G ↔
      IsPerfect G := by
  exact clique_system_core G

end
