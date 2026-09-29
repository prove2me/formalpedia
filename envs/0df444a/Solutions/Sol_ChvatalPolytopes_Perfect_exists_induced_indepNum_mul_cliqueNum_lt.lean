-- Prove2me | solution 1 for ChvatalPolytopes.Perfect.exists_induced_indepNum_mul_cliqueNum_lt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:50:56.771997+00:00
-- url     : https://prove2.me/submissions/ab1e5d1d-4668-4bb3-a07c-3cad123b8f48

import Mathlib
import Definitions.Def_ChvatalPolytopes_Perfect_StablePolytope
import Definitions.Def_ChvatalPolytopes_Perfect_IsPerfect



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

theorem indepNum_induce_le_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) (α : ℕ) (h : ∀ S ⊆ A, G.IsIndepSet (S : Set V) → S.card ≤ α) :
    (G.induce (A : Set V)).indepNum ≤ α := by
  obtain ⟨s, hs⟩ := (G.induce (A : Set V)).exists_isNIndepSet_indepNum
  rw [← hs.card_eq, ← Finset.card_map (Function.Embedding.subtype _)]
  apply h
  · intro x hx
    simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
    obtain ⟨y, _, rfl⟩ := hx
    exact y.2
  · intro x hx y hy hxy
    simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
      Finset.mem_coe] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have hne : x' ≠ y' := fun h => hxy (h ▸ rfl)
    have := hs.isIndepSet hx' hy' hne
    simpa using this

theorem cliqueNum_induce_le_P {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A : Finset V) (ω : ℕ) (h : ∀ S ⊆ A, G.IsClique (S : Set V) → S.card ≤ ω) :
    (G.induce (A : Set V)).cliqueNum ≤ ω := by
  obtain ⟨s, hs⟩ := (G.induce (A : Set V)).exists_isNClique_cliqueNum
  rw [SimpleGraph.isNClique_induce_iff] at hs
  rw [← hs.card_eq]
  apply h _ ?_ hs.isClique
  intro x hx
  simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact y.2

theorem color_of_cover_P {V : Type*} [DecidableEq V] (G : SimpleGraph V) (B : Finset V)
    (F : Finset (Finset V)) (hF : ∀ W ∈ F, G.IsClique (W : Set V))
    (hcov : ∀ x ∈ B, ∃ W ∈ F, x ∈ W) (α : ℕ) (hα : 0 < α) (hFα : F.card ≤ α) :
    ∃ c : V → Fin α, ∀ x ∈ B, ∀ y ∈ B, x ≠ y → c x = c y → G.Adj x y := by
  classical
  choose! W hW1 hW2 using hcov
  let e : Finset V → Fin α := fun U =>
    if h : U ∈ F then Fin.castLE hFα (F.equivFin ⟨U, h⟩) else ⟨0, hα⟩
  refine ⟨fun x => e (W x), ?_⟩
  intro x hx y hy hxy hc
  have hWe : W x = W y := by
    simp only [e, dif_pos (hW1 x hx), dif_pos (hW1 y hy)] at hc
    have := F.equivFin.injective (Fin.castLE_injective hFα hc)
    simpa using this
  have h1 := hW2 x hx
  have h2 := hW2 y hy
  rw [hWe] at h1
  exact hF (W y) (hW1 y hy) h1 h2 hxy

theorem card_inter_le_one_P {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S K : Finset V)
    (hS : G.IsIndepSet (S : Set V)) (hK : G.IsClique (K : Set V)) : (S ∩ K).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  rw [Finset.mem_inter] at ha hb
  exact hS ha.1 hb.1 hab (hK ha.2 hb.2 hab)

theorem lovasz_core {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ IsPerfect G) :
    ∃ A : Finset V,
      (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum < A.card := by
  classical
  have hex : ∃ A, ¬ GoodP G A := by
    by_contra h
    push_neg at h
    exact hG (perfect_of_good_P G h)
  obtain ⟨A, hAbad, hAmin⟩ : ∃ A, ¬ GoodP G A ∧ ∀ B ⊂ A, GoodP G B := by
    obtain ⟨A0, hA0⟩ := hex
    obtain ⟨A, hA⟩ := (Finset.univ.filter (fun A => ¬ GoodP G A)).exists_minimal
      ⟨A0, by simpa using hA0⟩
    refine ⟨A, by simpa using hA.1, fun B hB => ?_⟩
    by_contra hBg
    have := hA.2 (by simpa using hBg) hB.le
    exact hB.2 this
  -- alpha and omega
  set PI : Finset (Finset V) := A.powerset.filter (fun S : Finset V => G.IsIndepSet (S : Set V)) with hPI
  set PC : Finset (Finset V) := A.powerset.filter (fun S : Finset V => G.IsClique (S : Set V)) with hPC
  set α := PI.sup Finset.card with hαdef
  set ω := PC.sup Finset.card with hωdef
  have hαle : ∀ S ⊆ A, G.IsIndepSet (S : Set V) → S.card ≤ α := fun S hS hi =>
    Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hi⟩)
  have hωle : ∀ S ⊆ A, G.IsClique (S : Set V) → S.card ≤ ω := fun S hS hi =>
    Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hi⟩)
  obtain ⟨S0, hS0, hS0e⟩ := Finset.exists_mem_eq_sup PI
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp⟩⟩ Finset.card
  obtain ⟨K0, hK0, hK0e⟩ := Finset.exists_mem_eq_sup PC
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp⟩⟩ Finset.card
  rw [← hαdef] at hS0e
  rw [← hωdef] at hK0e
  obtain ⟨hS0A, hS0i⟩ := Finset.mem_filter.mp hS0
  obtain ⟨hK0A, hK0c⟩ := Finset.mem_filter.mp hK0
  rw [Finset.mem_powerset] at hS0A hK0A
  have hAne : A.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    subst h
    exact hAbad ⟨∅, Finset.empty_subset _, by simp, ∅, by simp, by simp, le_refl _⟩
  obtain ⟨a, ha⟩ := hAne
  have hα1 : 1 ≤ α := by
    have := hαle {a} (by simpa using ha) (by simp)
    simpa using this
  have hω1 : 1 ≤ ω := by
    have := hωle {a} (by simpa using ha) (by simp)
    simpa using this
  -- key lemma 1
  have hK1 : ∀ K ⊆ A, G.IsClique (K : Set V) →
      ∃ S ⊆ A \ K, G.IsIndepSet (S : Set V) ∧ S.card = α := by
    intro K hKA hKc
    by_cases hKe : K = ∅
    · subst hKe
      exact ⟨S0, by simpa using hS0A, hS0i, hS0e.symm⟩
    have hss : A \ K ⊂ A := Finset.sdiff_ssubset hKA (Finset.nonempty_iff_ne_empty.mpr hKe)
    obtain ⟨S, hSs, hSi, F, hFc, hFcov, hFS⟩ := hAmin _ hss
    refine ⟨S, hSs, hSi, ?_⟩
    have hSle : S.card ≤ α := hαle S (hSs.trans Finset.sdiff_subset) hSi
    by_contra hne
    apply hAbad
    refine ⟨S0, hS0A, hS0i, insert K F, ?_, ?_, ?_⟩
    · intro W hW
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact hKc
      · exact hFc W hW
    · intro x hx
      by_cases hxK : x ∈ K
      · exact ⟨K, Finset.mem_insert_self _ _, hxK⟩
      · obtain ⟨W, hW, hxW⟩ := hFcov x (Finset.mem_sdiff.mpr ⟨hx, hxK⟩)
        exact ⟨W, Finset.mem_insert_of_mem hW, hxW⟩
    · have := Finset.card_insert_le K F
      omega
  -- colourings of A - v
  have hcol : ∀ v ∈ A, ∃ c : V → Fin α,
      ∀ x ∈ A.erase v, ∀ y ∈ A.erase v, x ≠ y → c x = c y → G.Adj x y := by
    intro v hv
    obtain ⟨S, hSs, hSi, F, hFc, hFcov, hFS⟩ := hAmin _ (Finset.erase_ssubset hv)
    have hSle : S.card ≤ α := hαle S (hSs.trans (Finset.erase_subset _ _)) hSi
    exact color_of_cover_P G _ F hFc hFcov α (by omega) (hFS.trans hSle)
  have : Nonempty (Fin α) := ⟨⟨0, by omega⟩⟩
  choose! c hc using hcol
  -- the family of cliques
  let I := Option (K0 × Fin α)
  let Kc : I → Finset V := fun i => Option.elim i K0
    (fun p => (A.erase (p.1 : V)).filter (fun x => c (p.1 : V) x = p.2))
  have hKcA : ∀ i, Kc i ⊆ A := by
    intro i
    rcases i with _ | ⟨v, k⟩
    · exact hK0A
    · exact (Finset.filter_subset _ _).trans (Finset.erase_subset _ _)
  have hKcc : ∀ i, G.IsClique (Kc i : Set V) := by
    intro i
    rcases i with _ | ⟨v, k⟩
    · exact hK0c
    · intro x hx y hy hxy
      simp only [Kc, Option.elim, Finset.coe_filter, Set.mem_setOf_eq] at hx hy
      exact hc v (hK0A v.2) x hx.1 y hy.1 hxy (hx.2.trans hy.2.symm)
  have hcardI : Fintype.card I = ω * α + 1 := by
    simp [I, Fintype.card_option, Fintype.card_prod, hK0e]
  -- counting
  have hsum : ∀ S ⊆ A, S.card = α → ∑ i : I, (S ∩ Kc i).card = ω * α := by
    intro S hSA hSc
    rw [Fintype.sum_option, Fintype.sum_prod_type]
    have hin : ∀ v : K0, ∑ k : Fin α, (S ∩ Kc (some (v, k))).card = (S.erase v).card := by
      intro v
      have : S.erase v = S ∩ A.erase v := by
        ext x
        simp only [Finset.mem_erase, Finset.mem_inter]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1, hSA h2⟩
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      rw [this, Finset.card_eq_sum_card_fiberwise (f := c v) (t := Finset.univ)
        (fun _ _ => Finset.mem_univ _)]
      apply Finset.sum_congr rfl
      intro k _
      congr 1
      ext x
      simp [Kc, Finset.mem_inter, Finset.mem_filter, and_assoc]
    simp only [hin]
    have h2 : ∀ v : K0, (S.erase v).card + (if (v : V) ∈ S then 1 else 0) = α := by
      intro v
      by_cases hv : (v : V) ∈ S
      · rw [Finset.card_erase_of_mem hv, if_pos hv]; omega
      · rw [Finset.erase_eq_of_notMem hv, if_neg hv]; omega
    have h3 : ∑ v : K0, (if (v : V) ∈ S then 1 else 0) = (S ∩ Kc none).card := by
      rw [Finset.sum_coe_sort K0 (fun v => if v ∈ S then 1 else 0), ← Finset.card_filter]
      congr 1
      ext x
      simp [Kc, and_comm]
    have h4 : ∑ v : K0, ((S.erase v).card + (if (v : V) ∈ S then 1 else 0)) = ω * α := by
      simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul, hK0e]
    rw [Finset.sum_add_distrib, h3] at h4
    omega
  choose! Ssel hSsel hSseli hSselc using fun i => hK1 (Kc i) (hKcA i) (hKcc i)
  have hSselA : ∀ i, Ssel i ⊆ A := fun i => (hSsel i).trans Finset.sdiff_subset
  have hcross : ∀ i j, (Ssel i ∩ Kc j).card = if i = j then 0 else 1 := by
    intro i j
    have hii : (Ssel i ∩ Kc i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      rw [Finset.mem_inter] at hx
      exact (Finset.mem_sdiff.mp (hSsel i hx.1)).2 hx.2
    have hle : ∀ j, (Ssel i ∩ Kc j).card ≤ 1 := fun j =>
      card_inter_le_one_P G _ _ (hSseli i) (hKcc j)
    have hs := hsum (Ssel i) (hSselA i) (hSselc i)
    have htot : ∑ j : I, (1 - (Ssel i ∩ Kc j).card) = 1 := by
      have e1 : ∑ j : I, (1 - (Ssel i ∩ Kc j).card) + ∑ j : I, (Ssel i ∩ Kc j).card =
          ∑ j : I, 1 := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have := hle j
        omega
      simp only [Finset.sum_const, Finset.card_univ, hcardI, smul_eq_mul, mul_one] at e1
      omega
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hii] at htot
    have hz : ∑ j ∈ Finset.univ.erase i, (1 - (Ssel i ∩ Kc j).card) = 0 := by omega
    rw [Finset.sum_eq_zero_iff] at hz
    by_cases hij : i = j
    · subst hij; simp [hii]
    · rw [if_neg hij]
      have := hz j (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ _⟩)
      have := hle j
      have : (Ssel i ∩ Kc j).card ≠ 0 := by omega
      omega
  -- linear algebra
  let M : Matrix I A ℝ := fun i x => if (x : V) ∈ Kc i then 1 else 0
  let N : Matrix A I ℝ := fun x j => if (x : V) ∈ Ssel j then 1 else 0
  have hMN : M * N = fun i j => if i = j then 0 else 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have : ∑ x : A, M i x * N x j = ∑ x ∈ A, (if x ∈ Ssel j ∩ Kc i then (1:ℝ) else 0) := by
      rw [← Finset.sum_coe_sort A]
      apply Finset.sum_congr rfl
      intro x _
      simp only [M, N, Finset.mem_inter]
      by_cases h1 : (x : V) ∈ Kc i <;> by_cases h2 : (x : V) ∈ Ssel j <;> simp [h1, h2]
    rw [this, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr (Finset.inter_subset_left.trans (hSselA j)), hcross j i]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij]; simp
  have hinj : Function.Injective (Matrix.mulVecLin N) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : N.mulVec v = 0 := hv
    have h0 : (M * N).mulVec v = 0 := by
      rw [← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero]
    rw [hMN] at h0
    have hvi : ∀ i, v i = ∑ j, v j := by
      intro i
      have := congrFun h0 i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      have e : ∑ j, (if i = j then (0:ℝ) else 1) * v j = ∑ j ∈ Finset.univ.erase i, v j := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        rw [if_pos rfl, zero_mul, zero_add]
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_neg (Ne.symm (Finset.ne_of_mem_erase hj)), one_mul]
      have e2 : ∑ j, v j = v i + ∑ j ∈ Finset.univ.erase i, v j :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
      linarith
    have hs : ∑ j, v j = (Fintype.card I : ℝ) * ∑ j, v j := by
      conv_lhs => rw [Finset.sum_congr rfl (fun j _ => hvi j)]
      simp
    rw [hcardI] at hs
    have hωα : (1:ℝ) ≤ (ω : ℝ) * α := by
      have : 1 ≤ ω * α := Nat.one_le_iff_ne_zero.mpr (by positivity)
      exact_mod_cast this
    push_cast at hs
    have hz : ∑ j, v j = 0 := by nlinarith
    funext i
    rw [hvi i, hz]
    rfl
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, hcardI,
    Fintype.card_coe] at hdim
  refine ⟨A, ?_⟩
  calc (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum ≤ α * ω :=
        Nat.mul_le_mul (indepNum_induce_le_P G A α hαle) (cliqueNum_induce_le_P G A ω hωle)
    _ < A.card := by rw [mul_comm]; omega

end ChvatalPolytopes.Perfect

open ChvatalPolytopes.Perfect


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ IsPerfect G) :
    ∃ A : Finset V,
      (G.induce (A : Set V)).indepNum * (G.induce (A : Set V)).cliqueNum < A.card := by
  exact lovasz_core G hG
