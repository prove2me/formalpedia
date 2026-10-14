-- Prove2me | solution 1 for EHRR10.Larman.diameter_le_larman
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-13T06:22:44.847213+00:00
-- url     : https://prove2.me/submissions/938feacd-1af8-48fd-8e97-4f60ec033d5f

import Mathlib
import Definitions.Def_EHRR10_LowerBound_BaseAbstraction



namespace EHRR10.Larman

open Finset

section Layers
variable {α : Type*} [DecidableEq α]

/-- A finite layer family with `N` layers of `d`-sets satisfying the interval condition. -/
structure LarLF (d : ℕ) (L : ℕ → Finset (Finset α)) (N : ℕ) : Prop where
  ne : ∀ i < N, (L i).Nonempty
  card : ∀ i < N, ∀ v ∈ L i, v.card = d
  disj : ∀ i < N, ∀ j < N, ∀ v ∈ L i, v ∈ L j → i = j
  P : ∀ i j k, i < j → j < k → k < N → ∀ u ∈ L i, ∀ w ∈ L k, ∃ v ∈ L j, u ∩ w ⊆ v

def larLab (L : ℕ → Finset (Finset α)) (i : ℕ) : Finset α := (L i).biUnion id

def larT (L : ℕ → Finset (Finset α)) (N a : ℕ) : Finset α := (Ico a N).biUnion (larLab L)

lemma mem_larLab {L : ℕ → Finset (Finset α)} {i : ℕ} {s : α} :
    s ∈ larLab L i ↔ ∃ v ∈ L i, s ∈ v := by
  simp [larLab]

lemma larLF_interval {d N : ℕ} {L : ℕ → Finset (Finset α)} (hF : LarLF d L N)
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hk : k < N) {s : α}
    (hi : s ∈ larLab L i) (hkk : s ∈ larLab L k) : s ∈ larLab L j := by
  rcases eq_or_lt_of_le hij with rfl | hij'
  · exact hi
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · exact hkk
  obtain ⟨u, hu, hsu⟩ := mem_larLab.1 hi
  obtain ⟨w, hw, hsw⟩ := mem_larLab.1 hkk
  obtain ⟨v, hv, huv⟩ := hF.P i j k hij' hjk' hk u hu w hw
  exact mem_larLab.2 ⟨v, hv, huv (mem_inter.2 ⟨hsu, hsw⟩)⟩

lemma larLab_subset {L : ℕ → Finset (Finset α)} {N : ℕ} {S : Finset α}
    (hS : ∀ i < N, ∀ v ∈ L i, v ⊆ S) {i : ℕ} (hi : i < N) : larLab L i ⊆ S := by
  intro s hs
  obtain ⟨v, hv, hsv⟩ := mem_larLab.1 hs
  exact hS i hi v hv hsv

lemma larman_base {L : ℕ → Finset (Finset α)} {N : ℕ} (hF : LarLF 1 L N) (S : Finset α)
    (hS : ∀ i < N, ∀ v ∈ L i, v ⊆ S) : N ≤ S.card := by
  have hsub : (range N).biUnion L ⊆ S.powersetCard 1 := by
    intro v hv
    simp only [mem_biUnion, mem_range] at hv
    obtain ⟨i, hi, hv⟩ := hv
    exact mem_powersetCard.2 ⟨hS i hi v hv, hF.card i hi v hv⟩
  have hcard : ((range N).biUnion L).card = ∑ i ∈ range N, (L i).card := by
    apply card_biUnion
    intro i hi j hj hij
    show Disjoint (L i) (L j)
    rw [Finset.disjoint_left]
    intro v hvi hvj
    exact hij (hF.disj i (mem_range.1 hi) j (mem_range.1 hj) v hvi hvj)
  have h1 : N ≤ ∑ i ∈ range N, (L i).card := by
    calc N = ∑ i ∈ range N, 1 := by simp
      _ ≤ ∑ i ∈ range N, (L i).card := by
        apply sum_le_sum
        intro i hi
        exact card_pos.2 (hF.ne i (mem_range.1 hi))
  have h2 := card_le_card hsub
  rw [card_powersetCard, Nat.choose_one_right] at h2
  omega

lemma larman_block {d : ℕ} {L : ℕ → Finset (Finset α)} {N : ℕ} (hF : LarLF (d+1) L N)
    {a e : ℕ} (hae : a ≤ e) (he : e < N) {s : α} (hsa : s ∈ larLab L a)
    (hse : s ∈ larLab L e) :
    LarLF d (fun i => ((L (a+i)).filter (fun v => s ∈ v)).image (fun v => v.erase s)) (e - a + 1)
    ∧ ∀ i < e - a + 1, ∀ v ∈ ((L (a+i)).filter (fun v => s ∈ v)).image (fun v => v.erase s),
       v ⊆ (Ico a (e+1)).biUnion (larLab L) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro i hi
    have hs : s ∈ larLab L (a+i) := larLF_interval hF (by omega) (by omega) he hsa hse
    obtain ⟨v, hv, hsv⟩ := mem_larLab.1 hs
    exact ⟨v.erase s, mem_image.2 ⟨v, mem_filter.2 ⟨hv, hsv⟩, rfl⟩⟩
  · intro i hi v hv
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
    rw [mem_filter] at hw
    rw [card_erase_of_mem hw.2, hF.card (a+i) (by omega) w hw.1]
    simp
  · intro i hi j hj v hvi hvj
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hvi
    obtain ⟨w', hw', hww⟩ := mem_image.1 hvj
    rw [mem_filter] at hw hw'
    have : w' = w := by
      rw [← insert_erase hw.2, ← insert_erase hw'.2, hww]
    subst this
    have := hF.disj (a+i) (by omega) (a+j) (by omega) w' hw.1 hw'.1
    omega
  · intro i j k hij hjk hk u hu w hw
    obtain ⟨u0, hu0, rfl⟩ := mem_image.1 hu
    obtain ⟨w0, hw0, rfl⟩ := mem_image.1 hw
    rw [mem_filter] at hu0 hw0
    obtain ⟨v, hv, huv⟩ :=
      hF.P (a+i) (a+j) (a+k) (by omega) (by omega) (by omega) u0 hu0.1 w0 hw0.1
    have hsv : s ∈ v := huv (mem_inter.2 ⟨hu0.2, hw0.2⟩)
    refine ⟨v.erase s, mem_image.2 ⟨v, mem_filter.2 ⟨hv, hsv⟩, rfl⟩, ?_⟩
    intro x hx
    rw [mem_inter, mem_erase, mem_erase] at hx
    exact mem_erase.2 ⟨hx.1.1, huv (mem_inter.2 ⟨hx.1.2, hx.2.2⟩)⟩
  · intro i hi v hv x hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hv
    rw [mem_filter] at hw
    rw [mem_biUnion]
    exact ⟨a+i, mem_Ico.2 ⟨by omega, by omega⟩, mem_larLab.2 ⟨w, hw.1, mem_of_mem_erase hx⟩⟩

lemma larman_inner {d : ℕ} (c : ℕ)
    (IH : ∀ (L : ℕ → Finset (Finset α)) (N : ℕ) (S : Finset α), LarLF d L N →
      (∀ i < N, ∀ v ∈ L i, v ⊆ S) → N ≤ c * S.card)
    {L : ℕ → Finset (Finset α)} {N : ℕ} (hF : LarLF (d+1) L N) :
    ∀ m a, N - a = m →
      N - a ≤ c * ((larT L N a).card + (larT L N a \ larLab L a).card) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro a ham
  by_cases haN : N ≤ a
  · have : N - a = 0 := by omega
    rw [this]; exact Nat.zero_le _
  replace haN : a < N := by omega
  have hlabne : (larLab L a).Nonempty := by
    obtain ⟨v, hv⟩ := hF.ne a haN
    have hc := hF.card a haN v hv
    obtain ⟨x, hx⟩ := card_pos.1 (by omega : 0 < v.card)
    exact ⟨x, mem_larLab.2 ⟨v, hv, hx⟩⟩
  let E := (Ico a N).filter (fun i => ¬ Disjoint (larLab L a) (larLab L i))
  have hEne : E.Nonempty := ⟨a, mem_filter.2 ⟨mem_Ico.2 ⟨le_rfl, haN⟩, by
      rw [disjoint_self_iff_empty]; exact hlabne.ne_empty⟩⟩
  obtain ⟨e, he_def⟩ : ∃ e, e = E.max' hEne := ⟨_, rfl⟩
  have heE : e ∈ E := he_def ▸ max'_mem E hEne
  have heE' := heE
  simp only [E, mem_filter, mem_Ico] at heE'
  obtain ⟨⟨hae, heN⟩, hdis⟩ := heE'
  have hmax : ∀ i, e < i → i < N → Disjoint (larLab L a) (larLab L i) := by
    intro i hei hiN
    by_contra hcon
    have hiE : i ∈ E := mem_filter.2 ⟨mem_Ico.2 ⟨by omega, hiN⟩, hcon⟩
    have := le_max' E i hiE
    omega
  obtain ⟨s, hs1, hs2⟩ := not_disjoint_iff.1 hdis
  obtain ⟨hres, hlabs⟩ := larman_block hF hae heN hs1 hs2
  have h1 : e - a + 1 ≤ c * ((Ico a (e+1)).biUnion (larLab L)).card := IH _ _ _ hres hlabs
  have h2 := ihm (N - (e+1)) (by omega) (e+1) rfl
  obtain ⟨U, hU⟩ : ∃ U, U = (Ico a (e+1)).biUnion (larLab L) := ⟨_, rfl⟩
  rw [← hU] at h1
  have hTa : larT L N a = U ∪ larT L N (e+1) := by
    rw [larT, larT, hU, ← Ico_union_Ico_eq_Ico (show a ≤ e + 1 by omega) (show e + 1 ≤ N by omega),
      union_biUnion]
  have hint : U ∩ larT L N (e+1) ⊆ larLab L (e+1) := by
    intro x hx
    rw [mem_inter, hU, mem_biUnion, larT, mem_biUnion] at hx
    obtain ⟨⟨i, hi, hxi⟩, ⟨k, hk, hxk⟩⟩ := hx
    rw [mem_Ico] at hi hk
    exact larLF_interval hF (by omega) hk.1 hk.2 hxi hxk
  have hdisj2 : Disjoint (U ∩ larT L N (e+1)) (larT L N (e+1) \ larLab L (e+1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    exact (mem_sdiff.1 hx').2 (hint hx)
  have hsub : (U ∩ larT L N (e+1)) ∪ (larT L N (e+1) \ larLab L (e+1)) ⊆
      larT L N a \ larLab L a := by
    intro x hx
    have hxT : x ∈ larT L N (e+1) := by
      rcases mem_union.1 hx with h | h
      · exact (mem_inter.1 h).2
      · exact (mem_sdiff.1 h).1
    rw [mem_sdiff]
    refine ⟨by rw [hTa]; exact mem_union_right _ hxT, ?_⟩
    intro hxa
    rw [larT, mem_biUnion] at hxT
    obtain ⟨k, hk, hxk⟩ := hxT
    rw [mem_Ico] at hk
    exact Finset.disjoint_left.1 (hmax k (by omega) hk.2) hxa hxk
  have hc1 := card_union_add_card_inter U (larT L N (e+1))
  have hc2 := card_le_card hsub
  rw [card_union_of_disjoint hdisj2] at hc2
  rw [← hTa] at hc1
  have key : U.card + (larT L N (e+1)).card + (larT L N (e+1) \ larLab L (e+1)).card ≤
      (larT L N a).card + (larT L N a \ larLab L a).card := by omega
  calc N - a = (e - a + 1) + (N - (e+1)) := by omega
    _ ≤ c * U.card + c * ((larT L N (e+1)).card + (larT L N (e+1) \ larLab L (e+1)).card) :=
        add_le_add h1 h2
    _ = c * (U.card + (larT L N (e+1)).card + (larT L N (e+1) \ larLab L (e+1)).card) := by
        ring
    _ ≤ c * ((larT L N a).card + (larT L N a \ larLab L a).card) := Nat.mul_le_mul_left c key

theorem larman_layers (d : ℕ) (hd : 1 ≤ d) : ∀ (L : ℕ → Finset (Finset α)) (N : ℕ)
    (S : Finset α), LarLF d L N → (∀ i < N, ∀ v ∈ L i, v ⊆ S) → N ≤ 2 ^ (d - 1) * S.card := by
  induction d, hd using Nat.le_induction with
  | base => intro L N S hF hS; simpa using larman_base hF S hS
  | succ d hd ih =>
    intro L N S hF hS
    have h := larman_inner (2 ^ (d-1)) ih hF (N - 0) 0 rfl
    have hT : larT L N 0 ⊆ S := by
      intro x hx
      rw [larT, mem_biUnion] at hx
      obtain ⟨i, hi, hxi⟩ := hx
      exact larLab_subset hS (mem_Ico.1 hi).2 hxi
    have h3 := card_le_card hT
    have h4 := card_le_card (sdiff_subset : larT L N 0 \ larLab L 0 ⊆ larT L N 0)
    have hpow : 2 ^ (d + 1 - 1) = 2 * 2 ^ (d-1) := by
      rw [show d + 1 - 1 = (d - 1) + 1 by omega, pow_succ]; ring
    rw [hpow]
    calc N = N - 0 := by simp
      _ ≤ 2 ^ (d-1) * ((larT L N 0).card + (larT L N 0 \ larLab L 0).card) := h
      _ ≤ 2 ^ (d-1) * (S.card + S.card) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * 2 ^ (d-1) * S.card := by ring

end Layers

lemma larman_walk_ivt {W : Type*} {G : SimpleGraph W} (f : W → ℕ)
    (hf : ∀ a b, G.Adj a b → f b ≤ f a + 1) {x y : W} (q : G.Walk x y) (j : ℕ) :
    f x ≤ j → j ≤ f y → ∃ z ∈ q.support, f z = j := by
  induction q with
  | nil => intro hx hy; exact ⟨_, SimpleGraph.Walk.start_mem_support _, by omega⟩
  | @cons a b c h q ih =>
    intro hx hy
    by_cases hj : f a = j
    · exact ⟨a, by simp, hj⟩
    · have := hf _ _ h
      obtain ⟨z, hz, hfz⟩ := ih (by omega) hy
      exact ⟨z, by simp [hz], hfz⟩

theorem larman_core (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V) (hG : EHRR10.LowerBound.InB d n V G)
    (u v : V) : ∃ p : G.Walk u v, p.length ≤ 2 ^ (d - 1) * n := by
  classical
  obtain ⟨_, hcard, hI⟩ := hG
  have hf : ∀ a b : V, G.Adj a b → G.dist u b ≤ G.dist u a + 1 := by
    intro a b h
    rcases h.diff_dist_adj (u := u) with h1 | h1 | h1 <;> omega
  obtain ⟨p0, -⟩ := hI u v
  obtain ⟨p, hp⟩ := p0.reachable.exists_walk_length_eq_dist
  refine ⟨p, ?_⟩
  let L : ℕ → Finset (Finset (Fin n)) := fun i =>
    (Finset.univ.filter (fun w : V => G.dist u w = i)).image Subtype.val
  have hmemL : ∀ i x, x ∈ L i ↔ ∃ w : V, G.dist u w = i ∧ (w : Finset (Fin n)) = x := by
    intro i x; simp [L]
  have hF : LarLF d L (G.dist u v + 1) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨z, -, hz⟩ := larman_walk_ivt (G := G) (fun w => G.dist u w) hf p i
        (by simp) (show i ≤ G.dist u v by omega)
      exact ⟨z.1, (hmemL i _).2 ⟨z, hz, rfl⟩⟩
    · intro i hi x hx
      obtain ⟨w, -, rfl⟩ := (hmemL i x).1 hx
      exact hcard w.1 w.2
    · intro i hi j hj x hxi hxj
      obtain ⟨w, hw, rfl⟩ := (hmemL i _).1 hxi
      obtain ⟨w', hw', hww⟩ := (hmemL j _).1 hxj
      have : w' = w := Subtype.ext hww
      subst this; omega
    · intro i j k' hij hjk hk x hx y hy
      obtain ⟨w1, hw1, rfl⟩ := (hmemL i _).1 hx
      obtain ⟨w2, hw2, rfl⟩ := (hmemL k' _).1 hy
      obtain ⟨q, hq⟩ := hI w1 w2
      obtain ⟨z, hz, hfz⟩ := larman_walk_ivt (G := G) (fun w => G.dist u w) hf q j
        (show G.dist u w1 ≤ j by omega) (show j ≤ G.dist u w2 by omega)
      exact ⟨z.1, (hmemL j _).2 ⟨z, hfz, rfl⟩, hq z hz⟩
  have := larman_layers d hd L (G.dist u v + 1) Finset.univ hF
    (fun _ _ _ _ => Finset.subset_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at this
  rw [hp]
  have h2 : 1 ≤ 2 ^ (d - 1) * n + 0 := by omega
  omega

end EHRR10.Larman

open EHRR10.Larman


theorem solution (d n : ℕ) (hd : 1 ≤ d)
    (V : Finset (Finset (Fin n))) (G : SimpleGraph V) (hG : EHRR10.LowerBound.InB d n V G)
    (u v : V) :
    ∃ p : G.Walk u v, p.length ≤ 2 ^ (d - 1) * n := by
  exact larman_core d n hd V G hG u v
