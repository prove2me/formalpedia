-- Prove2me | solution 1 for CClosedGraphs.LowerBound.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T18:07:12.614728+00:00
-- url     : https://prove2.me/submissions/14e79780-8cf2-45c4-9b53-93d7d141346e

import Mathlib
import Definitions.Def_CClosedGraphs_LowerBound_Setting

set_option autoImplicit false

namespace CCLB3ac

open Finset CClosedGraphs.Peeling CClosedGraphs.LowerBound

/-- witness form of a maximal clique -/
def IsMaxW {V : Type*} (G : SimpleGraph V) (K : Finset V) : Prop :=
  G.IsClique (↑K : Set V) ∧ ∀ v, v ∉ K → ∃ u ∈ K, u ≠ v ∧ ¬ G.Adj u v

theorem mem_maxCliques_of_isMaxW {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : Finset V) (hK : IsMaxW G K) :
    K ∈ maxCliquesIn G Set.univ := by
  classical
  unfold maxCliquesIn
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨⟨Set.subset_univ _, hK.1⟩, ?_⟩⟩
  intro T hT hKT t ht
  by_contra htK
  obtain ⟨u, hu, hut, hnadj⟩ := hK.2 t htK
  exact hnadj (hT.2 (hKT hu) ht hut)

theorem isMaxW_map {V W : Type*} (G : SimpleGraph V) (e : V ↪ W) (K : Finset V)
    (hK : IsMaxW G K) (hne : K.Nonempty) : IsMaxW (G.map e) (K.map e) := by
  refine ⟨?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    rw [SimpleGraph.map_adj_apply]
    exact hK.1 ha hb (fun h => hab (by rw [h]))
  · intro v hv
    by_cases hr : ∃ w, e w = v
    · obtain ⟨w, rfl⟩ := hr
      have hw : w ∉ K := fun h => hv (Finset.mem_map_of_mem e h)
      obtain ⟨u, hu, huw, hn⟩ := hK.2 w hw
      refine ⟨e u, Finset.mem_map_of_mem e hu, fun h => huw (e.injective h), ?_⟩
      rw [SimpleGraph.map_adj_apply]; exact hn
    · obtain ⟨u, hu⟩ := hne
      refine ⟨e u, Finset.mem_map_of_mem e hu, fun h => hr ⟨u, h⟩, ?_⟩
      rw [SimpleGraph.map_adj]
      rintro ⟨a, b, _, _, hb⟩
      exact hr ⟨b, hb⟩

theorem isCClosed_map {V W : Type*} [Finite V] (G : SimpleGraph V) (e : V ↪ W) (c : ℕ) (hc : 1 ≤ c)
    (hG : IsCClosed c G) : IsCClosed c (G.map e) := by
  intro u v huv hcn
  by_cases hu : ∃ a, e a = u
  · by_cases hv : ∃ b, e b = v
    · obtain ⟨a, rfl⟩ := hu
      obtain ⟨b, rfl⟩ := hv
      rw [SimpleGraph.map_adj_apply]
      refine hG a b (fun h => huv (by rw [h])) ?_
      refine le_trans hcn ?_
      have hsub : (G.map e).commonNeighbors (e a) (e b) ⊆ e '' G.commonNeighbors a b := by
        intro w hw
        rw [SimpleGraph.mem_commonNeighbors] at hw
        obtain ⟨h1, h2⟩ := hw
        rw [SimpleGraph.map_adj] at h1 h2
        obtain ⟨a1, w1, hA1, ha1, rfl⟩ := h1
        obtain ⟨b1, w2, hB1, hb1, hw2⟩ := h2
        have := e.injective ha1; subst this
        have := e.injective hb1; subst this
        have := e.injective hw2; subst this
        exact ⟨w2, (G.mem_commonNeighbors).2 ⟨hA1, hB1⟩, rfl⟩
      calc ((G.map e).commonNeighbors (e a) (e b)).ncard ≤ (e '' G.commonNeighbors a b).ncard :=
            Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ (G.commonNeighbors a b).ncard := Set.ncard_image_le (Set.toFinite _)
    · exfalso
      have : (G.map e).commonNeighbors u v = ∅ := by
        ext w
        simp only [SimpleGraph.mem_commonNeighbors, Set.mem_empty_iff_false, iff_false, not_and]
        intro _ h2
        rw [SimpleGraph.map_adj] at h2
        obtain ⟨b, _, _, hb, _⟩ := h2
        exact hv ⟨b, hb⟩
      rw [this, Set.ncard_empty] at hcn
      omega
  · exfalso
    have : (G.map e).commonNeighbors u v = ∅ := by
      ext w
      simp only [SimpleGraph.mem_commonNeighbors, Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 _
      rw [SimpleGraph.map_adj] at h1
      obtain ⟨a, _, _, ha, _⟩ := h1
      exact hu ⟨a, ha⟩
    rw [this, Set.ncard_empty] at hcn
    omega

/-- triangle-free -/
def TriFree {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ x y z, H.Adj x y → H.Adj y z → H.Adj x z → False

/-- two distinct vertices have at most one common neighbour -/
def QuadFree {W : Type*} (H : SimpleGraph W) : Prop :=
  ∀ x y z w, x ≠ y → H.Adj x z → H.Adj y z → H.Adj x w → H.Adj y w → z = w

theorem card_closedCommon_le {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hT : TriFree H) (hQ : QuadFree H) (x y : W) (hxy : x ≠ y) :
    (univ.filter (fun z => (x = z ∨ H.Adj x z) ∧ (y = z ∨ H.Adj y z))).card ≤ 2 := by
  by_cases hadj : H.Adj x y
  · calc _ ≤ ({x, y} : Finset W).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
          simp only [Finset.mem_insert, Finset.mem_singleton]
          by_contra hne
          push Not at hne
          obtain ⟨h1 | h1, h2 | h2⟩ := hz
          · exact hne.1 h1.symm
          · exact hne.1 h1.symm
          · exact hne.2 h2.symm
          · exact hT x y z hadj h2 h1
      _ ≤ 2 := Finset.card_le_two
  · calc _ ≤ 1 := by
          rw [Finset.card_le_one]
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
          have ha' : H.Adj x a ∧ H.Adj y a := by
            rcases ha with ⟨h1 | h1, h2 | h2⟩
            · exact absurd (h1.trans h2.symm) hxy
            · subst h1; exact absurd h2.symm hadj
            · subst h2; exact absurd h1 hadj
            · exact ⟨h1, h2⟩
          have hb' : H.Adj x b ∧ H.Adj y b := by
            rcases hb with ⟨h1 | h1, h2 | h2⟩
            · exact absurd (h1.trans h2.symm) hxy
            · subst h1; exact absurd h2.symm hadj
            · subst h2; exact absurd h1 hadj
            · exact ⟨h1, h2⟩
          exact hQ x y a b hxy ha'.1 ha'.2 hb'.1 hb'.2
      _ ≤ 2 := by norm_num

theorem blowUp_closed {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hT : TriFree H) (hQ : QuadFree H) (h c : ℕ) (hch : 2 * h ≤ c + 1) :
    IsCClosed c (blowUp H h) := by
  intro p q hpq hcn
  by_contra hna
  obtain ⟨x, i⟩ := p
  obtain ⟨y, j⟩ := q
  have hxy : x ≠ y := by
    rintro rfl
    have hij : i ≠ j := fun h => hpq (by rw [h])
    exact hna ⟨hij, Or.inl rfl⟩
  set S := univ.filter (fun z => (x = z ∨ H.Adj x z) ∧ (y = z ∨ H.Adj y z))
  have hsub : (blowUp H h).commonNeighbors (x, i) (y, j) ⊆ ↑(S ×ˢ (univ.erase i)) := by
    intro w hw
    rw [SimpleGraph.mem_commonNeighbors] at hw
    obtain ⟨⟨h1, h2⟩, ⟨_, h4⟩⟩ := hw
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_erase,
      Finset.mem_univ, and_true, S, Finset.mem_filter, true_and]
    exact ⟨⟨h2, h4⟩, fun h => h1 h.symm⟩
  have hS := card_closedCommon_le H hT hQ x y hxy
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_product, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin] at h1
  have : S.card * (h - 1) ≤ 2 * (h - 1) := Nat.mul_le_mul_right _ hS
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0; exact i.elim0
    · exact h0
  have : 2 * (h - 1) < c := by omega
  omega

/-- the clique of the blow-up over an edge `xy` picking `x` on `S` and `y` off `S` -/
def Kc {W : Type*} [DecidableEq W] {h : ℕ} (x y : W) (S : Finset (Fin h)) : Finset (W × Fin h) :=
  S.image (fun i => (x, i)) ∪ Sᶜ.image (fun i => (y, i))

theorem mem_Kc {W : Type*} [DecidableEq W] {h : ℕ} (x y z : W) (S : Finset (Fin h)) (k : Fin h) :
    (z, k) ∈ Kc x y S ↔ (k ∈ S ∧ z = x) ∨ (k ∉ S ∧ z = y) := by
  unfold Kc
  simp only [Finset.mem_union, Finset.mem_image, Prod.mk.injEq, Finset.mem_compl]
  constructor
  · rintro (⟨i, hi, rfl, rfl⟩ | ⟨i, hi, rfl, rfl⟩)
    · exact Or.inl ⟨hi, rfl⟩
    · exact Or.inr ⟨hi, rfl⟩
  · rintro (⟨hk, rfl⟩ | ⟨hk, rfl⟩)
    · exact Or.inl ⟨k, hk, rfl, rfl⟩
    · exact Or.inr ⟨k, hk, rfl, rfl⟩

theorem Kc_isMaxW {W : Type*} [DecidableEq W] (H : SimpleGraph W) {h : ℕ} (x y : W)
    (hxy : H.Adj x y) (S : Finset (Fin h)) : IsMaxW (blowUp H h) (Kc x y S) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨a, i⟩ ha ⟨b, j⟩ hb hab
    rw [Finset.mem_coe, mem_Kc] at ha hb
    show i ≠ j ∧ (a = b ∨ H.Adj a b)
    rcases ha with ⟨hi, rfl⟩ | ⟨hi, rfl⟩ <;> rcases hb with ⟨hj, rfl⟩ | ⟨hj, rfl⟩
    · exact ⟨fun h => hab (by rw [h]), Or.inl rfl⟩
    · exact ⟨fun h => hj (h ▸ hi), Or.inr hxy⟩
    · exact ⟨fun h => hi (h ▸ hj), Or.inr hxy.symm⟩
    · exact ⟨fun h => hab (by rw [h]), Or.inl rfl⟩
  · rintro ⟨z, k⟩ hv
    by_cases hk : k ∈ S
    · refine ⟨(x, k), (mem_Kc x y x S k).2 (Or.inl ⟨hk, rfl⟩), fun h => hv (h ▸ (mem_Kc x y x S k).2 (Or.inl ⟨hk, rfl⟩)), ?_⟩
      exact fun h => h.1 rfl
    · refine ⟨(y, k), (mem_Kc x y y S k).2 (Or.inr ⟨hk, rfl⟩), fun h => hv (h ▸ (mem_Kc x y y S k).2 (Or.inr ⟨hk, rfl⟩)), ?_⟩
      exact fun h => h.1 rfl

theorem blow_main {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hT : TriFree H) (hQ : QuadFree H) (f : I → W × W)
    (hf : Function.Injective f) (hadj : ∀ i, H.Adj (f i).1 (f i).2) (h c n : ℕ) (h2 : 2 ≤ h)
    (hch : 2 * h ≤ c + 1) (hc : 1 ≤ c) (hn : Fintype.card W * h ≤ n) :
    ∃ G : SimpleGraph (Fin n), IsCClosed c G ∧ Fintype.card I * 2 ^ (h - 2) ≤ numMaxCliques G := by
  obtain ⟨e⟩ : Nonempty (W × Fin h ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Fintype.card_prod] using hn)
  refine ⟨(blowUp H h).map e, isCClosed_map _ e c hc (blowUp_closed H hT hQ h c hch), ?_⟩
  set a0 : Fin h := ⟨0, by omega⟩
  set b0 : Fin h := ⟨h - 1, by omega⟩
  have hab : b0 ≠ a0 := by
    intro hh; have := congrArg Fin.val hh; simp [a0, b0] at this; omega
  set M : Finset (Fin h) := (univ.erase a0).erase b0
  have hM : M.card = h - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hab, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  let F : I × Finset (Fin h) → Finset (Fin n) := fun p =>
    (Kc (f p.1).1 (f p.1).2 (insert a0 p.2)).map e
  have hcard : ((univ : Finset I) ×ˢ M.powerset).card = Fintype.card I * 2 ^ (h - 2) := by
    rw [Finset.card_product, Finset.card_powerset, hM, Finset.card_univ]
  rw [← hcard]
  unfold numMaxCliques numMaxCliquesIn
  apply Finset.card_le_card_of_injOn F
  · intro p _
    apply mem_maxCliques_of_isMaxW
    apply isMaxW_map
    · exact Kc_isMaxW H _ _ (hadj p.1) _
    · exact ⟨((f p.1).1, a0), (mem_Kc (f p.1).1 (f p.1).2 (f p.1).1 (insert a0 p.2) a0).2
        (Or.inl ⟨Finset.mem_insert_self _ _, rfl⟩)⟩
  · rintro ⟨i, S⟩ hS ⟨j, T⟩ hT' hEq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_powerset] at hS hT'
    have hK : Kc (f i).1 (f i).2 (insert a0 S) = Kc (f j).1 (f j).2 (insert a0 T) :=
      Finset.map_injective e hEq
    have hSa : a0 ∉ S := fun h => by have := hS.2 h; simp [M] at this
    have hSb : b0 ∉ S := fun h => by have := hS.2 h; simp [M] at this
    have hTa : a0 ∉ T := fun h => by have := hT'.2 h; simp [M] at this
    have hTb : b0 ∉ T := fun h => by have := hT'.2 h; simp [M] at this
    have hx : (f i).1 = (f j).1 := by
      have h1 := (mem_Kc (f i).1 (f i).2 (f i).1 (insert a0 S) a0).2
        (Or.inl ⟨Finset.mem_insert_self a0 S, rfl⟩)
      rw [hK, mem_Kc] at h1
      rcases h1 with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · exact absurd (Finset.mem_insert_self a0 T) h
    have hy : (f i).2 = (f j).2 := by
      have hb1 : b0 ∉ insert a0 S := by
        rw [Finset.mem_insert]; push Not; exact ⟨hab, hSb⟩
      have hb2 : b0 ∉ insert a0 T := by
        rw [Finset.mem_insert]; push Not; exact ⟨hab, hTb⟩
      have h1 := (mem_Kc (f i).1 (f i).2 (f i).2 _ b0).2 (Or.inr ⟨hb1, rfl⟩)
      rw [hK, mem_Kc] at h1
      rcases h1 with ⟨h, _⟩ | ⟨_, h⟩
      · exact absurd h hb2
      · exact h
    have hij : i = j := hf (Prod.ext hx hy)
    subst hij
    have hne : (f i).1 ≠ (f i).2 := (hadj i).ne
    have key : ∀ (U : Finset (Fin h)) (k : Fin h),
        ((f i).1, k) ∈ Kc (f i).1 (f i).2 U ↔ k ∈ U := by
      intro U k
      rw [mem_Kc]
      constructor
      · rintro (⟨hk, _⟩ | ⟨_, hk⟩)
        · exact hk
        · exact absurd hk hne
      · intro hk; exact Or.inl ⟨hk, rfl⟩
    have hST : insert a0 S = insert a0 T := by
      ext k
      rw [← key, hK, key]
    have hS' : S = T := by
      rw [← Finset.erase_insert hSa, hST, Finset.erase_insert hTa]
    rw [hS']

theorem base_main {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I] (H : SimpleGraph W)
    (hT : TriFree H) (hQ : QuadFree H) (f : I → W × W)
    (hf : Function.Injective f) (hadj : ∀ i, H.Adj (f i).1 (f i).2)
    (hsep : ∀ i j, (f i).1 ≠ (f j).2) (c n : ℕ) (hc : 2 ≤ c) (hn : Fintype.card W ≤ n) :
    ∃ G : SimpleGraph (Fin n), IsCClosed c G ∧ Fintype.card I ≤ numMaxCliques G := by
  obtain ⟨e⟩ : Nonempty (W ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hn)
  have hcl : IsCClosed c H := by
    intro u v huv hcn
    by_contra hna
    have : (H.commonNeighbors u v).ncard ≤ 1 := by
      rw [Set.ncard_le_one (Set.toFinite _)]
      intro a ha b hb
      rw [SimpleGraph.mem_commonNeighbors] at ha hb
      exact hQ u v a b huv ha.1 ha.2 hb.1 hb.2
    omega
  refine ⟨H.map e, isCClosed_map H e c (by omega) hcl, ?_⟩
  unfold numMaxCliques numMaxCliquesIn
  rw [← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (fun i => ({(f i).1, (f i).2} : Finset W).map e)
  · intro i _
    apply mem_maxCliques_of_isMaxW
    apply isMaxW_map
    · refine ⟨?_, ?_⟩
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        · exact absurd rfl hab
        · exact hadj i
        · exact (hadj i).symm
        · exact absurd rfl hab
      · intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hv
        by_cases hxv : H.Adj (f i).1 v
        · exact ⟨(f i).2, by simp, fun h => hv.2 h.symm, fun hyv => hT _ _ _ (hadj i) hyv hxv⟩
        · exact ⟨(f i).1, by simp, fun h => hv.1 h.symm, hxv⟩
    · exact ⟨(f i).1, by simp⟩
  · intro i _ j _ hEq
    have hK : ({(f i).1, (f i).2} : Finset W) = {(f j).1, (f j).2} := Finset.map_injective e hEq
    have h1 : (f i).1 ∈ ({(f j).1, (f j).2} : Finset W) := hK ▸ (by simp)
    have h2 : (f i).2 ∈ ({(f j).1, (f j).2} : Finset W) := hK ▸ (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    apply hf
    rcases h1 with h1 | h1
    · rcases h2 with h2 | h2
      · exact absurd h2.symm (hsep j i)
      · exact Prod.ext h1 h2
    · exact absurd h1 (hsep i j)

/-- point-line incidence graph of the affine plane over `F` (lines `y = m x + k`) -/
def inc (F : Type*) [Field F] : SimpleGraph ((F × F) ⊕ (F × F)) where
  Adj u v := match u, v with
    | Sum.inl P, Sum.inr l => P.2 = l.1 * P.1 + l.2
    | Sum.inr l, Sum.inl P => P.2 = l.1 * P.1 + l.2
    | _, _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

theorem inc_tri (F : Type*) [Field F] : TriFree (inc F) := by
  intro x y z h1 h2 h3
  cases x <;> cases y <;> cases z <;> first | exact h1 | exact h2 | exact h3

theorem inc_quad (F : Type*) [Field F] : QuadFree (inc F) := by
  intro x y z w hxy h1 h2 h3 h4
  rcases x with ⟨a, b⟩ | ⟨m, k⟩ <;> rcases y with ⟨a', b'⟩ | ⟨m', k'⟩ <;>
    rcases z with ⟨u, v⟩ | ⟨u, v⟩ <;> rcases w with ⟨s, t⟩ | ⟨s, t⟩ <;>
    first | exact h1.elim | exact h2.elim | exact h3.elim | exact h4.elim | skip
  · -- two points, two lines
    change b = u * a + v at h1
    change b' = u * a' + v at h2
    change b = s * a + t at h3
    change b' = s * a' + t at h4
    have ha : a ≠ a' := by
      intro haa; subst haa
      exact hxy (by rw [show b = b' by rw [h1, h2]])
    have hus : u = s := by
      have : (u - s) * (a - a') = 0 := by linear_combination -h1 + h2 + h3 - h4
      rcases mul_eq_zero.1 this with h | h
      · exact sub_eq_zero.1 h
      · exact absurd (sub_eq_zero.1 h) ha
    subst hus
    have : v = t := by linear_combination -h1 + h3
    rw [this]
  · -- two lines, two points
    change v = m * u + k at h1
    change v = m' * u + k' at h2
    change t = m * s + k at h3
    change t = m' * s + k' at h4
    have hm : m ≠ m' := by
      intro hmm; subst hmm
      exact hxy (by rw [show k = k' by linear_combination -h1 + h2])
    have hus : u = s := by
      have : (m - m') * (u - s) = 0 := by linear_combination -h1 + h2 + h3 - h4
      rcases mul_eq_zero.1 this with h | h
      · exact absurd (sub_eq_zero.1 h) hm
      · exact sub_eq_zero.1 h
    subst hus
    have : v = t := by linear_combination h1 - h3
    rw [this]

def incF (F : Type*) [Field F] (q : F × F × F) : ((F × F) ⊕ (F × F)) × ((F × F) ⊕ (F × F)) :=
  (Sum.inl (q.1, q.2.1 * q.1 + q.2.2), Sum.inr (q.2.1, q.2.2))

theorem incF_inj (F : Type*) [Field F] : Function.Injective (incF F) := by
  rintro ⟨a, m, k⟩ ⟨a', m', k'⟩ h
  simp only [incF, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
  obtain ⟨⟨rfl, _⟩, rfl, rfl⟩ := h
  rfl

theorem incF_adj (F : Type*) [Field F] (q : F × F × F) : (inc F).Adj (incF F q).1 (incF F q).2 := by
  show q.2.1 * q.1 + q.2.2 = q.2.1 * q.1 + q.2.2
  rfl

theorem incF_sep (F : Type*) [Field F] (q r : F × F × F) : (incF F q).1 ≠ (incF F r).2 := by
  simp [incF]

theorem k2_tri : TriFree (⊤ : SimpleGraph Bool) := by
  intro x y z h1 h2 h3
  simp only [SimpleGraph.top_adj] at h1 h2 h3
  cases x <;> cases y <;> cases z <;> simp_all

theorem k2_quad : QuadFree (⊤ : SimpleGraph Bool) := by
  intro x y z w hxy h1 h2 h3 h4
  simp only [SimpleGraph.top_adj] at h1 h2 h3 h4
  cases x <;> cases y <;> cases z <;>
    first | exact absurd rfl hxy | exact absurd rfl h1 | exact absurd rfl h2

theorem prime_choice (n D : ℕ) (hD : 0 < D) (hn : D ≤ n) :
    ∃ p, p.Prime ∧ D * p ^ 2 ≤ 4 * n ∧ n < D * p ^ 2 := by
  set m := Nat.sqrt (n / D) with hmdef
  have hm : 1 ≤ m := Nat.le_sqrt.2 (by rw [Nat.le_div_iff_mul_le hD]; omega)
  obtain ⟨p, hp, hmp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  refine ⟨p, hp, ?_, ?_⟩
  · have h1 : m * m ≤ n / D := Nat.sqrt_le _
    have h2 : D * (n / D) ≤ n := Nat.mul_div_le n D
    calc D * p ^ 2 ≤ D * (2 * m) ^ 2 := by gcongr
      _ = 4 * (D * (m * m)) := by ring
      _ ≤ 4 * (D * (n / D)) := by gcongr
      _ ≤ 4 * n := by omega
  · have h1 : n / D < (m + 1) * (m + 1) := Nat.lt_succ_sqrt _
    have h2 : n < D * (n / D + 1) := by
      have := Nat.div_add_mod n D
      have := Nat.mod_lt n hD
      nlinarith
    have h3 : (m + 1) * (m + 1) ≤ p ^ 2 := by nlinarith
    calc n < D * (n / D + 1) := h2
      _ ≤ D * ((m + 1) * (m + 1)) := by gcongr; omega
      _ ≤ D * p ^ 2 := by gcongr

theorem finA (c n L : ℕ) (hc : 2 ≤ c) (hc3 : c ≤ 3) (hn : n ≤ 8 * L ^ 2) :
    2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * (L ^ 3) ^ 2 := by
  have h2c : 2 ^ c ≤ c ^ 3 := by interval_cases c <;> norm_num
  have hn3 : n ^ 3 ≤ 512 * L ^ 6 := by
    calc n ^ 3 ≤ (8 * L ^ 2) ^ 3 := Nat.pow_le_pow_left hn 3
      _ = 512 * L ^ 6 := by ring
  calc 2 ^ c * n ^ 3 ≤ c ^ 3 * (512 * L ^ 6) := Nat.mul_le_mul h2c hn3
    _ = 512 * c ^ 3 * (L ^ 3) ^ 2 := by ring
    _ ≤ 4096 * c ^ 3 * (L ^ 3) ^ 2 := by gcongr; norm_num

theorem finB (c n h L : ℕ) (hh : 2 ≤ h) (hch : c ≤ 2 * h + 1) (h2c : 2 * h ≤ c)
    (hn : n ≤ 8 * h * L ^ 2) : 2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * (L ^ 3 * 2 ^ (h - 2)) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 2 := ⟨h - 2, by omega⟩
  simp only [Nat.add_sub_cancel]
  have e1 : 2 ^ c ≤ 32 * (2 ^ k) ^ 2 := by
    calc 2 ^ c ≤ 2 ^ (2 * k + 5) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 32 * (2 ^ k) ^ 2 := by ring
  have e2 : n ^ 3 ≤ 512 * (k + 2) ^ 3 * L ^ 6 := by
    calc n ^ 3 ≤ (8 * (k + 2) * L ^ 2) ^ 3 := Nat.pow_le_pow_left hn 3
      _ = 512 * (k + 2) ^ 3 * L ^ 6 := by ring
  have e3 : 8 * (k + 2) ^ 3 ≤ c ^ 3 := by
    calc 8 * (k + 2) ^ 3 = (2 * (k + 2)) ^ 3 := by ring
      _ ≤ c ^ 3 := Nat.pow_le_pow_left h2c 3
  calc 2 ^ c * n ^ 3 ≤ (32 * (2 ^ k) ^ 2) * (512 * (k + 2) ^ 3 * L ^ 6) := Nat.mul_le_mul e1 e2
    _ = 2048 * (8 * (k + 2) ^ 3) * (L ^ 3 * 2 ^ k) ^ 2 := by ring
    _ ≤ 2048 * c ^ 3 * (L ^ 3 * 2 ^ k) ^ 2 := by gcongr
    _ ≤ 4096 * c ^ 3 * (L ^ 3 * 2 ^ k) ^ 2 := by gcongr; norm_num

theorem real_bound (c n M : ℕ) (hc : 1 ≤ c) (h : 2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * M ^ 2) :
    (1 / 64 : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 2) * (2 : ℝ) ^ ((c : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)
      ≤ (M : ℝ) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have e1 : ((c : ℝ) ^ (-(3 : ℝ) / 2)) ^ 2 = ((c : ℝ) ^ 3)⁻¹ := by
    rw [← Real.rpow_mul_natCast hc0.le]
    rw [show (-(3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = -((3 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hc0.le, Real.rpow_natCast]
  have e2 : ((2 : ℝ) ^ ((c : ℝ) / 2)) ^ 2 = (2 : ℝ) ^ c := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show ((c : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((c : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have e3 : ((n : ℝ) ^ ((3 : ℝ) / 2)) ^ 2 = (n : ℝ) ^ 3 := by
    rw [← Real.rpow_mul_natCast hn0]
    rw [show ((3 : ℝ) / 2) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  set X := (1 / 64 : ℝ) * (c : ℝ) ^ (-(3 : ℝ) / 2) * (2 : ℝ) ^ ((c : ℝ) / 2) *
    (n : ℝ) ^ ((3 : ℝ) / 2) with hX
  have hX0 : 0 ≤ X := by positivity
  have hsq : X ^ 2 = (2 : ℝ) ^ c * (n : ℝ) ^ 3 / (4096 * (c : ℝ) ^ 3) := by
    rw [hX, mul_pow, mul_pow, mul_pow, e1, e2, e3]
    field_simp
    ring
  have hcast : (2 : ℝ) ^ c * (n : ℝ) ^ 3 ≤ 4096 * (c : ℝ) ^ 3 * (M : ℝ) ^ 2 := by exact_mod_cast h
  have hle : X ^ 2 ≤ (M : ℝ) ^ 2 := by
    rw [hsq, div_le_iff₀ (by positivity)]
    linarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  nlinarith

end CCLB3ac

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ c n : ℕ, 2 ≤ c → c ≤ n →
    ∃ G : SimpleGraph (Fin n), CClosedGraphs.Peeling.IsCClosed c G ∧
      C * (c : ℝ) ^ (-(3 : ℝ) / 2) * (2 : ℝ) ^ ((c : ℝ) / 2) * (n : ℝ) ^ ((3 : ℝ) / 2)
        ≤ (CClosedGraphs.Peeling.numMaxCliques G : ℝ) := by
  refine ⟨1 / 64, by norm_num, ?_⟩
  intro c n hc hn
  suffices hs : ∃ G : SimpleGraph (Fin n), CClosedGraphs.Peeling.IsCClosed c G ∧
      2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * (CClosedGraphs.Peeling.numMaxCliques G) ^ 2 by
    obtain ⟨G, hG, hb⟩ := hs
    exact ⟨G, hG, CCLB3ac.real_bound c n _ (by omega) hb⟩
  have fin_helper : ∀ L M : ℕ, L ≤ M → 2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * L ^ 2 →
      2 ^ c * n ^ 3 ≤ 4096 * c ^ 3 * M ^ 2 := fun L M hLM h =>
    le_trans h (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLM 2))
  by_cases hc3 : c ≤ 3
  · by_cases hn8 : n < 8
    · obtain ⟨G, hG, hM⟩ := CCLB3ac.base_main (⊤ : SimpleGraph Bool) CCLB3ac.k2_tri
        CCLB3ac.k2_quad (fun _ : Unit => (false, true)) (fun a b _ => Subsingleton.elim a b)
        (fun _ => by simp) (fun _ _ => by simp) c n hc (by simp; omega)
      refine ⟨G, hG, fin_helper (1 ^ 3) _ (by simpa using hM) ?_⟩
      exact CCLB3ac.finA c n 1 hc hc3 (by omega)
    · obtain ⟨p, hp, hp1, hp2⟩ := CCLB3ac.prime_choice n 8 (by norm_num) (by omega)
      have := Fact.mk hp
      classical
      obtain ⟨G, hG, hM⟩ := CCLB3ac.base_main (CCLB3ac.inc (ZMod p)) (CCLB3ac.inc_tri _)
        (CCLB3ac.inc_quad _) (CCLB3ac.incF (ZMod p)) (CCLB3ac.incF_inj _) (CCLB3ac.incF_adj _)
        (CCLB3ac.incF_sep _) c n hc (by simp [Fintype.card_sum, ZMod.card]; nlinarith)
      have hI : Fintype.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
        simp [ZMod.card]; ring
      rw [hI] at hM
      exact ⟨G, hG, fin_helper (p ^ 3) _ hM (CCLB3ac.finA c n p hc hc3 (by omega))⟩
  · set h := c / 2 with hh
    have h2 : 2 ≤ h := by omega
    have hch : 2 * h ≤ c + 1 := by omega
    by_cases hn8 : n < 8 * h
    · obtain ⟨G, hG, hM⟩ := CCLB3ac.blow_main (⊤ : SimpleGraph Bool) CCLB3ac.k2_tri
        CCLB3ac.k2_quad (fun _ : Unit => (false, true)) (fun a b _ => Subsingleton.elim a b)
        (fun _ => by simp) h c n h2 hch (by omega) (by simp; omega)
      refine ⟨G, hG, fin_helper (1 ^ 3 * 2 ^ (h - 2)) _ (by simpa using hM) ?_⟩
      exact CCLB3ac.finB c n h 1 h2 (by omega) (by omega) (by omega)
    · obtain ⟨p, hp, hp1, hp2⟩ := CCLB3ac.prime_choice n (8 * h) (by omega) (by omega)
      have := Fact.mk hp
      classical
      obtain ⟨G, hG, hM⟩ := CCLB3ac.blow_main (CCLB3ac.inc (ZMod p)) (CCLB3ac.inc_tri _)
        (CCLB3ac.inc_quad _) (CCLB3ac.incF (ZMod p)) (CCLB3ac.incF_inj _) (CCLB3ac.incF_adj _)
        h c n h2 hch (by omega) (by simp [Fintype.card_sum, ZMod.card]; nlinarith)
      have hI : Fintype.card (ZMod p × ZMod p × ZMod p) = p ^ 3 := by
        simp [ZMod.card]; ring
      rw [hI] at hM
      exact ⟨G, hG, fin_helper (p ^ 3 * 2 ^ (h - 2)) _ hM
        (CCLB3ac.finB c n h p h2 (by omega) (by omega) (by nlinarith))⟩
