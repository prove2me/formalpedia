-- Prove2me | solution 1 for CClosedGraphs.Improved.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-20T22:44:25.429072+00:00
-- url     : https://prove2.me/submissions/ba274fe9-dbcd-46b5-8098-a7a12d0c4462

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

def nbr (G : SimpleGraph V) (W : Finset V) (v : V) : Finset V :=
  W.filter (G.Adj v)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_nbr {G : SimpleGraph V} {W : Finset V} {v u : V} :
    u ∈ nbr G W v ↔ u ∈ W ∧ G.Adj v u := by simp [nbr]

omit [Fintype V] [DecidableEq V] in
theorem nbr_subset (G : SimpleGraph V) (W : Finset V) (v : V) : nbr G W v ⊆ W :=
  fun _ h => (mem_nbr.mp h).1

omit [Fintype V] [DecidableEq V] in
@[simp] theorem self_not_mem_nbr (G : SimpleGraph V) (W : Finset V) (v : V) :
    v ∉ nbr G W v := by simp

omit [DecidableEq V] in
theorem mem_max_iff (G : SimpleGraph V) (W K : Finset V) :
    K ∈ maxCliquesIn G (W : Set V) ↔ K ⊆ W ∧ G.IsClique (K : Set V) ∧
      ∀ T : Finset V, K ⊆ T → T ⊆ W → G.IsClique (T : Set V) → T ⊆ K := by
  classical
  change (K ∈ Finset.univ.filter (fun T : Finset V => Maximal (fun U : Finset V => (↑U : Set V) ⊆ (W : Set V) ∧ G.IsClique (↑U : Set V)) T)) ↔ _
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change ((K ⊆ W ∧ G.IsClique (K : Set V)) ∧ ∀ ⦃T : Finset V⦄, (T ⊆ W ∧ G.IsClique (T : Set V)) → K ⊆ T → T ⊆ K) ↔ _
  constructor
  · rintro ⟨⟨hW,hC⟩,hm⟩
    exact ⟨hW,hC,fun T hKT hTW hTC => hm ⟨hTW,hTC⟩ hKT⟩
  · rintro ⟨hW,hC,hm⟩
    exact ⟨⟨hW,hC⟩,fun T hT hKT => hm T hKT hT.1 hT.2⟩

omit [DecidableEq V] in
theorem max_subset {G : SimpleGraph V} {W K : Finset V}
    (h : K ∈ maxCliquesIn G (W : Set V)) : K ⊆ W := (mem_max_iff G W K).mp h |>.1

omit [DecidableEq V] in
theorem max_clique {G : SimpleGraph V} {W K : Finset V}
    (h : K ∈ maxCliquesIn G (W : Set V)) : G.IsClique (K : Set V) :=
  ((mem_max_iff G W K).mp h).2.1

omit [DecidableEq V] in
theorem max_nonempty {G : SimpleGraph V} {W K : Finset V} (hW : W.Nonempty)
    (h : K ∈ maxCliquesIn G (W : Set V)) : K.Nonempty := by
  by_contra he
  have hk : K = ∅ := not_nonempty_iff_eq_empty.mp he
  obtain ⟨v,hv⟩ := hW
  have hh := ((mem_max_iff G W K).mp h).2.2 {v} (by simp [hk])
    (singleton_subset_iff.mpr hv) (by simp)
  simpa [hk] using hh (mem_singleton_self v)

omit [DecidableEq V] in
theorem max_restrict {G : SimpleGraph V} {W U K : Finset V}
    (h : K ∈ maxCliquesIn G (W : Set V)) (hKU : K ⊆ U) (hUW : U ⊆ W) :
    K ∈ maxCliquesIn G (U : Set V) := by
  rcases (mem_max_iff G W K).mp h with ⟨_,hC,hm⟩
  exact (mem_max_iff G U K).mpr ⟨hKU,hC,fun T hKT hTU hTC => hm T hKT (hTU.trans hUW) hTC⟩

theorem max_erase_nbr {G : SimpleGraph V} {W K : Finset V} {v : V}
    (h : K ∈ maxCliquesIn G (W : Set V)) (hv : v ∈ K) :
    K.erase v ∈ maxCliquesIn G (nbr G W v : Set V) := by
  rcases (mem_max_iff G W K).mp h with ⟨hKW,hC,hm⟩
  have hEN : K.erase v ⊆ nbr G W v := by
    intro u hu
    rcases mem_erase.mp hu with ⟨hne,hu⟩
    exact mem_nbr.mpr ⟨hKW hu,hC hv hu hne.symm⟩
  refine (mem_max_iff G _ _).mpr ⟨hEN,(fun _ ha _ hb hne => hC (mem_erase.mp ha).2 (mem_erase.mp hb).2 hne),?_⟩
  intro T hET hTN hTC u hu
  have hIns : G.IsClique ((insert v T : Finset V) : Set V) := by
    rw [coe_insert]
    exact hTC.insert (fun b hb _ => (mem_nbr.mp (hTN hb)).2)
  have hKI : K ⊆ insert v T := by
    intro a ha
    by_cases he : a = v
    · simp [he]
    · exact mem_insert_of_mem (hET (mem_erase.mpr ⟨he,ha⟩))
  have hIW : insert v T ⊆ W := insert_subset_iff.mpr ⟨hKW hv,hTN.trans (nbr_subset G W v)⟩
  exact mem_erase.mpr ⟨fun he => by simpa [he] using hTN hu,
    hm (insert v T) hKI hIW hIns (mem_insert_of_mem hu)⟩

omit [Fintype V] in
theorem erase_injective_through (v : V) :
    Set.InjOn (fun K : Finset V => K.erase v) {K | v ∈ K} := by
  intro K hK L hL he
  have := congrArg (insert v) he
  simpa [insert_erase hK,insert_erase hL] using this

theorem through_count_le (G : SimpleGraph V) (W : Finset V) (v : V) :
    ((maxCliquesIn G (W : Set V)).filter (fun K => v ∈ K)).card ≤
      numMaxCliquesIn G (nbr G W v : Set V) := by
  apply Finset.card_le_card_of_injOn (fun K => K.erase v)
  · intro K hK
    rcases mem_filter.mp hK with ⟨hK,hv⟩
    exact max_erase_nbr hK hv
  · intro K hK L hL he
    exact erase_injective_through v (mem_filter.mp hK).2 (mem_filter.mp hL).2 he

end
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

def common (G : SimpleGraph V) (W : Finset V) (u v : V) : Finset V :=
  W.filter (fun w => G.Adj u w ∧ G.Adj v w)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_common {G : SimpleGraph V} {W : Finset V} {u v w : V} :
    w ∈ common G W u v ↔ w ∈ W ∧ G.Adj u w ∧ G.Adj v w := by simp [common]

omit [Fintype V] [DecidableEq V] in
theorem common_coe (G : SimpleGraph V) (W : Finset V) (u v : V) :
    (common G W u v : Set V) = (W : Set V) ∩ G.commonNeighbors u v := by
  ext w
  simp [SimpleGraph.mem_commonNeighbors]

omit [Fintype V] [DecidableEq V] in
theorem closed_iff (c : ℕ) (G : SimpleGraph V) (W : Finset V) :
    IsCClosedOn c G (W : Set V) ↔
      ∀ u ∈ W, ∀ v ∈ W, u ≠ v → c ≤ (common G W u v).card → G.Adj u v := by
  simp only [IsCClosedOn, ← common_coe, Set.ncard_coe_finset, mem_coe]

omit [Fintype V] [DecidableEq V] in
theorem closed_mono {c : ℕ} {G : SimpleGraph V} {W U : Finset V}
    (h : IsCClosedOn c G (W : Set V)) (hUW : U ⊆ W) : IsCClosedOn c G (U : Set V) := by
  rw [closed_iff] at h ⊢
  intro u hu v hv hne hn
  apply h u (hUW hu) v (hUW hv) hne
  apply hn.trans (card_le_card ?_)
  intro w hw
  rcases mem_common.mp hw with ⟨hw,huv,hvv⟩
  exact mem_common.mpr ⟨hUW hw,huv,hvv⟩

omit [Fintype V] [DecidableEq V] in
theorem neighborhood_closed {c : ℕ} {G : SimpleGraph V} {W : Finset V} {v : V}
    (hc : 1 ≤ c) (h : IsCClosedOn c G (W : Set V)) (hv : v ∈ W) :
    IsCClosedOn (c-1) G (nbr G W v : Set V) := by
  rw [closed_iff] at h ⊢
  intro a ha b hb hab hn
  have hav := mem_nbr.mp ha
  have hbv := mem_nbr.mp hb
  apply h a hav.1 b hbv.1 hab
  have hsub : insert v (common G (nbr G W v) a b) ⊆ common G W a b := by
    intro w hw
    rcases mem_insert.mp hw with rfl|hw
    · exact mem_common.mpr ⟨hv,hav.2.symm,hbv.2.symm⟩
    · rcases mem_common.mp hw with ⟨hw,haw,hbw⟩
      exact mem_common.mpr ⟨(mem_nbr.mp hw).1,haw,hbw⟩
  have hnv : v ∉ common G (nbr G W v) a b := by simp
  have hh := card_le_card hsub
  rw [card_insert_of_notMem hnv] at hh
  omega

omit [Fintype V] [DecidableEq V] in
theorem nonadj_common_lt {c : ℕ} {G : SimpleGraph V} {W : Finset V} {u v : V}
    (h : IsCClosedOn c G (W : Set V)) (hu : u ∈ W) (hv : v ∈ W)
    (hne : u ≠ v) (ha : ¬ G.Adj u v) : (common G W u v).card < c := by
  by_contra hn
  exact ha ((closed_iff c G W).mp h u hu v hv hne (by omega))

omit [Fintype V] in
theorem residual_nonempty {G : SimpleGraph V} {W : Finset V} {v : V} (hv : v ∈ W) :
    (W \ nbr G W v).Nonempty := ⟨v,by simp [hv]⟩

omit [Fintype V] in
theorem residual_card (G : SimpleGraph V) (W : Finset V) (v : V) :
    (W \ nbr G W v).card = W.card - (nbr G W v).card :=
  card_sdiff_of_subset (nbr_subset G W v)

omit [Fintype V] [DecidableEq V] in
theorem degree_lt {G : SimpleGraph V} {W : Finset V} {v : V} (hv : v ∈ W) :
    (nbr G W v).card < W.card := by
  apply card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨nbr_subset G W v,fun he => (self_not_mem_nbr G W v) (he.symm ▸ hv)⟩

end
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

theorem maximal_intersect_eq {G : SimpleGraph V} {W K L : Finset V}
    (hG : IsCClosedOn 1 G (W : Set V)) (hK : K ∈ maxCliquesIn G (W : Set V))
    (hL : L ∈ maxCliquesIn G (W : Set V)) {w : V} (hwK : w ∈ K) (hwL : w ∈ L) : K=L := by
  rcases (mem_max_iff G W K).mp hK with ⟨hKW,hKC,hKM⟩
  rcases (mem_max_iff G W L).mp hL with ⟨hLW,hLC,hLM⟩
  have cross : ∀ u ∈ K, ∀ v ∈ L, u ≠ v → G.Adj u v := by
    intro u hu v hv huv
    by_cases huw : u=w
    · subst u; exact hLC hwL hv huv
    by_cases hvw : v=w
    · subst v; exact hKC hu hwK huv
    apply (closed_iff 1 G W).mp hG u (hKW hu) v (hLW hv) huv
    have : 0 < (common G W u v).card := card_pos.mpr ⟨w,
      mem_common.mpr ⟨hKW hwK,hKC hu hwK huw,hLC hv hwL hvw⟩⟩
    omega
  have hUC : G.IsClique ((K ∪ L : Finset V) : Set V) := by
    intro u hu v hv huv
    rcases mem_union.mp hu with hu|hu <;> rcases mem_union.mp hv with hv|hv
    · exact hKC hu hv huv
    · exact cross u hu v hv huv
    · exact (cross v hv u hu huv.symm).symm
    · exact hLC hu hv huv
  have hUW : K ∪ L ⊆ W := union_subset hKW hLW
  have hUK := hKM (K ∪ L) subset_union_left hUW hUC
  have hUL := hLM (K ∪ L) subset_union_right hUW hUC
  exact Subset.antisymm (subset_union_left.trans hUL) (subset_union_right.trans hUK)

theorem one_closed_count {G : SimpleGraph V} {W : Finset V} (hW : W.Nonempty)
    (hG : IsCClosedOn 1 G (W : Set V)) : numMaxCliquesIn G (W : Set V) ≤ W.card := by
  let pick : Finset V → V := fun K => if h : K.Nonempty then h.choose else hW.choose
  have hp : ∀ K ∈ maxCliquesIn G (W : Set V), pick K ∈ K := by
    intro K hK
    simp only [pick, dif_pos (max_nonempty hW hK)]
    exact (max_nonempty hW hK).choose_spec
  apply card_le_card_of_injOn pick
  · intro K hK; exact max_subset hK (hp K hK)
  · intro K hK L hL he
    apply maximal_intersect_eq hG hK hL (hp K hK)
    simpa [he] using hp L hL

theorem zero_degree_count {G : SimpleGraph V} {W : Finset V} (hW : W.Nonempty)
    (hd : ∀ v ∈ W, (nbr G W v).card=0) : numMaxCliquesIn G (W : Set V) ≤ W.card := by
  apply one_closed_count hW
  rw [closed_iff]
  intro u hu v _ _ hn
  have hz : common G W u v = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    have hwN : w ∈ nbr G W u := mem_nbr.mpr ⟨(mem_common.mp hw).1,(mem_common.mp hw).2.1⟩
    have he := card_eq_zero.mp (hd u hu)
    simp [he] at hwN
  simp [hz] at hn

theorem through_zero_le_one (G : SimpleGraph V) (W : Finset V) (v : V)
    (hz : (nbr G W v).card=0) :
    ((maxCliquesIn G (W : Set V)).filter (fun K => v ∈ K)).card ≤ 1 := by
  calc
    _ ≤ ({ {v} } : Finset (Finset V)).card := by
      apply card_le_card
      intro K hK
      rcases mem_filter.mp hK with ⟨hK,hv⟩
      have he : K = {v} := by
        apply Subset.antisymm
        · intro u hu
          by_contra hne
          have huv : u ≠ v := by simpa using hne
          have hN : u ∈ nbr G W v := mem_nbr.mpr ⟨max_subset hK hu,
            max_clique hK hv hu huv.symm⟩
          have hEmpty := card_eq_zero.mp hz
          simp [hEmpty] at hN
        · exact singleton_subset_iff.mpr hv
      simp [he]
    _ = 1 := card_singleton _

end
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

def traces (G : SimpleGraph V) (W : Finset V) (v : V) : Finset (Finset V) :=
  (nbr G W v).powerset.filter Finset.Nonempty

def outside (G : SimpleGraph V) (W : Finset V) (v : V) (S : Finset V) : Finset V :=
  W.filter (fun w => w ≠ v ∧ ¬ G.Adj v w ∧ ∀ s ∈ S, G.Adj s w)

def middle (G : SimpleGraph V) (W : Finset V) (v : V) : Finset (Finset V) :=
  (maxCliquesIn G (W : Set V)).filter (fun K => v ∉ K ∧ (K ∩ nbr G W v).Nonempty)

@[simp] theorem mem_outside {G : SimpleGraph V} {W S : Finset V} {v w : V} :
    w ∈ outside G W v S ↔ w ∈ W ∧ w ≠ v ∧ ¬ G.Adj v w ∧ ∀ s ∈ S, G.Adj s w := by
  simp [outside]

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_traces {G : SimpleGraph V} {W S : Finset V} {v : V} :
    S ∈ traces G W v ↔ S ⊆ nbr G W v ∧ S.Nonempty := by simp [traces]

theorem outside_subset (G : SimpleGraph V) (W S : Finset V) (v : V) :
    outside G W v S ⊆ W := fun _ h => (mem_outside.mp h).1

theorem outside_subset_nbr {G : SimpleGraph V} {W S : Finset V} {v s : V} (hs : s ∈ S) :
    outside G W v S ⊆ nbr G W s := by
  intro w hw
  rcases mem_outside.mp hw with ⟨hw,_,_,hS⟩
  exact mem_nbr.mpr ⟨hw,hS s hs⟩

theorem outside_closed {c : ℕ} {G : SimpleGraph V} {W S : Finset V} {v : V}
    (hc : 1 ≤ c) (hG : IsCClosedOn c G (W : Set V)) (hS : S ∈ traces G W v) :
    IsCClosedOn (c-1) G (outside G W v S : Set V) := by
  obtain ⟨hSN,s,hs⟩ := mem_traces.mp hS
  exact closed_mono (neighborhood_closed hc hG (mem_nbr.mp (hSN hs)).1)
    (outside_subset_nbr hs)

theorem middle_outside_nonempty {G : SimpleGraph V} {W K : Finset V} {v : V}
    (hv : v ∈ W) (hK : K ∈ middle G W v) : (K \ nbr G W v).Nonempty := by
  rcases mem_filter.mp hK with ⟨hK,hvK,_⟩
  by_contra hn
  have hKN : K ⊆ nbr G W v := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hn)
  have hKC := max_clique hK
  have hIC : G.IsClique ((insert v K : Finset V) : Set V) := by
    rw [coe_insert]
    exact hKC.insert (fun u hu _ => (mem_nbr.mp (hKN hu)).2)
  have hi := ((mem_max_iff G W K).mp hK).2.2 (insert v K) (subset_insert _ _)
    (insert_subset_iff.mpr ⟨hv,max_subset hK⟩) hIC
  exact hvK (hi (mem_insert_self v K))

theorem middle_remainder_max {G : SimpleGraph V} {W K : Finset V} {v : V}
    (hK : K ∈ middle G W v) :
    K \ nbr G W v ∈ maxCliquesIn G (outside G W v (K ∩ nbr G W v) : Set V) := by
  rcases mem_filter.mp hK with ⟨hK,hvK,_⟩
  have hKW := max_subset hK
  have hKC := max_clique hK
  have hsub : K \ nbr G W v ⊆ outside G W v (K ∩ nbr G W v) := by
    intro w hw
    rcases mem_sdiff.mp hw with ⟨hw,hwN⟩
    refine mem_outside.mpr ⟨hKW hw,fun he => hvK (he ▸ hw),?_,?_⟩
    · exact fun ha => hwN (mem_nbr.mpr ⟨hKW hw,ha⟩)
    · intro s hs
      exact hKC (mem_inter.mp hs).1 hw (fun he => hwN (he ▸ (mem_inter.mp hs).2))
  refine (mem_max_iff G _ _).mpr ⟨hsub,?_,?_⟩
  · exact fun _ ha _ hb hne => hKC (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 hne
  · intro T hRT hTU hTC
    have hUC : G.IsClique (((K ∩ nbr G W v) ∪ T : Finset V) : Set V) := by
      intro a ha b hb hab
      rcases mem_union.mp ha with ha|ha <;> rcases mem_union.mp hb with hb|hb
      · exact hKC (mem_inter.mp ha).1 (mem_inter.mp hb).1 hab
      · exact (mem_outside.mp (hTU hb)).2.2.2 a ha
      · exact ((mem_outside.mp (hTU ha)).2.2.2 b hb).symm
      · exact hTC ha hb hab
    have hKU : K ⊆ (K ∩ nbr G W v) ∪ T := by
      intro a ha
      by_cases hN : a ∈ nbr G W v
      · exact mem_union_left _ (mem_inter.mpr ⟨ha,hN⟩)
      · exact mem_union_right _ (hRT (mem_sdiff.mpr ⟨ha,hN⟩))
    have hUW : (K ∩ nbr G W v) ∪ T ⊆ W := union_subset
      (inter_subset_left.trans hKW) (hTU.trans (outside_subset G W _ v))
    have hUK := ((mem_max_iff G W K).mp hK).2.2 _ hKU hUW hUC
    intro a ha
    have hao := mem_outside.mp (hTU ha)
    exact mem_sdiff.mpr ⟨hUK (mem_union_right _ ha),fun hN => hao.2.2.1 (mem_nbr.mp hN).2⟩

theorem middle_fiber_count {G : SimpleGraph V} {W S : Finset V} {v : V} :
    ((middle G W v).filter (fun K => K ∩ nbr G W v = S)).card ≤
      numMaxCliquesIn G (outside G W v S : Set V) := by
  apply card_le_card_of_injOn (fun K => K \ nbr G W v)
  · intro K hK
    rcases mem_filter.mp hK with ⟨hK,hS⟩
    simpa [hS] using middle_remainder_max hK
  · intro K hK L hL he
    have hKS := (mem_filter.mp hK).2
    have hLS := (mem_filter.mp hL).2
    have hpart (A : Finset V) : (A ∩ nbr G W v) ∪ (A \ nbr G W v) = A := by
      ext a; simp only [mem_union,mem_inter,mem_sdiff]; tauto
    change K \ nbr G W v = L \ nbr G W v at he
    rw [← hpart K,← hpart L,hKS,hLS,he]

theorem middle_fiber_empty {G : SimpleGraph V} {W S : Finset V} {v : V}
    (hv : v ∈ W) (hS : (outside G W v S).card=0) :
    ((middle G W v).filter (fun K => K ∩ nbr G W v=S)).card=0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro K hK
  rcases mem_filter.mp hK with ⟨hK,hKS⟩
  obtain ⟨w,hw⟩ := middle_outside_nonempty hv hK
  have hm := max_subset (middle_remainder_max hK) hw
  have he := card_eq_zero.mp hS
  simp [hKS,he] at hm

end
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

theorem outside_sum_bound {c : ℕ} {G : SimpleGraph V} {W : Finset V} {v : V}
    (hv : v ∈ W) (hG : IsCClosedOn c G (W : Set V)) :
    ∑ S ∈ traces G W v, (outside G W v S).card ≤ W.card * 2^(c-1) := by
  have hf : ∀ w ∈ W,
      ((traces G W v).filter (fun S => w ∈ outside G W v S)).card ≤ 2^(c-1) := by
    intro w hw
    by_cases he : w=v
    · subst w; simp
    by_cases ha : G.Adj v w
    · simp [ha]
    have hsub : (traces G W v).filter (fun S => w ∈ outside G W v S) ⊆
        (common G W v w).powerset := by
      intro S hS
      rcases mem_filter.mp hS with ⟨hS,hwS⟩
      apply mem_powerset.mpr
      intro s hs
      have hsN := (mem_traces.mp hS).1 hs
      exact mem_common.mpr ⟨(mem_nbr.mp hsN).1,(mem_nbr.mp hsN).2,
        ((mem_outside.mp hwS).2.2.2 s hs).symm⟩
    have hc := nonadj_common_lt hG hv hw (Ne.symm he) ha
    calc
      _ ≤ ((common G W v w).powerset).card := card_le_card hsub
      _ = 2^(common G W v w).card := card_powerset _
      _ ≤ 2^(c-1) := Nat.pow_le_pow_right (by omega) (by omega)
  have heq : ∑ S ∈ traces G W v, (outside G W v S).card =
      ∑ w ∈ W, ((traces G W v).filter (fun S => w ∈ outside G W v S)).card := by
    have hh (S : Finset V) : (outside G W v S).card =
        ∑ w ∈ W, if w ∈ outside G W v S then 1 else 0 := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      congr 1
      ext w
      simp only [mem_filter, mem_outside]
      tauto
    simp_rw [hh]
    rw [sum_comm]
    apply sum_congr rfl
    intro w _
    rw [← sum_filter]
    simp
  rw [heq]
  calc
    _ ≤ ∑ _w ∈ W, 2^(c-1) := sum_le_sum hf
    _ = W.card * 2^(c-1) := by simp

theorem middle_count_bound {c : ℕ} {G : SimpleGraph V} {W : Finset V} {v : V}
    (hc : 2 ≤ c) (hv : v ∈ W) (hG : IsCClosedOn c G (W : Set V))
    (hdeg : ∀ u ∈ W, (nbr G W u).card ≤ (nbr G W v).card)
    {B : ℝ} (hB : 0 ≤ B)
    (ih : ∀ U : Finset V, U ⊆ W → U.Nonempty → U.card ≤ (nbr G W v).card →
      IsCClosedOn (c-1) G (U : Set V) →
      (numMaxCliquesIn G (U : Set V) : ℝ) ≤ B * (U.card : ℝ)) :
    ((middle G W v).card : ℝ) ≤ B * ((W.card : ℝ) * (2 : ℝ)^(c-1)) := by
  have hf : ∀ S ∈ traces G W v,
      (((middle G W v).filter (fun K => K ∩ nbr G W v=S)).card : ℝ) ≤
        B * ((outside G W v S).card : ℝ) := by
    intro S hS
    by_cases hz : (outside G W v S).card=0
    · simp [middle_fiber_empty hv hz,hz]
    have hn : (outside G W v S).Nonempty := card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨s,hs⟩ := (mem_traces.mp hS).2
    have hsW := (mem_nbr.mp ((mem_traces.mp hS).1 hs)).1
    have hd := (card_le_card (outside_subset_nbr (G := G) (W := W) (v := v) hs)).trans (hdeg s hsW)
    have hh : (((middle G W v).filter (fun K => K ∩ nbr G W v=S)).card : ℝ) ≤
        (numMaxCliquesIn G (outside G W v S : Set V) : ℝ) := by
      exact_mod_cast (middle_fiber_count (G := G) (W := W) (S := S) (v := v))
    exact hh.trans (ih _ (outside_subset G W S v) hn hd (outside_closed (by omega) hG hS))
  have heq : (middle G W v).card =
      ∑ S ∈ traces G W v, ((middle G W v).filter (fun K => K ∩ nbr G W v=S)).card := by
    apply card_eq_sum_card_fiberwise
    intro K hK
    exact mem_traces.mpr ⟨inter_subset_right,(mem_filter.mp hK).2.2⟩
  rw [heq, Nat.cast_sum]
  calc
    _ ≤ ∑ S ∈ traces G W v, B * ((outside G W v S).card : ℝ) := sum_le_sum hf
    _ = B * ((∑ S ∈ traces G W v, (outside G W v S).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum,mul_sum]
    _ ≤ B * ((W.card : ℝ) * (2 : ℝ)^(c-1)) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast outside_sum_bound hv hG) hB

end
end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable section
open scoped Classical

theorem low_count_bound {c D : ℕ} {G : SimpleGraph V} {W : Finset V}
    (hc : 2 ≤ c) (hW : W.Nonempty) (hG : IsCClosedOn c G (W : Set V))
    (hD : 0 < D) (hdeg : ∀ v ∈ W, (nbr G W v).card ≤ D)
    {M : ℝ} (hM : 1 ≤ M)
    (ih : ∀ U : Finset V, U ⊆ W → U.Nonempty → U.card ≤ D →
      IsCClosedOn (c-1) G (U : Set V) → (numMaxCliquesIn G (U : Set V) : ℝ) ≤ M) :
    (numMaxCliquesIn G (W : Set V) : ℝ) ≤ (W.card : ℝ) * M := by
  have _ := hD
  let through := fun v => (maxCliquesIn G (W : Set V)).filter (fun K => v ∈ K)
  have hsub : maxCliquesIn G (W : Set V) ⊆ W.biUnion through := by
    intro K hK
    obtain ⟨v,hv⟩ := max_nonempty hW hK
    exact mem_biUnion.mpr ⟨v,max_subset hK hv,mem_filter.mpr ⟨hK,hv⟩⟩
  have hh : numMaxCliquesIn G (W : Set V) ≤ ∑ v ∈ W, (through v).card :=
    (card_le_card hsub).trans card_biUnion_le
  have hb : ∀ v ∈ W, ((through v).card : ℝ) ≤ M := by
    intro v hv
    by_cases hz : (nbr G W v).card=0
    · have hh : ((through v).card : ℝ) ≤ 1 := by exact_mod_cast through_zero_le_one G W v hz
      exact hh.trans hM
    · have hh : ((through v).card : ℝ) ≤ (numMaxCliquesIn G (nbr G W v : Set V) : ℝ) := by
        exact_mod_cast through_count_le G W v
      exact hh.trans (ih _ (nbr_subset G W v) (card_pos.mp (Nat.pos_of_ne_zero hz)) (hdeg v hv)
          (neighborhood_closed (by omega) hG hv))
  calc
    _ ≤ ∑ v ∈ W, ((through v).card : ℝ) := by exact_mod_cast hh
    _ ≤ ∑ _v ∈ W, M := sum_le_sum hb
    _ = (W.card : ℝ) * M := by simp

theorem high_count_bound {c : ℕ} {G : SimpleGraph V} {W : Finset V} {v : V}
    (hc : 2 ≤ c) (hv : v ∈ W) (hG : IsCClosedOn c G (W : Set V))
    (hD : 0 < (nbr G W v).card)
    (hdeg : ∀ u ∈ W, (nbr G W u).card ≤ (nbr G W v).card)
    {B : ℝ} (hB : 0 ≤ B)
    (ih : ∀ U : Finset V, U ⊆ W → U.Nonempty → U.card ≤ (nbr G W v).card →
      IsCClosedOn (c-1) G (U : Set V) →
      (numMaxCliquesIn G (U : Set V) : ℝ) ≤ B * (U.card : ℝ)) :
    (numMaxCliquesIn G (W : Set V) : ℝ) ≤
      B * ((nbr G W v).card + (W.card : ℝ) * (2 : ℝ) ^ (c-1)) +
        (numMaxCliquesIn G ((W \ nbr G W v : Finset V) : Set V) : ℝ) := by
  let P := (maxCliquesIn G (W : Set V)).filter (fun K => v ∈ K)
  let Q := middle G W v
  let R := maxCliquesIn G ((W \ nbr G W v : Finset V) : Set V)
  have hsub : maxCliquesIn G (W : Set V) ⊆ (P ∪ Q) ∪ R := by
    intro K hK
    by_cases hvK : v ∈ K
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hK,hvK⟩))
    by_cases hmeet : (K ∩ nbr G W v).Nonempty
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hK,hvK,hmeet⟩))
    apply mem_union_right
    apply max_restrict hK
    · intro u hu
      refine mem_sdiff.mpr ⟨max_subset hK hu,?_⟩
      exact fun hN => hmeet ⟨u,mem_inter.mpr ⟨hu,hN⟩⟩
    · exact sdiff_subset
  have hcard : numMaxCliquesIn G (W : Set V) ≤ P.card+Q.card+R.card :=
    (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hP : (P.card : ℝ) ≤ B * (nbr G W v).card := by
    have hh : (P.card : ℝ) ≤ (numMaxCliquesIn G (nbr G W v : Set V) : ℝ) := by
      exact_mod_cast through_count_le G W v
    exact hh.trans (ih _ (nbr_subset G W v) (card_pos.mp hD) le_rfl (neighborhood_closed (by omega) hG hv))
  have hQ : (Q.card : ℝ) ≤ B * ((W.card : ℝ) * (2 : ℝ)^(c-1)) :=
    middle_count_bound hc hv hG hdeg hB ih
  have hreal : (numMaxCliquesIn G (W : Set V) : ℝ) ≤ (P.card : ℝ)+Q.card+R.card := by
    exact_mod_cast hcard
  change (numMaxCliquesIn G (W : Set V) : ℝ) ≤
    B * ((nbr G W v).card + (W.card : ℝ) * (2 : ℝ)^(c-1)) + (R.card : ℝ)
  nlinarith

end
end CClosedBoundProof

namespace CClosedBoundProof

noncomputable def coefficient (c : ℕ) : ℝ :=
  (4 : ℝ) ^ (((c : ℝ) + 4) * ((c : ℝ) - 1) / 2)

noncomputable def exponent (c : ℕ) : ℝ :=
  2 - (2 : ℝ) ^ (1 - (c : ℝ))

noncomputable def bound (n : ℝ) (c : ℕ) : ℝ := coefficient c * n ^ exponent c

lemma bound_eq_F0 (n : ℝ) (c : ℕ) :
    bound n c = CClosedGraphs.Improved.F0 n c := rfl

lemma coefficient_pos (c : ℕ) : 0 < coefficient c := by
  exact Real.rpow_pos_of_pos (by norm_num) _

lemma coefficient_one : coefficient 1 = 1 := by norm_num [coefficient]
lemma exponent_one : exponent 1 = 1 := by norm_num [exponent]
lemma bound_one (n : ℝ) : bound n 1 = n := by
  simp [bound, coefficient_one, exponent_one]

lemma coefficient_ge_one {c : ℕ} (hc : 1 ≤ c) : 1 ≤ coefficient c := by
  apply Real.one_le_rpow (by norm_num)
  have : (1 : ℝ) ≤ c := by exact_mod_cast hc
  positivity

lemma exponent_ge_one {c : ℕ} (hc : 1 ≤ c) : 1 ≤ exponent c := by
  have : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hh := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ)) (by norm_num)
    (show 1 - (c : ℝ) ≤ 0 by linarith)
  simp only [Real.rpow_zero] at hh
  dsimp [exponent]
  linarith

lemma exponent_succ (c : ℕ) : exponent (c + 1) = 1 + exponent c / 2 := by
  have he : 1 - ((c + 1 : ℕ) : ℝ) = (1 - (c : ℝ)) + (-1) := by push_cast; ring
  rw [exponent, he, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  rw [Real.rpow_neg_one]
  dsimp [exponent]
  ring

lemma coefficient_succ (c : ℕ) :
    coefficient (c + 1) = coefficient c * (4 : ℝ) ^ (c + 2) := by
  have he : ((((c + 1 : ℕ) : ℝ) + 4) * (((c + 1 : ℕ) : ℝ) - 1) / 2) =
      ((c : ℝ) + 4) * ((c : ℝ) - 1) / 2 + ((c + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [coefficient, he, Real.rpow_add (by norm_num : (0 : ℝ) < 4),
    Real.rpow_natCast]
  rfl

lemma coefficient_mono_step (c : ℕ) : coefficient c ≤ coefficient (c + 1) := by
  rw [coefficient_succ]
  exact le_mul_of_one_le_right (coefficient_pos c).le (one_le_pow₀ (by norm_num))

lemma coefficient_absorb (c : ℕ) :
    coefficient c * (2 : ℝ) ^ (c + 1) ≤ coefficient (c + 1) := by
  rw [coefficient_succ]
  apply mul_le_mul_of_nonneg_left _ (coefficient_pos c).le
  calc
    (2 : ℝ) ^ (c + 1) ≤ (4 : ℝ) ^ (c + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ ≤ (4 : ℝ) ^ (c + 2) := by
      calc
        (4 : ℝ) ^ (c + 1) ≤ (4 : ℝ) ^ (c + 1) * 4 := by
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) (c + 1)]
        _ = (4 : ℝ) ^ (c + 2) := (pow_succ (4 : ℝ) (c + 1)).symm

lemma bound_ge_self {n : ℝ} (hn : 1 ≤ n) {c : ℕ} (hc : 1 ≤ c) : n ≤ bound n c := by
  have hp : n ≤ n ^ exponent c := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hn (exponent_ge_one hc)
  exact hp.trans (le_mul_of_one_le_left (by positivity) (coefficient_ge_one hc))

lemma bound_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) {c : ℕ} (hc : 1 ≤ c) :
    bound x c ≤ bound y c := by
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hx hxy (by linarith [exponent_ge_one hc])) (coefficient_pos c).le

lemma bound_linear {x D : ℝ} (hx : 0 < x) (hxD : x ≤ D) {c : ℕ} (hc : 1 ≤ c) :
    bound x c ≤ (coefficient c * D ^ (exponent c - 1)) * x := by
  have hpow := Real.rpow_le_rpow hx.le hxD (show 0 ≤ exponent c - 1 by linarith [exponent_ge_one hc])
  have he : x ^ exponent c = x ^ (exponent c - 1) * x := by
    rw [← Real.rpow_add_one hx.ne']
    congr 1
    ring
  dsimp [bound]
  rw [he]
  nlinarith [coefficient_pos c, mul_le_mul_of_nonneg_right hpow hx.le]

lemma low_absorption {n D : ℝ} (hn : 0 < n) (hD : 0 ≤ D) (hDn : D ^ 2 ≤ n)
    {c : ℕ} (hc : 1 ≤ c) : n * bound D c ≤ bound n (c + 1) := by
  have hq : 0 ≤ exponent c / 2 := by linarith [exponent_ge_one hc]
  have hp : D ^ exponent c ≤ n ^ (exponent c / 2) := by
    have h := Real.rpow_le_rpow (sq_nonneg D) hDn hq
    have he : (D ^ 2) ^ (exponent c / 2) = D ^ exponent c := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hD]
      congr 1
      ring
    rwa [he] at h
  have hnexp : n * n ^ (exponent c / 2) = n ^ exponent (c + 1) := by
    rw [exponent_succ, Real.rpow_add hn, Real.rpow_one]
  dsimp [bound]
  calc
    n * (coefficient c * D ^ exponent c)
        ≤ coefficient c * (n * n ^ (exponent c / 2)) := by
          nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hn.le (coefficient_pos c).le)]
    _ = coefficient c * n ^ exponent (c + 1) := by rw [hnexp]
    _ ≤ coefficient (c + 1) * n ^ exponent (c + 1) :=
      mul_le_mul_of_nonneg_right (coefficient_mono_step c) (by positivity)

lemma high_scaling {n D e : ℝ} (hn : 0 < n) (hD : 0 < D) (he : 0 ≤ e)
    (hDn : n ≤ D ^ 2) : n * D ^ (1 - 2 * e) ≤ D * n ^ (1 - e) := by
  have hp : n ^ e ≤ D ^ (2 * e) := by
    have h := Real.rpow_le_rpow hn.le hDn he
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le] at h
    norm_num at h ⊢
    exact h
  have hnprod : n ^ (1 - e) * n ^ e = n := by
    rw [← Real.rpow_add hn]
    ring_nf
    exact Real.rpow_one n
  have hDprod : D ^ (1 - 2 * e) * D ^ (2 * e) = D := by
    rw [← Real.rpow_add hD]
    ring_nf
    exact Real.rpow_one D
  calc
    n * D ^ (1 - 2 * e) = (n ^ (1 - e) * n ^ e) * D ^ (1 - 2 * e) := by rw [hnprod]
    _ = (n ^ (1 - e) * D ^ (1 - 2 * e)) * n ^ e := by ring
    _ ≤ (n ^ (1 - e) * D ^ (1 - 2 * e)) * D ^ (2 * e) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = D * n ^ (1 - e) := by rw [mul_assoc, hDprod]; ring

lemma chord_bound {n D p : ℝ} (hn : 0 < n) (hD : 0 ≤ D) (hDn : D < n) (hp : 1 ≤ p) :
    (n - D) ^ p ≤ n ^ p - D * n ^ (p - 1) := by
  have hnD : 0 < n - D := sub_pos.mpr hDn
  have h := Real.rpow_le_rpow hnD.le (show n - D ≤ n by linarith)
    (show 0 ≤ p - 1 by linarith)
  have hleft : (n - D) ^ p = (n - D) * (n - D) ^ (p - 1) := by
    calc
      (n - D) ^ p = (n - D) ^ ((p - 1) + 1) := by congr 1; ring
      _ = (n - D) ^ (p - 1) * (n - D) := Real.rpow_add_one hnD.ne' _
      _ = (n - D) * (n - D) ^ (p - 1) := mul_comm _ _
  have hright : n ^ p = n * n ^ (p - 1) := by
    calc
      n ^ p = n ^ ((p - 1) + 1) := by congr 1; ring
      _ = n ^ (p - 1) * n := Real.rpow_add_one hn.ne' _
      _ = n * n ^ (p - 1) := mul_comm _ _
  rw [hleft, hright]
  nlinarith [mul_le_mul_of_nonneg_left h hnD.le]

lemma high_absorption {n D : ℝ} (hn : 0 < n) (hD : 0 < D) (hDn : D < n)
    (hlarge : n ≤ D ^ 2) (c : ℕ) :
    (coefficient c * D ^ (exponent c - 1)) * (D + n * (2 : ℝ) ^ c) +
      bound (n - D) (c + 1) ≤ bound n (c + 1) := by
  let e : ℝ := (2 : ℝ) ^ (1 - ((c + 1 : ℕ) : ℝ))
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hp : exponent (c + 1) - 1 = 1 - e := by dsimp [exponent, e]; ring
  have hq : exponent c - 1 = 1 - 2 * e := by
    have hrec := exponent_succ c
    dsimp [exponent] at hrec
    dsimp [exponent, e]
    linarith
  have hscale : n * D ^ (exponent c - 1) ≤ D * n ^ (exponent (c + 1) - 1) := by
    rw [hp, hq]
    exact high_scaling hn hD he hlarge
  have hcount : D + n * (2 : ℝ) ^ c ≤ n * (2 : ℝ) ^ (c + 1) := by
    rw [pow_succ]
    have : 1 ≤ (2 : ℝ) ^ c := one_le_pow₀ (by norm_num)
    nlinarith
  have hcoef := coefficient_absorb c
  have hterm : (coefficient c * D ^ (exponent c - 1)) * (D + n * (2 : ℝ) ^ c) ≤
      coefficient (c + 1) * (D * n ^ (exponent (c + 1) - 1)) := by
    calc
      _ ≤ (coefficient c * D ^ (exponent c - 1)) * (n * (2 : ℝ) ^ (c + 1)) :=
        mul_le_mul_of_nonneg_left hcount
          (mul_nonneg (coefficient_pos c).le (Real.rpow_nonneg hD.le _))
      _ = (coefficient c * (2 : ℝ) ^ (c + 1)) * (n * D ^ (exponent c - 1)) := by ring
      _ ≤ coefficient (c + 1) * (D * n ^ (exponent (c + 1) - 1)) :=
        mul_le_mul hcoef hscale (by positivity) (coefficient_pos _).le
  have hchord := chord_bound hn hD.le hDn (exponent_ge_one (show 1 ≤ c + 1 by omega))
  have hrem := mul_le_mul_of_nonneg_left hchord (coefficient_pos (c + 1)).le
  dsimp [bound]
  nlinarith

end CClosedBoundProof

namespace CClosedBoundProof
open Finset CClosedGraphs.Peeling CClosedGraphs.Improved

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem relative_bound (k : ℕ) (G : SimpleGraph V) :
    ∀ W : Finset V, W.Nonempty → IsCClosedOn (k + 1) G (W : Set V) →
      (numMaxCliquesIn G (W : Set V) : ℝ) ≤ bound (W.card : ℝ) (k + 1) := by
  classical
  induction k with
  | zero =>
    intro W hW hG
    rw [bound_one]
    exact_mod_cast one_closed_count hW hG
  | succ k ih =>
    have aux : ∀ n : ℕ, ∀ W : Finset V, W.card = n → W.Nonempty →
        IsCClosedOn (k + 1 + 1) G (W : Set V) →
        (numMaxCliquesIn G (W : Set V) : ℝ) ≤ bound (W.card : ℝ) (k + 1 + 1) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n inner =>
        intro W hcard hW hG
        obtain ⟨v,hv,hmax⟩ := W.exists_max_image (fun u => (nbr G W u).card) hW
        let D : ℕ := (nbr G W v).card
        have hdeg : ∀ u ∈ W, (nbr G W u).card ≤ D := hmax
        have hDn : D < W.card := degree_lt hv
        have hn : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
        have hn1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
        by_cases hzero : D = 0
        · have hz := zero_degree_count hW (fun u hu => Nat.eq_zero_of_le_zero (hzero ▸ hdeg u hu))
          have hzreal : (numMaxCliquesIn G (W : Set V) : ℝ) ≤ W.card := by exact_mod_cast hz
          exact hzreal.trans (bound_ge_self hn1 (by omega))
        have hD : 0 < D := Nat.pos_of_ne_zero hzero
        have hDr : (0 : ℝ) < D := by exact_mod_cast hD
        have hDr1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
        have hDnr : (D : ℝ) < W.card := by exact_mod_cast hDn
        by_cases hsmall : (D : ℝ) ^ 2 ≤ W.card
        · have hM : 1 ≤ bound (D : ℝ) (k + 1) := hDr1.trans (bound_ge_self hDr1 (by omega))
          have hh := low_count_bound (D := D) (by omega : 2 ≤ k + 1 + 1) hW hG hD hdeg hM
            (fun U _ hU hUD hclosed =>
              (ih U hU (by simpa using hclosed)).trans
                (bound_mono (by positivity) (by exact_mod_cast hUD) (by omega)))
          exact hh.trans (low_absorption hn hDr.le hsmall (by omega))
        · let U : Finset V := W \ nbr G W v
          have hU : U.Nonempty := residual_nonempty hv
          have hUW : U ⊆ W := sdiff_subset
          have hUcard : U.card = W.card - D := residual_card G W v
          have hUn : U.card < n := by
            rw [hUcard, hcard]
            omega
          have hclosed : IsCClosedOn (k + 1 + 1) G (U : Set V) := closed_mono hG hUW
          have hr := inner U.card hUn U rfl hU hclosed
          have hUreal : (U.card : ℝ) = (W.card : ℝ) - D := by
            rw [hUcard, Nat.cast_sub hDn.le]
          rw [hUreal] at hr
          let B : ℝ := coefficient (k + 1) * (D : ℝ) ^ (exponent (k + 1) - 1)
          have hB : 0 ≤ B := mul_nonneg (coefficient_pos _).le (Real.rpow_nonneg hDr.le _)
          have hh := high_count_bound (by omega : 2 ≤ k + 1 + 1) hv hG hD hdeg hB
            (fun S _ hS hSD hclosed =>
              (ih S hS (by simpa using hclosed)).trans
                (bound_linear (by exact_mod_cast hS.card_pos) (by exact_mod_cast hSD) (by omega)))
          have hh' : (numMaxCliquesIn G (W : Set V) : ℝ) ≤
              B * ((D : ℝ) + (W.card : ℝ) * (2 : ℝ) ^ (k + 1)) +
                (numMaxCliquesIn G (U : Set V) : ℝ) := by
            simpa only [Nat.add_sub_cancel, D, U] using hh
          have hs := high_absorption hn hDr hDnr (le_of_not_ge hsmall) (k + 1)
          dsimp only [B] at hh'
          linarith
    intro W hW hG
    exact aux W.card W rfl hW hG

end CClosedBoundProof

namespace CClosedGraphs.Improved
theorem theorem_3_1 (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : CClosedGraphs.Peeling.IsCClosed c G) :
    (CClosedGraphs.Peeling.numMaxCliques G : ℝ) ≤
      (4 : ℝ) ^ (((c : ℝ) + 4) * ((c : ℝ) - 1) / 2) *
        (n : ℝ) ^ ((2 : ℝ) - (2 : ℝ) ^ (1 - (c : ℝ))) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  have hW : (Finset.univ : Finset (Fin n)).Nonempty := by
    exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hclosed : IsCClosedOn (k + 1) G ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    simpa only [Finset.coe_univ, IsCClosedOn, CClosedGraphs.Peeling.IsCClosed, Set.mem_univ, forall_const, Set.univ_inter] using hG
  have hh := CClosedBoundProof.relative_bound k G Finset.univ hW hclosed
  simpa only [CClosedGraphs.Peeling.numMaxCliques, Finset.coe_univ, Finset.card_univ,
    Fintype.card_fin, CClosedBoundProof.bound, CClosedBoundProof.coefficient,
    CClosedBoundProof.exponent] using hh
end CClosedGraphs.Improved

theorem solution (c n : ℕ) (hc : 0 < c) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hG : CClosedGraphs.Peeling.IsCClosed c G) :
    (CClosedGraphs.Peeling.numMaxCliques G : ℝ) ≤
      (4 : ℝ) ^ (((c : ℝ) + 4) * ((c : ℝ) - 1) / 2) *
        (n : ℝ) ^ ((2 : ℝ) - (2 : ℝ) ^ (1 - (c : ℝ))) :=
  CClosedGraphs.Improved.theorem_3_1 c n hc hn G hG
