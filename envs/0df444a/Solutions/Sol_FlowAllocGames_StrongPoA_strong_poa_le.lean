-- Prove2me | solution 1 for FlowAllocGames.StrongPoA.strong_poa_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T16:37:10.535298+00:00
-- url     : https://prove2.me/submissions/93c0af5a-94ac-4458-ab78-0d33b9617fde

import Mathlib
import Definitions.Def_FlowAllocGames_StrongPoA_Model
import Definitions.Def_FlowAllocGames_StrongPoA_Cycles

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace FlowAllocGames.StrongPoA

open Finset

/-- `LawfulBEq` for the derived `BEq` instance of `Sum` (used by `List.count` on `ExtEdge`). -/
instance instLawfulBEqSumP10 {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] :
    LawfulBEq (α ⊕ β) where
  eq_of_beq {a b} h := by
    cases a with
    | inl x => cases b with
      | inl y => exact congrArg Sum.inl (eq_of_beq (show (x == y) = true from h))
      | inr y => exact absurd (show false = true from h) Bool.false_ne_true
    | inr x => cases b with
      | inl y => exact absurd (show false = true from h) Bool.false_ne_true
      | inr y => exact congrArg Sum.inr (eq_of_beq (show (x == y) = true from h))
  rfl {a} := by
    cases a with
    | inl x => exact (show (x == x) = true from beq_self_eq_true x)
    | inr x => exact (show (x == x) = true from beq_self_eq_true x)

section WaterFill

variable {E : Type*} [DecidableEq E]

/-- Water filling of `y` units along the list `L`, edge `e0` first, up to the targets `t`. -/
def wf (t : E → ℕ) : List E → ℕ → E → ℕ
  | [], _, _ => 0
  | e0 :: L, y, e => (if e = e0 then min (t e0) y else 0) + wf t L (y - min (t e0) y) e

lemma wf_not_mem (t : E → ℕ) : ∀ (L : List E) (y : ℕ) (e : E), e ∉ L → wf t L y e = 0
  | [], _, _, _ => rfl
  | e0 :: L, y, e, h => by
    simp only [List.mem_cons, not_or] at h
    simp [wf, h.1, wf_not_mem t L _ e h.2]

lemma wf_zero (t : E → ℕ) : ∀ (L : List E) (e : E), wf t L 0 e = 0
  | [], _ => rfl
  | e0 :: L, e => by simp [wf, wf_zero t L e]

lemma wf_le (t : E → ℕ) : ∀ (L : List E), L.Nodup → ∀ y e, wf t L y e ≤ t e
  | [], _, _, _ => Nat.zero_le _
  | e0 :: L, hL, y, e => by
    rw [List.nodup_cons] at hL
    by_cases he : e = e0
    · subst he
      simp [wf, wf_not_mem t L _ e hL.1]
    · simp only [wf, he, if_false, zero_add]
      exact wf_le t L hL.2 _ e

lemma wf_mono (t : E → ℕ) : ∀ (L : List E) (e : E), Monotone (fun y => wf t L y e)
  | [], _ => fun _ _ _ => le_rfl
  | e0 :: L, e => by
    intro y1 y2 hy
    simp only [wf]
    have h2 : y1 - min (t e0) y1 ≤ y2 - min (t e0) y2 := by omega
    have h3 : wf t L (y1 - min (t e0) y1) e ≤ wf t L (y2 - min (t e0) y2) e :=
      wf_mono t L e h2
    split_ifs <;> omega

lemma wf_sum (t : E → ℕ) : ∀ (L : List E), L.Nodup → ∀ y,
    ∑ e ∈ L.toFinset, wf t L y e = min (∑ e ∈ L.toFinset, t e) y
  | [], _, y => by simp
  | e0 :: L, hL, y => by
    rw [List.nodup_cons] at hL
    have hnot : e0 ∉ L.toFinset := by simpa using hL.1
    rw [List.toFinset_cons, sum_insert hnot, sum_insert hnot]
    have hrest : ∑ e ∈ L.toFinset, wf t (e0 :: L) y e =
        ∑ e ∈ L.toFinset, wf t L (y - min (t e0) y) e := by
      apply sum_congr rfl
      intro e he
      have hne : e ≠ e0 := by rintro rfl; exact hnot he
      simp [wf, hne]
    have h0 : wf t (e0 :: L) y e0 = min (t e0) y := by
      simp [wf, wf_not_mem t L _ e0 hL.1]
    rw [hrest, wf_sum t L hL.2, h0]
    omega

lemma wf_full (t : E → ℕ) : ∀ (L : List E), L.Nodup → ∀ y, (∑ e ∈ L.toFinset, t e) ≤ y →
    ∀ e ∈ L, wf t L y e = t e
  | [], _, _, _, e, he => by simp at he
  | e0 :: L, hL, y, hy, e, he => by
    rw [List.nodup_cons] at hL
    have hnot : e0 ∉ L.toFinset := by simpa using hL.1
    rw [List.toFinset_cons, sum_insert hnot] at hy
    by_cases hee : e = e0
    · subst hee
      have h0 : wf t (e :: L) y e = min (t e) y := by
        simp [wf, wf_not_mem t L _ e hL.1]
      rw [h0]; omega
    · have heL : e ∈ L := by simpa [hee] using he
      have h0 : wf t (e0 :: L) y e = wf t L (y - min (t e0) y) e := by
        simp [wf, hee]
      rw [h0]
      exact wf_full t L hL.2 _ (by omega) e heL

end WaterFill

lemma map_head_aux {α β : Type*} (h t : α → β) : ∀ (c : α) (l : List α),
    (c :: l).IsChain (fun p q => h p = t q) →
      (c :: l).map h = l.map t ++ [h ((c :: l).getLast (List.cons_ne_nil _ _))]
  | c, [], _ => by simp
  | c, d :: l, hch => by
    have h1 := List.isChain_cons_cons.1 hch
    rw [List.map_cons, map_head_aux h t d l h1.2, h1.1]
    simp

lemma sum_count_inl_le {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]
    (C : List (ExtEdge V E)) : ∑ e, C.count (Sum.inl e) ≤ C.length := by
  induction C with
  | nil => simp
  | cons p C ih =>
    have h1 : ∀ e : E, (p :: C).count (Sum.inl e) =
        C.count (Sum.inl e) + (if p = Sum.inl e then 1 else 0) := by
      intro e
      by_cases h : p = Sum.inl e
      · subst h; simp
      · rw [List.count_cons_of_ne h, if_neg h, add_zero]
    simp only [h1, sum_add_distrib, List.length_cons]
    have : ∑ e : E, (if p = Sum.inl e then 1 else 0) ≤ 1 := by
      rcases p with e0 | w
      · simp
      · simp
    omega

namespace Game

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] (G : Game V E)

lemma mem_out {v : V} {e : E} : e ∈ G.outEdges v ↔ G.tail e = v := by simp [Game.outEdges]

lemma mem_in {v : V} {e : E} : e ∈ G.inEdges v ↔ G.head e = v := by simp [Game.inEdges]

lemma supply_mono {f g : E → ℕ} (h : ∀ e, f e ≤ g e) (v : V) : G.supply f v ≤ G.supply g v := by
  unfold Game.supply
  exact Nat.add_le_add_left (sum_le_sum fun e _ => h e) _

lemma exists_feasible_ge (a : FlowAllocGames.StrongEq.Profile E)
    (hcap : ∀ e y, a e y ≤ G.c e) (hmono : ∀ e, Monotone (a e)) :
    ∀ n (p : E → ℕ), (∑ e, G.c e) - (∑ e, p e) = n →
      (∀ e, p e ≤ a e (G.supply p (G.tail e))) → ∃ f, G.IsFeasible a f ∧ ∀ e, p e ≤ f e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp
  by_cases hfix : ∀ e, a e (G.supply p (G.tail e)) = p e
  · exact ⟨p, fun e => (hfix e).symm, fun e => le_rfl⟩
  · push_neg at hfix
    obtain ⟨e0, he0⟩ := hfix
    obtain ⟨q, hq⟩ : ∃ q : E → ℕ, ∀ e, q e = a e (G.supply p (G.tail e)) := ⟨_, fun e => rfl⟩
    have hpq : ∀ e, p e ≤ q e := fun e => by rw [hq e]; exact hp e
    have hqc : ∀ e, q e ≤ G.c e := fun e => by rw [hq e]; exact hcap _ _
    have hq2 : ∀ e, q e ≤ a e (G.supply q (G.tail e)) := fun e => by
      rw [hq e]; exact hmono e (G.supply_mono hpq _)
    have hlt : ∑ e, p e < ∑ e, q e := by
      apply Finset.sum_lt_sum (fun e _ => hpq e)
      refine ⟨e0, mem_univ _, lt_of_le_of_ne (hpq e0) ?_⟩
      rw [hq e0]; exact Ne.symm he0
    have hle : ∑ e, q e ≤ ∑ e, G.c e := sum_le_sum fun e _ => hqc e
    obtain ⟨f, hf, hqf⟩ := ih _ (by omega) q rfl hq2
    exact ⟨f, hf, fun e => (hpq e).trans (hqf e)⟩

lemma feasible_le_clearing (a : FlowAllocGames.StrongEq.Profile E)
    (hcap : ∀ e y, a e y ≤ G.c e) {f : E → ℕ} (hf : G.IsFeasible a f) (e : E) :
    f e ≤ G.clearingState a e := by
  show f e ≤ sSup ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f})
  apply le_csSup
  · refine ⟨G.c e, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    have hg' : G.IsFeasible a g := hg
    show g e ≤ G.c e
    rw [hg' e]; exact hcap _ _
  · exact ⟨f, hf, rfl⟩

lemma clearing_feasible (a : FlowAllocGames.StrongEq.Profile E)
    (hcap : ∀ e y, a e y ≤ G.c e) (hmono : ∀ e, Monotone (a e)) :
    G.IsFeasible a (G.clearingState a) := by
  obtain ⟨f0, hf0, -⟩ :=
    G.exists_feasible_ge a hcap hmono _ (fun _ => 0) rfl (fun e => Nat.zero_le _)
  have hpost : ∀ e, G.clearingState a e ≤ a e (G.supply (G.clearingState a) (G.tail e)) := by
    intro e
    show sSup ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f}) ≤ _
    refine csSup_le ⟨f0 e, f0, hf0, rfl⟩ ?_
    rintro _ ⟨g, hg, rfl⟩
    have hg' : G.IsFeasible a g := hg
    show g e ≤ _
    rw [hg' e]
    exact hmono e (G.supply_mono (fun e' => G.feasible_le_clearing a hcap hg' e') _)
  obtain ⟨f, hf, hle⟩ := G.exists_feasible_ge a hcap hmono _ _ rfl hpost
  have heq : f = G.clearingState a :=
    funext fun e => le_antisymm (G.feasible_le_clearing a hcap hf e) (hle e)
  rw [← heq]; exact hf

lemma post_le_clearing (a : FlowAllocGames.StrongEq.Profile E)
    (hcap : ∀ e y, a e y ≤ G.c e) (hmono : ∀ e, Monotone (a e)) (p : E → ℕ)
    (hp : ∀ e, p e ≤ a e (G.supply p (G.tail e))) (e : E) :
    p e ≤ G.clearingState a e := by
  obtain ⟨f, hf, hpf⟩ := G.exists_feasible_ge a hcap hmono _ p rfl hp
  exact (hpf e).trans (G.feasible_le_clearing a hcap hf e)

lemma utility_eq (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsUnitRanking a) (v : V) :
    G.utility a v = min (G.cplus v) (G.supply (G.clearingState a) v) := by
  have hf := G.clearing_feasible a ha.1 ha.2.2.2
  unfold Game.utility
  rw [← ha.2.2.1 v]
  apply sum_congr rfl
  intro e he
  rw [hf e, G.mem_out.1 he]

lemma flow_le_sum_g (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (a' : FlowAllocGames.StrongEq.Profile E) (ha' : G.IsUnitRanking a') :
    G.flow a' ≤ ∑ e, x.g e := by
  have hf : G.IsFeasible a' (G.clearingState a') := G.clearing_feasible a' ha'.1 ha'.2.2.2
  have hout : ∀ v, ∑ e ∈ G.outEdges v, G.clearingState a' e ≤ G.supply (G.clearingState a') v := by
    intro v
    calc ∑ e ∈ G.outEdges v, G.clearingState a' e
        = ∑ e ∈ G.outEdges v, a' e (G.supply (G.clearingState a') v) := by
          apply sum_congr rfl; intro e he
          rw [hf e, G.mem_out.1 he]
      _ ≤ G.supply (G.clearingState a') v := ha'.2.1 v _
  let y : ExtFlow V E := ⟨G.clearingState a',
    fun v => G.supply (G.clearingState a') v - ∑ e ∈ G.outEdges v, G.clearingState a' e, G.b⟩
  have hin : ∑ v, ∑ e ∈ G.inEdges v, G.clearingState a' e = ∑ e, G.clearingState a' e :=
    Finset.sum_fiberwise univ G.head (G.clearingState a')
  have hout' : ∑ v, ∑ e ∈ G.outEdges v, G.clearingState a' e = ∑ e, G.clearingState a' e :=
    Finset.sum_fiberwise univ G.tail (G.clearingState a')
  have hsupply : ∑ v, G.supply (G.clearingState a') v =
      ∑ v, G.b v + ∑ e, G.clearingState a' e := by
    unfold Game.supply; rw [sum_add_distrib, hin]
  have htoS : ∑ v, y.toS v = ∑ v, G.b v := by
    show ∑ v, (G.supply (G.clearingState a') v - ∑ e ∈ G.outEdges v, G.clearingState a' e) = _
    rw [sum_tsub_distrib _ (fun v _ => hout v), hsupply, hout']
    omega
  have hy : G.IsCirculation y := by
    refine ⟨fun e => ?_, fun v => le_rfl, fun v => ?_, ?_⟩
    · show G.clearingState a' e ≤ G.c e
      rw [hf e]; exact ha'.1 _ _
    · show G.b v + ∑ e ∈ G.inEdges v, G.clearingState a' e =
        ∑ e ∈ G.outEdges v, G.clearingState a' e +
          (G.supply (G.clearingState a') v - ∑ e ∈ G.outEdges v, G.clearingState a' e)
      have := hout v
      unfold Game.supply at this ⊢
      omega
    · exact htoS
  have htot := hx.2 y hy
  obtain ⟨⟨-, hxb, -, hxs⟩, -⟩ := hx
  have hxb' : ∑ v, x.fromS v ≤ ∑ v, G.b v := sum_le_sum fun v _ => hxb v
  unfold ExtFlow.total at htot
  have e1 : ∑ e, y.g e = ∑ e, G.clearingState a' e := rfl
  have e2 : ∑ v, y.fromS v = ∑ v, G.b v := rfl
  have e3 : G.flow a' = ∑ e, G.clearingState a' e := rfl
  omega

lemma card_mem_le (x : ExtFlow V E) (Cs : List (List (ExtEdge V E)))
    (hCs : G.IsUnitCycleDecomposition x Cs) (q : ExtEdge V E) :
    (univ.filter (fun i : Fin Cs.length => q ∈ Cs[i.1])).card ≤ x.val q := by
  rw [hCs.2 q, ← Fin.sum_univ_fun_getElem Cs (fun C => C.count q), card_eq_sum_ones, sum_filter]
  exact sum_le_sum fun i _ => by
    split_ifs with h
    · exact List.count_pos_iff.2 h
    · exact Nat.zero_le _

lemma walk (g : E → ℕ) (hg : ∀ e, g e ≤ G.c e) : ∀ (L : List (ExtEdge V E)),
    L.IsChain (fun p q => G.extHead p = G.extTail q) →
    ∀ (k : ℕ) (hk : k < L.length), (∃ e, L[k] = Sum.inl e) →
    (∃ p ∈ L, ∃ e', Sum.inl e' ∈ L ∧ (p = Sum.inr (Sum.inr (G.tail e')) ∨
        ∃ e, p = Sum.inl e ∧ g e = G.c e ∧ G.head e = G.tail e')) ∨
    (∀ (j : ℕ) (hj : j < k), ∃ e, L[j]'(by omega) = Sum.inl e ∧ g e < G.c e) := by
  intro L
  induction L with
  | nil => intro _ k hk; simp at hk
  | cons p L ih =>
    intro hch k hk hkE
    cases k with
    | zero => right; intro j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ k =>
      have hk' : k < L.length := by simpa using hk
      have hkE' : ∃ e, L[k] = Sum.inl e := by simpa using hkE
      rcases ih hch.tail k hk' hkE' with ⟨p', hp', e', he', hgood⟩ | hall
      · left
        exact ⟨p', List.mem_cons_of_mem _ hp', e', List.mem_cons_of_mem _ he', hgood⟩
      · rcases L with _ | ⟨q, L'⟩
        · simp at hk'
        · have hq : ∃ e', q = Sum.inl e' := by
            rcases Nat.eq_zero_or_pos k with h0 | h0
            · subst h0; simpa using hkE'
            · obtain ⟨e, he, -⟩ := hall 0 h0; exact ⟨e, by simpa using he⟩
          obtain ⟨e', rfl⟩ := hq
          have hrel : G.extHead p = G.extTail (Sum.inl e') := (List.isChain_cons_cons.1 hch).1
          rcases p with e | w | w
          · by_cases hge : g e < G.c e
            · right
              intro j hj
              cases j with
              | zero => exact ⟨e, rfl, hge⟩
              | succ j => simpa using hall j (by omega)
            · left
              refine ⟨Sum.inl e, by simp, e', by simp,
                Or.inr ⟨e, rfl, le_antisymm (hg e) (not_lt.1 hge), ?_⟩⟩
              simpa [Game.extHead, Game.extTail] using hrel
          · simp [Game.extHead, Game.extTail] at hrel
          · left
            refine ⟨Sum.inr (Sum.inr w), by simp, e', by simp, Or.inl ?_⟩
            simp [Game.extHead, Game.extTail] at hrel
            rw [hrel]

lemma map_head_perm (C : List (ExtEdge V E))
    (hch : C.IsChain (fun p q => G.extHead p = G.extTail q))
    (hcl : ∀ h : C ≠ [], G.extHead (C.getLast h) = G.extTail (C.head h)) :
    (C.map G.extHead).Perm (C.map G.extTail) := by
  rcases C with _ | ⟨c, l⟩
  · simp
  · rw [map_head_aux _ _ c l hch, hcl (List.cons_ne_nil _ _)]
    simp only [List.head_cons, List.map_cons]
    exact List.perm_append_singleton _ _

/-- Deviation strategy: water-fill to the target `p` at supply `supply p v`, then fill the
remaining capacity. -/
noncomputable def devProfile (p : E → ℕ) : FlowAllocGames.StrongEq.Profile E := fun e y =>
  wf p (G.outEdges (G.tail e)).toList y e +
    wf (fun e => G.c e - p e) (G.outEdges (G.tail e)).toList (y - G.supply p (G.tail e)) e

lemma dev_cap (p : E → ℕ) (hpc : ∀ e, p e ≤ G.c e) (e : E) (y : ℕ) :
    G.devProfile p e y ≤ G.c e := by
  unfold devProfile
  have h1 := wf_le p (G.outEdges (G.tail e)).toList (Finset.nodup_toList _) y e
  have h2 := wf_le (fun e => G.c e - p e) (G.outEdges (G.tail e)).toList (Finset.nodup_toList _)
    (y - G.supply p (G.tail e)) e
  have := hpc e
  omega

lemma dev_mono (p : E → ℕ) (e : E) : Monotone (G.devProfile p e) := by
  intro y1 y2 h
  unfold devProfile
  exact add_le_add (wf_mono p _ e h) (wf_mono _ _ e (Nat.sub_le_sub_right h _))

lemma dev_sum (p : E → ℕ) (hpc : ∀ e, p e ≤ G.c e) (v : V)
    (hv : ∑ e ∈ G.outEdges v, p e = G.supply p v) (y : ℕ) :
    ∑ e ∈ G.outEdges v, G.devProfile p e y = min (G.cplus v) y := by
  have h1 : ∀ e ∈ G.outEdges v, G.devProfile p e y =
      wf p (G.outEdges v).toList y e +
        wf (fun e => G.c e - p e) (G.outEdges v).toList (y - G.supply p v) e := by
    intro e he
    have : G.tail e = v := G.mem_out.1 he
    simp only [devProfile, this]
  rw [sum_congr rfl h1, sum_add_distrib]
  have hs1 := wf_sum p (G.outEdges v).toList (Finset.nodup_toList _) y
  have hs2 := wf_sum (fun e => G.c e - p e) (G.outEdges v).toList (Finset.nodup_toList _)
    (y - G.supply p v)
  rw [Finset.toList_toFinset] at hs1 hs2
  rw [hs1, hs2, sum_tsub_distrib _ (fun e _ => hpc e)]
  have hle : ∑ e ∈ G.outEdges v, p e ≤ G.cplus v := sum_le_sum fun e _ => hpc e
  unfold Game.cplus at hle ⊢
  rw [hv] at hle ⊢
  omega

lemma dev_at (p : E → ℕ) (e : E)
    (hv : ∑ e' ∈ G.outEdges (G.tail e), p e' = G.supply p (G.tail e)) :
    G.devProfile p e (G.supply p (G.tail e)) = p e := by
  unfold devProfile
  rw [Nat.sub_self, wf_zero, add_zero]
  exact wf_full p _ (Finset.nodup_toList _) _
    (le_of_eq (by rw [Finset.toList_toFinset, hv])) e (by rw [Finset.mem_toList, G.mem_out])

lemma no_open_cycle (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a)
    (C : List (ExtEdge V E)) (hC : G.IsExtCycle C)
    (hall : ∀ q ∈ C, ∃ e, q = Sum.inl e ∧ G.clearingState a e < G.c e) : False := by
  classical
  obtain ⟨hur, hse⟩ := ha
  have hgf : G.IsFeasible a (G.clearingState a) := G.clearing_feasible a hur.1 hur.2.2.2
  have hgc : ∀ e, G.clearingState a e ≤ G.c e := fun e => by rw [hgf e]; exact hur.1 _ _
  obtain ⟨hne, hch, hcl, hnd⟩ := hC
  have hperm := G.map_head_perm C hch hcl
  have hndH : (C.map G.extHead).Nodup := hperm.nodup_iff.2 hnd
  obtain ⟨T, hT⟩ : ∃ T : Finset V, ∀ v, v ∈ T ↔ ∃ e, Sum.inl e ∈ C ∧ G.tail e = v :=
    ⟨univ.filter (fun v => ∃ e, Sum.inl e ∈ C ∧ G.tail e = v), fun v => by simp⟩
  obtain ⟨p, hp⟩ : ∃ p : E → ℕ, ∀ e,
      p e = G.clearingState a e + if Sum.inl e ∈ C then 1 else 0 := ⟨_, fun e => rfl⟩
  have hpc : ∀ e, p e ≤ G.c e := by
    intro e; rw [hp e]
    split_ifs with h
    · obtain ⟨e', he', hlt⟩ := hall _ h
      rw [Sum.inl.injEq] at he'
      subst he'
      omega
    · simpa using hgc e
  have hout1 : ∀ v ∈ T, ∑ e ∈ G.outEdges v, (if Sum.inl e ∈ C then 1 else 0) = 1 := by
    intro v hv
    obtain ⟨e0, he0, rfl⟩ := (hT v).1 hv
    simp only [sum_boole, Nat.cast_id]
    rw [card_eq_one]
    refine ⟨e0, ?_⟩
    ext e
    simp only [mem_filter, mem_singleton, G.mem_out]
    constructor
    · rintro ⟨ht, he⟩
      have := List.inj_on_of_nodup_map hnd he he0 (by simp [Game.extTail, ht])
      simpa using this
    · rintro rfl; exact ⟨rfl, he0⟩
  have hin1 : ∀ v ∈ T, ∑ e ∈ G.inEdges v, (if Sum.inl e ∈ C then 1 else 0) = 1 := by
    intro v hv
    obtain ⟨e0, he0, rfl⟩ := (hT v).1 hv
    have hmem : some (G.tail e0) ∈ C.map G.extHead := by
      rw [hperm.mem_iff]; exact List.mem_map.2 ⟨_, he0, rfl⟩
    obtain ⟨q, hq, hqh⟩ := List.mem_map.1 hmem
    obtain ⟨e1, rfl, -⟩ := hall q hq
    have he1 : G.head e1 = G.tail e0 := by simpa [Game.extHead] using hqh
    simp only [sum_boole, Nat.cast_id]
    rw [card_eq_one]
    refine ⟨e1, ?_⟩
    ext e
    simp only [mem_filter, mem_singleton, G.mem_in]
    constructor
    · rintro ⟨ht, he⟩
      have := List.inj_on_of_nodup_map hndH he hq (by simp [Game.extHead, ht, he1])
      simpa using this
    · rintro rfl; exact ⟨he1, hq⟩
  have hTsub : ∀ e, Sum.inl e ∈ C → G.tail e ∈ T := fun e he => (hT _).2 ⟨e, he, rfl⟩
  have hopen : ∀ v ∈ T, ∑ e ∈ G.outEdges v, G.clearingState a e =
      G.supply (G.clearingState a) v := by
    intro v hv
    obtain ⟨e0, he0, rfl⟩ := (hT v).1 hv
    have hu := G.utility_eq a hur (G.tail e0)
    have hlt : ∑ e ∈ G.outEdges (G.tail e0), G.clearingState a e < G.cplus (G.tail e0) := by
      unfold Game.cplus
      apply sum_lt_sum (fun e _ => hgc e)
      obtain ⟨e', he', hlt⟩ := hall _ he0
      rw [Sum.inl.injEq] at he'
      subst he'
      exact ⟨e0, G.mem_out.2 rfl, hlt⟩
    unfold Game.utility at hu
    omega
  have hpout : ∀ v, ∑ e ∈ G.outEdges v, p e = ∑ e ∈ G.outEdges v, G.clearingState a e +
      ∑ e ∈ G.outEdges v, (if Sum.inl e ∈ C then 1 else 0) := by
    intro v
    rw [← sum_add_distrib]; exact sum_congr rfl fun e _ => hp e
  have hpsum : ∀ v ∈ T, ∑ e ∈ G.outEdges v, p e = G.supply p v := by
    intro v hv
    have h2 : G.supply p v = G.supply (G.clearingState a) v +
        ∑ e ∈ G.inEdges v, (if Sum.inl e ∈ C then 1 else 0) := by
      unfold Game.supply
      rw [add_assoc, ← sum_add_distrib]
      congr 1
      exact sum_congr rfl fun e _ => hp e
    rw [hpout v, h2, hout1 v hv, hin1 v hv, hopen v hv]
  have hgp : ∀ e, G.clearingState a e ≤ p e := fun e => by rw [hp e]; omega
  have hDe : ∀ e, G.deviate a (G.devProfile p) T e =
      if G.tail e ∈ T then G.devProfile p e else a e := fun e => rfl
  have hDur : G.IsUnitRanking (G.deviate a (G.devProfile p) T) := by
    have hex : ∀ v y, ∑ e ∈ G.outEdges v, G.deviate a (G.devProfile p) T e y =
        min (G.cplus v) y := by
      intro v y
      by_cases hv : v ∈ T
      · rw [← G.dev_sum p hpc v (hpsum v hv) y]
        apply sum_congr rfl; intro e he
        rw [hDe, if_pos (by rw [G.mem_out.1 he]; exact hv)]
      · rw [← hur.2.2.1 v y]
        apply sum_congr rfl; intro e he
        rw [hDe, if_neg (by rw [G.mem_out.1 he]; exact hv)]
    refine ⟨fun e y => ?_, fun v y => (hex v y).le.trans (min_le_right _ _), hex, fun e => ?_⟩
    · rw [hDe]; split_ifs
      · exact G.dev_cap p hpc e y
      · exact hur.1 e y
    · rw [hDe]; split_ifs
      · exact G.dev_mono p e
      · exact hur.2.2.2 e
  have hpost : ∀ e, p e ≤ G.deviate a (G.devProfile p) T e (G.supply p (G.tail e)) := by
    intro e
    rw [hDe]
    split_ifs with h
    · exact (G.dev_at p e (hpsum _ h)).ge
    · have hnot : Sum.inl e ∉ C := fun he => h (hTsub e he)
      rw [hp e, if_neg hnot, add_zero, hgf e]
      exact hur.2.2.2 e (G.supply_mono hgp _)
  have hle : ∀ e, p e ≤ G.clearingState (G.deviate a (G.devProfile p) T) e :=
    G.post_le_clearing _ hDur.1 hDur.2.2.2 p hpost
  obtain ⟨q0, hq0⟩ := List.exists_mem_of_ne_nil C hne
  obtain ⟨e0, rfl, -⟩ := hall q0 hq0
  apply hse T (G.devProfile p) ⟨_, hTsub e0 hq0⟩ hDur
  intro v hv
  unfold Game.utility
  calc ∑ e ∈ G.outEdges v, G.clearingState a e
      < ∑ e ∈ G.outEdges v, G.clearingState a e + 1 := Nat.lt_succ_self _
    _ = ∑ e ∈ G.outEdges v, p e := by rw [hpout v, hout1 v hv]
    _ ≤ _ := sum_le_sum fun e _ => hle e

/-- Where a cycle of the decomposition is charged. -/
def Chg (a : FlowAllocGames.StrongEq.Profile E) (C : List (ExtEdge V E)) (v : V) : Prop :=
  (¬ G.utility a v < G.cplus v ∧ ∃ e ∈ G.outEdges v, Sum.inl e ∈ C) ∨
  (G.utility a v < G.cplus v ∧ (Sum.inr (Sum.inr v) ∈ C ∨
      ∃ e ∈ G.inEdges v, G.clearingState a e = G.c e ∧ Sum.inl e ∈ C))

lemma cycle_charge (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a)
    (C : List (ExtEdge V E)) (hC : G.IsExtCycle C) (hE : ∃ e, Sum.inl e ∈ C) :
    ∃ v, G.Chg a C v := by
  classical
  have hur := ha.1
  have hgf := G.clearing_feasible a hur.1 hur.2.2.2
  have hgc : ∀ e, G.clearingState a e ≤ G.c e := fun e => by rw [hgf e]; exact hur.1 _ _
  by_cases hcl : ∃ e, Sum.inl e ∈ C ∧ ¬ G.utility a (G.tail e) < G.cplus (G.tail e)
  · obtain ⟨e, he, hc⟩ := hcl
    exact ⟨G.tail e, Or.inl ⟨hc, e, G.mem_out.2 rfl, he⟩⟩
  · push_neg at hcl
    obtain ⟨e0, he0⟩ := hE
    obtain ⟨j0, hj0, hj0e⟩ := List.getElem_of_mem he0
    have hchain : (C ++ C).IsChain (fun p q => G.extHead p = G.extTail q) := by
      refine List.IsChain.append hC.2.1 hC.2.1 ?_
      intro p hp q hq
      simp only [List.getLast?_eq_some_getLast hC.1, List.head?_eq_some_head hC.1, Option.mem_def,
        Option.some.injEq] at hp hq
      subst hp; subst hq
      exact hC.2.2.1 hC.1
    have hidx : C.length + j0 < (C ++ C).length := by simp; omega
    have hE' : ∃ e, (C ++ C)[C.length + j0] = Sum.inl e := by
      refine ⟨e0, ?_⟩
      rw [List.getElem_append_right (by omega)]
      simpa using hj0e
    rcases G.walk (G.clearingState a) hgc (C ++ C) hchain (C.length + j0) hidx hE' with
      ⟨p, hp, e', he', hgood⟩ | hall
    · have hp' : p ∈ C := by simpa using hp
      have he'' : Sum.inl e' ∈ C := by simpa using he'
      refine ⟨G.tail e', Or.inr ⟨hcl e' he'', ?_⟩⟩
      rcases hgood with rfl | ⟨e, rfl, hs, hh⟩
      · exact Or.inl hp'
      · exact Or.inr ⟨e, G.mem_in.2 hh, hs, hp'⟩
    · exfalso
      apply G.no_open_cycle a ha C hC
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hq
      obtain ⟨e, he, hlt⟩ := hall j (by omega)
      refine ⟨e, ?_, hlt⟩
      rwa [List.getElem_append_left hj] at he

lemma charging (x : ExtFlow V E) (hxc : G.IsCirculation x) (Cs : List (List (ExtEdge V E)))
    (hCs : G.IsUnitCycleDecomposition x Cs) (a : FlowAllocGames.StrongEq.Profile E)
    (ha : G.IsStrongEquilibrium a) :
    (univ.filter (fun i : Fin Cs.length => ∃ e, Sum.inl e ∈ Cs[i.1])).card ≤ G.flow a := by
  classical
  have hur := ha.1
  have hcount : ∀ v, (univ.filter (fun i : Fin Cs.length => G.Chg a Cs[i.1] v)).card ≤
      G.utility a v := by
    intro v
    by_cases hv : G.utility a v < G.cplus v
    · calc (univ.filter (fun i : Fin Cs.length => G.Chg a Cs[i.1] v)).card
          ≤ (univ.filter (fun i : Fin Cs.length => Sum.inr (Sum.inr v) ∈ Cs[i.1]) ∪
              (G.inEdges v).biUnion (fun e => univ.filter (fun i : Fin Cs.length =>
                G.clearingState a e = G.c e ∧ Sum.inl e ∈ Cs[i.1]))).card := by
            apply card_le_card
            intro i hi
            have h' : G.Chg a Cs[i.1] v := (mem_filter.1 hi).2
            unfold Game.Chg at h'
            rcases h' with ⟨h, -⟩ | ⟨-, h | ⟨e, he, h⟩⟩
            · exact absurd hv h
            · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, h⟩)
            · exact mem_union_right _ (mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨mem_univ _, h⟩⟩)
        _ ≤ (univ.filter (fun i : Fin Cs.length => Sum.inr (Sum.inr v) ∈ Cs[i.1])).card +
              ((G.inEdges v).biUnion (fun e => univ.filter (fun i : Fin Cs.length =>
                G.clearingState a e = G.c e ∧ Sum.inl e ∈ Cs[i.1]))).card := card_union_le _ _
        _ ≤ G.b v + ∑ e ∈ G.inEdges v, G.clearingState a e := by
            apply add_le_add
            · exact (G.card_mem_le x Cs hCs _).trans (hxc.2.1 v)
            · refine card_biUnion_le.trans (sum_le_sum fun e _ => ?_)
              by_cases hs : G.clearingState a e = G.c e
              · calc _ ≤ (univ.filter (fun i : Fin Cs.length => Sum.inl e ∈ Cs[i.1])).card := by
                      apply card_le_card; intro i hi
                      exact mem_filter.2 ⟨mem_univ _, (mem_filter.1 hi).2.2⟩
                  _ ≤ x.val (Sum.inl e) := G.card_mem_le x Cs hCs _
                  _ ≤ G.c e := hxc.1 e
                  _ = _ := hs.symm
              · simp [hs]
        _ = G.utility a v := by
            have hu := G.utility_eq a hur v
            unfold Game.supply at hu
            omega
    · calc (univ.filter (fun i : Fin Cs.length => G.Chg a Cs[i.1] v)).card
          ≤ ((G.outEdges v).biUnion (fun e =>
              univ.filter (fun i : Fin Cs.length => Sum.inl e ∈ Cs[i.1]))).card := by
            apply card_le_card
            intro i hi
            have h' : G.Chg a Cs[i.1] v := (mem_filter.1 hi).2
            unfold Game.Chg at h'
            rcases h' with ⟨-, e, he, h⟩ | ⟨h, -⟩
            · exact mem_biUnion.2 ⟨e, he, mem_filter.2 ⟨mem_univ _, h⟩⟩
            · exact absurd h hv
        _ ≤ ∑ e ∈ G.outEdges v,
              (univ.filter (fun i : Fin Cs.length => Sum.inl e ∈ Cs[i.1])).card := card_biUnion_le
        _ ≤ ∑ e ∈ G.outEdges v, G.c e :=
            sum_le_sum fun e _ => (G.card_mem_le x Cs hCs _).trans (hxc.1 e)
        _ = G.cplus v := rfl
        _ ≤ G.utility a v := not_lt.1 hv
  have hflow : ∑ v, G.utility a v = G.flow a :=
    Finset.sum_fiberwise univ G.tail (G.clearingState a)
  calc (univ.filter (fun i : Fin Cs.length => ∃ e, Sum.inl e ∈ Cs[i.1])).card
      ≤ (univ.biUnion (fun v => univ.filter (fun i : Fin Cs.length => G.Chg a Cs[i.1] v))).card := by
        apply card_le_card
        intro i hi
        obtain ⟨v, hv⟩ := G.cycle_charge a ha _ (hCs.1 _ (List.getElem_mem _)) (mem_filter.1 hi).2
        exact mem_biUnion.2 ⟨v, mem_univ _, mem_filter.2 ⟨mem_univ _, hv⟩⟩
    _ ≤ ∑ v, (univ.filter (fun i : Fin Cs.length => G.Chg a Cs[i.1] v)).card := card_biUnion_le
    _ ≤ ∑ v, G.utility a v := sum_le_sum fun v _ => hcount v
    _ = G.flow a := hflow

theorem main_bound (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (Cs : List (List (ExtEdge V E))) (hCs : G.IsUnitCycleDecomposition x Cs)
    (d : ℕ) (hd : ∀ C ∈ Cs, C.length ≤ d)
    (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a)
    (a' : FlowAllocGames.StrongEq.Profile E) (ha' : G.IsUnitRanking a') :
    G.flow a' ≤ d * G.flow a := by
  have h1 := G.flow_le_sum_g x hx a' ha'
  have hsum : ∑ e, x.g e = ∑ i : Fin Cs.length, ∑ e, Cs[i.1].count (Sum.inl e) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    have h : x.g e = (Cs.map (fun C => C.count (Sum.inl e))).sum := hCs.2 (Sum.inl e)
    rw [h]
    exact (Fin.sum_univ_fun_getElem Cs (fun C => C.count (Sum.inl e))).symm
  have h3 : ∀ i : Fin Cs.length, ∑ e, Cs[i.1].count (Sum.inl e) ≤
      if (∃ e, Sum.inl e ∈ Cs[i.1]) then d else 0 := by
    intro i
    split_ifs with hE
    · exact (sum_count_inl_le _).trans (hd _ (List.getElem_mem _))
    · push_neg at hE
      have : ∀ e, Cs[i.1].count (Sum.inl e) = 0 := fun e => List.count_eq_zero_of_not_mem (hE e)
      simp [this]
  have h4 := G.charging x hx.1 Cs hCs a ha
  calc G.flow a' ≤ ∑ e, x.g e := h1
    _ = ∑ i : Fin Cs.length, ∑ e, Cs[i.1].count (Sum.inl e) := hsum
    _ ≤ ∑ i : Fin Cs.length, (if (∃ e, Sum.inl e ∈ Cs[i.1]) then d else 0) :=
        sum_le_sum fun i _ => h3 i
    _ = (univ.filter (fun i : Fin Cs.length => ∃ e, Sum.inl e ∈ Cs[i.1])).card * d := by
        rw [← sum_filter, sum_const, smul_eq_mul]
    _ ≤ G.flow a * d := Nat.mul_le_mul_right _ h4
    _ = d * G.flow a := mul_comm _ _

end Game

end FlowAllocGames.StrongPoA

open FlowAllocGames.StrongPoA FlowAllocGames.StrongPoA.Game in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x)
    (Cs : List (List (ExtEdge V E))) (hCs : G.IsUnitCycleDecomposition x Cs)
    (d : ℕ) (hd : ∀ C ∈ Cs, C.length ≤ d)
    (a : FlowAllocGames.StrongEq.Profile E) (ha : G.IsStrongEquilibrium a) (a' : FlowAllocGames.StrongEq.Profile E) (ha' : G.IsUnitRanking a') :
    G.flow a' ≤ d * G.flow a := by
  exact G.main_bound x hx Cs hCs d hd a ha a' ha'
