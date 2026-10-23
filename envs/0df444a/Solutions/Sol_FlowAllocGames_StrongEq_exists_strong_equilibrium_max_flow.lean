-- Prove2me | solution 1 for FlowAllocGames.StrongEq.exists_strong_equilibrium_max_flow
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-22T18:04:44.691006+00:00
-- url     : https://prove2.me/submissions/48bdaea0-eb69-4ad2-9f3b-13be5718aa69

import Definitions.Def_FlowAllocGames_StrongEq_Model
namespace FlowAllocGames.StrongEq

open Finset

/-- Generic allocation: for any finite set of edges with weights `w` there is a monotone
allocation filling the weights greedily. -/
lemma flowalloc_alloc {E : Type*} [DecidableEq E] (s : Finset E) (w : E → ℕ) :
    ∃ A : E → ℕ → ℕ, (∀ e y, A e y ≤ w e) ∧ (∀ e, Monotone (A e)) ∧
      ∀ y, ∑ e ∈ s, A e y = min (∑ e ∈ s, w e) y := by
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨fun _ _ => 0, fun _ _ => Nat.zero_le _, fun _ => monotone_const, fun y => by simp⟩
  | insert e0 s he0 ih =>
    obtain ⟨A, hA1, hA2, hA3⟩ := ih
    refine ⟨fun e y => if e = e0 then min (w e0) y else A e (y - w e0), ?_, ?_, ?_⟩
    · intro e y
      by_cases h : e = e0
      · subst h; simp
      · simp only [h, if_false]; exact hA1 e _
    · intro e
      by_cases h : e = e0
      · subst h
        intro x y hxy
        simp only [if_true]
        exact min_le_min_left _ hxy
      · intro x y hxy
        simp only [h, if_false]
        exact hA2 e (Nat.sub_le_sub_right hxy _)
    · intro y
      rw [sum_insert he0, sum_insert he0]
      beta_reduce
      rw [if_pos rfl]
      rw [sum_congr rfl (fun e he => if_neg (show e ≠ e0 from fun h => he0 (h ▸ he)))]
      rw [hA3]
      omega

lemma flowalloc_cycle {V E : Type*} [DecidableEq V] (tail head : E → V) (D : E → Prop) :
    ∀ (n : ℕ) (U : Finset V), U.card = n → U.Nonempty →
      (∀ v ∈ U, ∃ e, D e ∧ head e = v ∧ tail e ∈ U) →
      ∃ T : Finset V, T.Nonempty ∧ ∃ p : V → E,
        (∀ t ∈ T, D (p t) ∧ head (p t) = t ∧ tail (p t) ∈ T) ∧
        Set.InjOn (fun t => tail (p t)) T := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro U hU hne hcl
  obtain ⟨v0, hv0⟩ := hne
  obtain ⟨e0, -⟩ := hcl v0 hv0
  classical
  let p : V → E := fun v => if h : v ∈ U then Classical.choose (hcl v h) else e0
  have hp : ∀ v ∈ U, D (p v) ∧ head (p v) = v ∧ tail (p v) ∈ U := fun v hv => by
    simp only [p, dif_pos hv]; exact Classical.choose_spec (hcl v hv)
  by_cases hinj : Set.InjOn (fun t => tail (p t)) U
  · exact ⟨U, ⟨v0, hv0⟩, p, hp, hinj⟩
  · let U' := U.image (fun t => tail (p t))
    have hlt : U'.card < n := by
      rw [← hU]
      exact lt_of_le_of_ne card_image_le (fun h => hinj (card_image_iff.mp h))
    have hsub : U' ⊆ U := fun x hx => by
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hx
      exact (hp t ht).2.2
    apply ih _ hlt U' rfl ⟨_, mem_image_of_mem _ hv0⟩
    intro v hv
    exact ⟨p v, (hp v (hsub hv)).1, (hp v (hsub hv)).2.1, mem_image_of_mem _ (hsub hv)⟩

lemma flowalloc_count {V E : Type*} [DecidableEq E] (T : Finset V) (p : V → E) (S : Finset E) :
    ∑ e ∈ S, (T.filter (fun t => p t = e)).card = (T.filter (fun t => p t ∈ S)).card := by
  simp only [card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  simp [sum_ite_eq]

set_option linter.unusedSectionVars false

section
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] (G : Game V E)

/-- weak flows: capacity and weak conservation. -/
def flowalloc_WF (g : E → ℕ) : Prop :=
  (∀ e, g e ≤ G.c e) ∧ ∀ v, ∑ e ∈ G.outEdges v, g e ≤ G.supply g v

lemma flowalloc_mem_out {e : E} {v : V} : e ∈ G.outEdges v ↔ G.tail e = v := by
  simp [Game.outEdges]

lemma flowalloc_mem_in {e : E} {v : V} : e ∈ G.inEdges v ↔ G.head e = v := by
  simp [Game.inEdges]

lemma flowalloc_feas_le_c {a : Profile E} (ha : G.IsUnitRanking a) {f : E → ℕ}
    (hf : G.IsFeasible a f) (e : E) : f e ≤ G.c e := by
  rw [hf e]; exact ha.1 e _

lemma flowalloc_bdd {a : Profile E} (ha : G.IsUnitRanking a) (e : E) :
    BddAbove ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f}) :=
  ⟨G.c e, by rintro _ ⟨f, hf, rfl⟩; exact flowalloc_feas_le_c G ha hf e⟩

lemma flowalloc_cs_le_c {a : Profile E} (ha : G.IsUnitRanking a) (e : E) :
    G.clearingState a e ≤ G.c e := by
  unfold Game.clearingState
  exact csSup_le' (by rintro _ ⟨f, hf, rfl⟩; exact flowalloc_feas_le_c G ha hf e)

lemma flowalloc_le_cs {a : Profile E} (ha : G.IsUnitRanking a) {f : E → ℕ}
    (hf : G.IsFeasible a f) (e : E) : f e ≤ G.clearingState a e :=
  le_csSup (flowalloc_bdd G ha e) ⟨f, hf, rfl⟩

lemma flowalloc_supply_mono {f g : E → ℕ} (h : ∀ e, f e ≤ g e) (v : V) :
    G.supply f v ≤ G.supply g v := by
  unfold Game.supply
  exact Nat.add_le_add_left (sum_le_sum fun e _ => h e) _

lemma flowalloc_cs_post {a : Profile E} (ha : G.IsUnitRanking a) (e : E) :
    G.clearingState a e ≤ a e (G.supply (G.clearingState a) (G.tail e)) := by
  by_cases hne : ((fun f : E → ℕ => f e) '' {f | G.IsFeasible a f}).Nonempty
  · obtain ⟨f, hf, hfe⟩ := Nat.sSup_mem hne (flowalloc_bdd G ha e)
    have h1 : G.clearingState a e = f e := hfe.symm
    rw [h1, hf e]
    exact ha.2.2.2 e (flowalloc_supply_mono G (flowalloc_le_cs G ha hf) _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : G.clearingState a e = 0 := by
      unfold Game.clearingState; rw [hne]; simp
    rw [h1]; exact Nat.zero_le _

lemma flowalloc_cs_out_le {a : Profile E} (ha : G.IsUnitRanking a) (v : V) :
    ∑ e ∈ G.outEdges v, G.clearingState a e ≤
      min (G.cplus v) (G.supply (G.clearingState a) v) := by
  calc ∑ e ∈ G.outEdges v, G.clearingState a e
        ≤ ∑ e ∈ G.outEdges v, a e (G.supply (G.clearingState a) v) :=
          sum_le_sum fun e he => by
            have : G.tail e = v := (flowalloc_mem_out G).mp he
            rw [← this]; exact flowalloc_cs_post G ha e
    _ = _ := ha.2.2.1 v _

lemma flowalloc_cs_WF {a : Profile E} (ha : G.IsUnitRanking a) :
    flowalloc_WF G (G.clearingState a) :=
  ⟨flowalloc_cs_le_c G ha, fun v => (flowalloc_cs_out_le G ha v).trans (min_le_right _ _)⟩

lemma flowalloc_exists_opt :
    ∃ g, flowalloc_WF G g ∧ ∀ h, flowalloc_WF G h → ∑ e, h e ≤ ∑ e, g e := by
  let S : Set ℕ := {n | ∃ g, flowalloc_WF G g ∧ ∑ e, g e = n}
  have hb : BddAbove S :=
    ⟨∑ e, G.c e, by rintro _ ⟨g, hg, rfl⟩; exact sum_le_sum fun e _ => hg.1 e⟩
  have hne : S.Nonempty :=
    ⟨0, fun _ => 0, ⟨fun e => Nat.zero_le _, fun v => by simp⟩, by simp⟩
  obtain ⟨g, hg, hgs⟩ := Nat.sSup_mem hne hb
  exact ⟨g, hg, fun h hh => hgs ▸ le_csSup hb ⟨h, hh, rfl⟩⟩

lemma flowalloc_bump [DecidableEq E] (g : E → ℕ) (e0 : E) (s : Finset E) :
    ∑ e ∈ s, (g e + if e = e0 then 1 else 0) = ∑ e ∈ s, g e + if e0 ∈ s then 1 else 0 := by
  rw [sum_add_distrib, sum_ite_eq']

lemma flowalloc_sat {g : E → ℕ} (hg : flowalloc_WF G g)
    (hopt : ∀ h, flowalloc_WF G h → ∑ e, h e ≤ ∑ e, g e) (v : V) :
    ∑ e ∈ G.outEdges v, g e = min (G.cplus v) (G.supply g v) := by
  classical
  have h1 : ∑ e ∈ G.outEdges v, g e ≤ G.cplus v := sum_le_sum fun e _ => hg.1 e
  have h2 := hg.2 v
  by_contra hne
  have hlt1 : ∑ e ∈ G.outEdges v, g e < ∑ e ∈ G.outEdges v, G.c e := by
    unfold Game.cplus at h1 hne; omega
  have hlt2 : ∑ e ∈ G.outEdges v, g e < G.supply g v := by omega
  obtain ⟨e0, he0, hlt0⟩ := exists_lt_of_sum_lt hlt1
  have hte0 : G.tail e0 = v := (flowalloc_mem_out G).mp he0
  let h : E → ℕ := fun e => g e + if e = e0 then 1 else 0
  have hh : flowalloc_WF G h := by
    refine ⟨fun e => ?_, fun u => ?_⟩
    · by_cases he : e = e0
      · subst he; simp only [h, if_true]; omega
      · simp only [h, he, if_false]; have := hg.1 e; omega
    · have hs : G.supply h u = G.supply g u + if e0 ∈ G.inEdges u then 1 else 0 := by
        simp only [Game.supply, h]; rw [flowalloc_bump]; ring
      simp only [h]
      rw [hs, flowalloc_bump]
      have := hg.2 u
      by_cases hu : e0 ∈ G.outEdges u
      · have huv : u = v := ((flowalloc_mem_out G).mp hu).symm.trans hte0
        subst huv
        rw [if_pos hu]; split_ifs <;> omega
      · rw [if_neg hu]; split_ifs <;> omega
  have h3 := hopt h hh
  have h4 : ∑ e, h e = ∑ e, g e + 1 := by
    simp only [h]; rw [flowalloc_bump]; simp
  omega

lemma flowalloc_construct {g : E → ℕ} (hg : flowalloc_WF G g)
    (hopt : ∀ h, flowalloc_WF G h → ∑ e, h e ≤ ∑ e, g e) :
    ∃ a : Profile E, G.IsUnitRanking a ∧ G.IsFeasible a g := by
  classical
  choose A1 hA1b hA1m hA1s using fun v : V => flowalloc_alloc (G.outEdges v) g
  choose A2 hA2b hA2m hA2s using
    fun v : V => flowalloc_alloc (G.outEdges v) (fun e => G.c e - g e)
  let o : V → ℕ := fun v => ∑ e ∈ G.outEdges v, g e
  have hid : ∀ v, ∑ e ∈ G.outEdges v, (G.c e - g e) + o v = G.cplus v := by
    intro v
    simp only [o, Game.cplus]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun e _ => Nat.sub_add_cancel (hg.1 e)
  let a : Profile E := fun e y => A1 (G.tail e) e y + A2 (G.tail e) e (y - o (G.tail e))
  have hsum : ∀ v y, ∑ e ∈ G.outEdges v, a e y = min (G.cplus v) y := by
    intro v y
    have : ∑ e ∈ G.outEdges v, a e y =
        ∑ e ∈ G.outEdges v, (A1 v e y + A2 v e (y - o v)) := by
      refine sum_congr rfl fun e he => ?_
      have : G.tail e = v := (flowalloc_mem_out G).mp he
      simp only [a, this]
    rw [this, sum_add_distrib, hA1s, hA2s]
    have := hid v
    simp only [o] at this ⊢
    omega
  refine ⟨a, ⟨fun e y => ?_, fun v y => ?_, hsum, fun e => ?_⟩, fun e => ?_⟩
  · have := hA1b (G.tail e) e y
    have := hA2b (G.tail e) e (y - o (G.tail e))
    have := hg.1 e
    simp only [a]; omega
  · rw [hsum]; exact min_le_right _ _
  · intro x y hxy
    exact add_le_add (hA1m _ _ hxy) (hA2m _ _ (Nat.sub_le_sub_right hxy _))
  · set v := G.tail e with hv
    have he : e ∈ G.outEdges v := (flowalloc_mem_out G).mpr rfl
    have hs := flowalloc_sat G hg hopt v
    have hle := hg.2 v
    have k1 : A1 v e (G.supply g v) = g e := by
      have hs1 := hA1s v (G.supply g v)
      have : ∑ e' ∈ G.outEdges v, A1 v e' (G.supply g v) = ∑ e' ∈ G.outEdges v, g e' := by
        rw [hs1]; exact min_eq_left hle
      exact (sum_eq_sum_iff_of_le (fun e' _ => hA1b v e' _)).mp this e he
    have k2 : A2 v e (G.supply g v - o v) = 0 := by
      have hs2 := hA2s v (G.supply g v - o v)
      have hid' := hid v
      have : ∑ e' ∈ G.outEdges v, A2 v e' (G.supply g v - o v) = 0 := by
        rw [hs2]; simp only [o] at hid' ⊢; omega
      exact (sum_eq_zero_iff.mp this) e he
    show g e = A1 v e (G.supply g v) + A2 v e (G.supply g v - o v)
    rw [k1, k2]; rfl

end

theorem exists_strong_equilibrium_max_flow {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) : ∃ a : Profile E, G.IsStrongEquilibrium a ∧
      ∀ a' : Profile E, G.IsUnitRanking a' → G.flow a' ≤ G.flow a := by
  classical
  obtain ⟨g, hg, hopt⟩ := flowalloc_exists_opt G
  obtain ⟨a, ha, hfeas⟩ := flowalloc_construct G hg hopt
  have hcs : G.clearingState a = g := by
    have hle : ∀ e, g e ≤ G.clearingState a e := flowalloc_le_cs G ha hfeas
    have h2 := hopt _ (flowalloc_cs_WF G ha)
    have h3 : ∑ e, g e = ∑ e, G.clearingState a e :=
      le_antisymm (sum_le_sum fun e _ => hle e) h2
    funext e
    exact ((sum_eq_sum_iff_of_le (fun e _ => hle e)).mp h3 e (mem_univ e)).symm
  refine ⟨a, ⟨ha, ?_⟩, ?_⟩
  · intro C a' hC ha'' himp
    set b := G.deviate a a' C with hb
    set F := G.clearingState b with hF
    have key1 : ∀ v ∈ C, G.supply g v < G.supply F v := by
      intro v hv
      have h1 := himp v hv
      simp only [Game.utility, hcs] at h1
      rw [← hF] at h1
      rw [flowalloc_sat G hg hopt v] at h1
      have h2 := flowalloc_cs_out_le G ha'' v
      rw [← hF] at h2
      omega
    have key2 : ∀ e, g e < F e → G.supply g (G.tail e) < G.supply F (G.tail e) := by
      intro e he
      by_cases hc : G.tail e ∈ C
      · exact key1 _ hc
      · by_contra hcon
        replace hcon := not_lt.mp hcon
        have h1 := flowalloc_cs_post G ha'' e
        rw [← hF] at h1
        have h2 : b e = a e := by simp only [hb, Game.deviate, if_neg hc]
        rw [h2] at h1
        have h3 := ha.2.2.2 e hcon
        have h4 := hfeas e
        omega
    have key3 : ∀ v, G.supply g v < G.supply F v → ∃ e, g e < F e ∧ G.head e = v := by
      intro v hv
      unfold Game.supply at hv
      have : ∑ e ∈ G.inEdges v, g e < ∑ e ∈ G.inEdges v, F e := by omega
      obtain ⟨e, he, hlt⟩ := exists_lt_of_sum_lt this
      exact ⟨e, hlt, (flowalloc_mem_in G).mp he⟩
    let U := univ.filter (fun v => G.supply g v < G.supply F v)
    obtain ⟨v0, hv0⟩ := hC
    have hUne : U.Nonempty := ⟨v0, mem_filter.mpr ⟨mem_univ _, key1 v0 hv0⟩⟩
    have hUcl : ∀ v ∈ U, ∃ e, g e < F e ∧ G.head e = v ∧ G.tail e ∈ U := by
      intro v hv
      obtain ⟨e, hlt, hhd⟩ := key3 v (mem_filter.mp hv).2
      exact ⟨e, hlt, hhd, mem_filter.mpr ⟨mem_univ _, key2 e hlt⟩⟩
    obtain ⟨T, hTne, p, hp, hinj⟩ :=
      flowalloc_cycle G.tail G.head (fun e => g e < F e) _ U rfl hUne hUcl
    let k : E → ℕ := fun e => (T.filter (fun t => p t = e)).card
    let h : E → ℕ := fun e => g e + k e
    have hk1 : ∀ e, k e ≤ 1 := by
      intro e
      apply card_le_one.mpr
      intro t1 ht1 t2 ht2
      obtain ⟨ht1, hp1⟩ := mem_filter.mp ht1
      obtain ⟨ht2, hp2⟩ := mem_filter.mp ht2
      rw [← (hp t1 ht1).2.1, ← (hp t2 ht2).2.1, hp1, hp2]
    have hkS : ∀ S : Finset E, ∑ e ∈ S, k e = (T.filter (fun t => p t ∈ S)).card :=
      fun S => flowalloc_count T p S
    have hh : flowalloc_WF G h := by
      refine ⟨fun e => ?_, fun v => ?_⟩
      · have hc := flowalloc_cs_le_c G ha'' e
        rw [← hF] at hc
        by_cases hk0 : k e = 0
        · simp only [h, hk0]; have := hg.1 e; omega
        · obtain ⟨t, ht⟩ := card_pos.mp (Nat.pos_of_ne_zero hk0)
          obtain ⟨ht, hpt⟩ := mem_filter.mp ht
          have := (hp t ht).1
          rw [hpt] at this
          have := hk1 e
          simp only [h]; omega
      · have hout : ∑ e ∈ G.outEdges v, h e = ∑ e ∈ G.outEdges v, g e +
            (T.filter (fun t => p t ∈ G.outEdges v)).card := by
          simp only [h]; rw [sum_add_distrib, hkS]
        have hin : G.supply h v = G.supply g v +
            (T.filter (fun t => p t ∈ G.inEdges v)).card := by
          simp only [Game.supply, h]; rw [sum_add_distrib, hkS]; ring
        rw [hout, hin]
        have hgv := hg.2 v
        have hcmp : (T.filter (fun t => p t ∈ G.outEdges v)).card ≤
            (T.filter (fun t => p t ∈ G.inEdges v)).card := by
          by_cases hvT : v ∈ T
          · have hle1 : (T.filter (fun t => p t ∈ G.outEdges v)).card ≤ 1 := by
              apply card_le_one.mpr
              intro t1 ht1 t2 ht2
              obtain ⟨ht1, hp1⟩ := mem_filter.mp ht1
              obtain ⟨ht2, hp2⟩ := mem_filter.mp ht2
              apply hinj ht1 ht2
              simp only
              rw [(flowalloc_mem_out G).mp hp1, (flowalloc_mem_out G).mp hp2]
            have hge1 : 1 ≤ (T.filter (fun t => p t ∈ G.inEdges v)).card := by
              apply card_pos.mpr
              exact ⟨v, mem_filter.mpr ⟨hvT, (flowalloc_mem_in G).mpr (hp v hvT).2.1⟩⟩
            omega
          · have : T.filter (fun t => p t ∈ G.outEdges v) = ∅ := by
              apply filter_eq_empty_iff.mpr
              intro t ht hpt
              have h1 := (flowalloc_mem_out G).mp hpt
              have h2 := (hp t ht).2.2
              rw [h1] at h2
              exact hvT h2
            rw [this]; simp
        omega
    have htot := hopt h hh
    have h5 : ∑ e, h e = ∑ e, g e + T.card := by
      simp only [h]; rw [sum_add_distrib, hkS]
      congr 1
      congr 1
      exact filter_true_of_mem fun t _ => mem_univ _
    have h6 := card_pos.mpr hTne
    omega
  · intro a' ha'
    unfold Game.flow
    rw [hcs]
    exact hopt _ (flowalloc_cs_WF G ha')

end FlowAllocGames.StrongEq


-- Platform entry point: restates the target verbatim.
namespace FlowAllocGames.StrongEq

open Finset

/-- Theorem 9 (arXiv:1908.01714v3, pp. 22–23), first sentence: every unit-ranking game has a strong
equilibrium whose total flow is maximal among all unit-ranking profiles. -/
theorem _root_.solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) : ∃ a : Profile E, G.IsStrongEquilibrium a ∧
      ∀ a' : Profile E, G.IsUnitRanking a' → G.flow a' ≤ G.flow a := by
  apply @FlowAllocGames.StrongEq.exists_strong_equilibrium_max_flow <;> assumption

end FlowAllocGames.StrongEq
