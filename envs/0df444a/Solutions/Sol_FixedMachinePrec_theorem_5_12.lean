-- Prove2me | solution 1 for FixedMachinePrec.theorem_5_12
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kj
-- created : 2026-11-26T17:00:16.367288+00:00
-- url     : https://prove2.me/submissions/f6852cde-49b1-4c97-8762-ab2dfe7ea715
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline
import Theorems.Thm_FixedMachinePrec_lemma_5_1
import Theorems.Thm_FixedMachinePrec_lemma_5_2
import Theorems.Thm_FixedMachinePrec_generateFamily_extensional
import Theorems.Thm_FixedMachinePrec_serialSchedule_meets_job_count
import Theorems.Thm_FixedMachinePrec_extract_padded_deadline
import Theorems.Thm_FixedMachinePrec_fill_slot_schedule_with_dummies
import Theorems.Thm_FixedMachinePrec_theorem_5_6
import Theorems.Thm_FixedMachinePrec_theorem_5_8
import Theorems.Thm_FixedMachinePrec_theorem_5_9

open FixedMachinePrec


private theorem topo_complete {N : ℕ} (p : Fin N → Fin N → Prop) [DecidableRel p]
    (wf : WellFounded p) :
    let L := topoList p
    L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
  let Good (l : List (Fin N)) := l.Nodup ∧ ∀ y ∈ l, ∀ x, p x y → x ∈ l ∧ l.idxOf x < l.idxOf y
  let step (l : List (Fin N)) (_ : ℕ) := match (List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) with
    | some x => l ++ [x]
    | none => l
  have finish (xs : List ℕ) (l : List (Fin N)) (hl : Good l) (hn : l.length + xs.length = N) :
      let L := xs.foldl step l
      L.length = N ∧ (∀ x, x ∈ L) ∧ ∀ x y, p x y → L.idxOf x < L.idxOf y := by
    induction xs generalizing l with
    | nil =>
      have hc : l.toFinset = Finset.univ := by
        apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
        simp [List.toFinset_card_of_nodup hl.1] at hn ⊢; omega
      have allmem (x : Fin N) : x ∈ l := List.mem_toFinset.mp (hc ▸ Finset.mem_univ x)
      exact ⟨by simpa using hn, allmem,fun x y h => (hl.2 y (allmem y) x h).2⟩
    | cons a xs ih =>
      have missing : ∃ x : Fin N, x ∉ l := by
        by_contra! allmem
        have hc : l.toFinset = Finset.univ := Finset.eq_univ_of_forall (by simpa using allmem)
        have := congrArg Finset.card hc
        simp [List.toFinset_card_of_nodup hl.1] at this
        simp only [List.length_cons] at hn
        omega
      let rem : Set (Fin N) := {x | x ∉ l}
      have hrem : rem.Nonempty := missing
      let z := wf.min rem hrem
      have hz : z ∉ l := wf.min_mem rem hrem
      have hpred (y) (hy : p y z) : y ∈ l := by
        by_contra h
        exact wf.not_lt_min rem (show y ∈ rem from h) hy
      have hit : ((List.finRange N).find? (fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l))).isSome :=
        List.find?_isSome.mpr ⟨z,by simp,decide_eq_true ⟨hz,hpred⟩⟩
      obtain ⟨x,hx⟩ := Option.isSome_iff_exists.mp hit
      have hp : x ∉ l ∧ ∀ y, p y x → y ∈ l := of_decide_eq_true (List.find?_some (p := fun x => decide (x ∉ l ∧ ∀ y, p y x → y ∈ l)) hx)
      have hs : step l a = l ++ [x] := by dsimp only [step]; rw [hx]
      simp only [List.foldl_cons,hs]
      apply ih
      · constructor
        · simp [List.nodup_append, hl.1]; grind
        · intro y hy w hw
          rcases List.mem_append.mp hy with old | new
          · obtain ⟨hmem,hpos⟩ := hl.2 y old w hw
            simp [List.idxOf_append,old,hmem,hpos]
          · have eq : y = x := by simpa using new
            subst y
            have hmem := hp.2 w hw
            simp [List.idxOf_append,hp.1,hmem,List.idxOf_lt_length_of_mem hmem]
      · change (l ++ [x]).length + xs.length = N; simp at hn ⊢; omega
  exact finish (List.range N) [] (by simp [Good]) (by simp)


private theorem slot_capacity {G : Instance} {m T : ℕ} {τ : Fin G.n → ℕ}
    (h : IsSlotSchedule G m T τ) : G.n ≤ T * m := by
  have hmap : ((Finset.univ : Finset (Fin G.n)) : Set (Fin G.n)).MapsTo τ (Finset.Icc 1 T) :=
    fun x _ => Finset.mem_Icc.mpr (h.1 x)
  have e := Finset.card_eq_sum_card_fiberwise hmap
  calc
    G.n = ∑ t ∈ Finset.Icc 1 T, (Finset.univ.filter fun x => τ x = t).card := by simpa using e
    _ ≤ ∑ _t ∈ Finset.Icc 1 T, m := Finset.sum_le_sum fun t _ => h.2.1 t
    _ = T * m := by simp [Nat.card_Icc]

private theorem rank_ok {N} (p : Fin N → Fin N → Prop) [DecidableRel p] (hp : IsStrictOrder' p) : IsTopoRank p (topoRank p) := by
  letI : IsTrans _ p := ⟨hp.2⟩
  letI : Std.Irrefl p := ⟨hp.1⟩
  obtain ⟨hl,hm,ho⟩ := topo_complete p (Finite.wellFounded_of_trans_of_irrefl p)
  refine ⟨fun x => ⟨by simp [topoRank],?_⟩,?_,fun x y h => Nat.succ_lt_succ (ho x y h)⟩
  · have h := List.idxOf_lt_length_of_mem (hm x); simpa [topoRank,hl] using h
  · intro x y e
    have h : (topoList p).idxOf x = (topoList p).idxOf y := by simpa [topoRank] using e
    have ex := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm x))
    have ey := List.getElem_idxOf (List.idxOf_lt_length_of_mem (hm y))
    simpa [h,ey] using ex.symm

private theorem full_count {N m} {p : Fin N → Fin N → Prop} {W S} (hs : IsFullSchedule p m W S) : W.card = m*S.length := by
  obtain ⟨hslot,hdis,hu,horder⟩ := hs
  clear horder
  rw [← hu]; clear hu
  induction S with
  | nil => simp
  | cons a s ih =>
    have hd := List.pairwise_cons.mp hdis
    have dj : Disjoint a (s.foldr (· ∪ ·) ∅) := by
      have aux (l : List (Finset (Fin N))) (h : ∀ b ∈ l, Disjoint a b) : Disjoint a (l.foldr (· ∪ ·) ∅) := by
        induction l with
        | nil => simp
        | cons b l ih => simp [h b (by simp),ih (fun c hc => h c (by simp [hc]))]
      exact aux _ hd.1
    simp only [List.foldr_cons,Finset.card_union_of_disjoint dj,List.length_cons,Nat.mul_add,Nat.mul_one]
    rw [(hslot a (by simp)).1,ih (fun b hb => hslot b (by simp [hb])) hd.2,Nat.add_comm]

private theorem search_bracket (G : Instance) (m : ℕ)
    (hd : ∀ T, (deadline G m T = none ↔ ¬DeadlineFeasible G m T) ∧ ∀ σ, deadline G m T = some σ → σ.MeetsDeadline m T)
    (fuel l u : ℕ) (σ : SlotSchedule G) (hw : u-l ≤ fuel) (hno : ¬DeadlineFeasible G m l) (hyes : σ.MeetsDeadline m u) :
    let res := optimumLoop G m fuel l u σ
    (∀ t < res.1, ¬DeadlineFeasible G m t) ∧ res.2.MeetsDeadline m res.1 := by
  have finish (l u : ℕ) (σ : SlotSchedule G) (h : u-l ≤ 1) (hl : ¬DeadlineFeasible G m l) (hu : σ.MeetsDeadline m u) :
      (∀ t < u, ¬DeadlineFeasible G m t) ∧ σ.MeetsDeadline m u := by
    refine ⟨?_,hu⟩
    rintro t ht ⟨ρ,hf,hc⟩
    exact hl ⟨ρ,hf,hc.trans (by exact_mod_cast (show t ≤ l by omega))⟩
  induction fuel generalizing l u σ with
  | zero => exact finish l u σ (by omega) hno hyes
  | succ fuel ih =>
    simp only [optimumLoop]
    split
    · split
      · rename_i he; exact ih _ _ _ (by omega) ((hd _).1.mp he) hyes
      · rename_i s he; exact ih _ _ _ (by omega) hno ((hd _).2 s he)
    · exact finish l u σ (by omega) hno hyes

theorem solution (m : ℕ) (hm : 3 ≤ m) (G : Instance) (hG : G.Acyclic) :
    (∀ T : ℕ, (deadline G m T = none ↔ ¬ DeadlineFeasible G m T) ∧
      ∀ σ, deadline G m T = some σ → σ.MeetsDeadline m T) ∧
    (∃ ρ : Schedule G m, (optimum G m).2.Realizes ρ ∧ IsOptimum ρ ∧
      ρ.cmax = ((optimum G m).1 : ℝ)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  by_cases zero : G.n = 0
  · let ρ : Schedule G m := ⟨fun _ => 0,fun _ => ⟨0,hm1⟩⟩
    have no (x : Fin G.n) : False := by have := x.isLt; omega
    have real : (emptySchedule G).Realizes ρ := fun x => (no x).elim
    have feas : ρ.Feasible := ⟨fun x => (no x).elim,fun x => (no x).elim,fun x => (no x).elim⟩
    have cm (s : Schedule G m) : s.cmax = 0 := by simp [Schedule.cmax,zero]
    constructor
    · intro T
      have hd : DeadlineFeasible G m T := ⟨ρ,feas,by simp [cm]⟩
      simp only [deadline,zero,if_true,reduceCtorEq,hd,not_true_eq_false,iff_self,true_and,Option.some.injEq]
      rintro σ rfl; exact ⟨ρ,real,feas,by simp [cm]⟩
    · exact ⟨ρ,by simpa [optimum,zero] using real,⟨feas,fun s _ => by simp [cm]⟩,by simp [cm,optimum,zero]⟩
  have hn : 0 < G.n := by omega
  obtain ⟨low,_,pad⟩ := lemma_5_2 m hm1 G hG hn
  have serial := serialSchedule_meets_job_count m hm1 G hG
  have correct (T : ℕ) : (deadline G m T = none ↔ ¬ DeadlineFeasible G m T) ∧ ∀ σ, deadline G m T = some σ → σ.MeetsDeadline m T := by
    by_cases lo : T < ceilDiv G.n m
    · simp [deadline,zero,lo,low _ lo]
    by_cases big : G.n ≤ T
    · obtain ⟨ρ,hr,hf,hc⟩ := serial
      have ht := hc.trans (show (G.n : ℝ) ≤ T by exact_mod_cast big)
      have hd : DeadlineFeasible G m T := ⟨ρ,hf,ht⟩
      simp only [deadline,zero,lo,big,if_false,if_true,reduceCtorEq,hd,not_true_eq_false,iff_self,true_and,Option.some.injEq]
      rintro σ rfl; exact ⟨ρ,hr,hf,ht⟩
    let p := paddedPrec G (m*T)
    have po : IsStrictOrder' p := ⟨fun x ⟨hx,hy,h⟩ => hG _ h,fun x y z ⟨hx,hy,h⟩ ⟨_,hz,h'⟩ => ⟨hx,hz,h.trans h'⟩⟩
    let r := topoRank p
    let F := family p r m (4*m+5)
    let C := family p r m (m+3)
    have atom (a : Atom (m*T)) (h : a.Valid m) : a.eval p r ∈ F := by
      simp only [F,family,Finset.mem_filter,Finset.mem_univ,true_and]; exact ⟨.atom a,h,show 1 ≤ 4*m+5 by omega,rfl⟩
    have h0 := atom .empty trivial; have hJ := atom .univ trivial
    have hdl : deadline G m T = (evaluateFamily p m F C Finset.univ).map (extractSchedule G) := by
      unfold deadline
      simp only [zero,lo,big,if_false]
      simp only [generateFamily_extensional m _ _ (4*m+5) (by omega),generateFamily_extensional m _ _ (m+3) (by omega)]
      cases ev : evaluateFamily p m F C Finset.univ <;> rfl
    have size : G.n ≤ m*T := by
      have q : (G.n+m-1)/m < T+1 := Nat.lt_succ_of_le (Nat.le_of_not_gt lo)
      have h := (Nat.div_lt_iff_lt_mul hm1).mp q
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm T m] at h; omega
    cases ev : evaluateFamily p m F C Finset.univ with
    | none =>
      have neg : ¬DeadlineFeasible G m T := by
        intro hf
        obtain ⟨s,hs,_⟩ := ((pad T (by omega) (by omega)).1).mp hf
        have desc := theorem_5_8 m hm p po r (rank_ok p po) ⟨s,hs⟩
        have yes := (theorem_5_9 m hm1 p po F C h0 hJ).2 desc
        simp [ev] at yes
      simp [hdl,ev,neg]
    | some s =>
      have hs := theorem_5_6 m hm1 p po F C h0 hJ _ _ ev
      have len : s.length = T := by have h := full_count hs; simp only [Finset.card_univ,Fintype.card_fin] at h; nlinarith
      have meet := extract_padded_deadline G m T size s hs len
      have ⟨ρ,_,hf,hc⟩ := meet
      have hd : DeadlineFeasible G m T := ⟨ρ,hf,hc⟩
      simp only [hdl,ev,Option.map_some,reduceCtorEq,hd,not_true_eq_false,iff_self,true_and,Option.some.injEq]
      rintro σ rfl; exact meet
  refine ⟨correct,?_⟩
  have ceilpos : 0 < ceilDiv G.n m := by
    apply (Nat.le_div_iff_mul_le hm1).mpr; simp; omega
  have bound := search_bracket G m correct (G.n+1) (ceilDiv G.n m-1) G.n (serialSchedule G) (by omega) (low _ (by omega)) serial
  rw [optimum,if_neg zero]
  let res := optimumLoop G m (G.n+1) (ceilDiv G.n m-1) G.n (serialSchedule G)
  obtain ⟨hmin,ρ,hr,hf,hc⟩ := bound
  have lower (s : Schedule G m) (hs : s.Feasible) : (res.1 : ℝ) ≤ s.cmax := by
    obtain ⟨u,τ,hτ,hu⟩ := lemma_5_1 m hm1 G hG s hs
    obtain ⟨L,hL,hlen⟩ := fill_slot_schedule_with_dummies G m u τ hτ
    have sz : G.n ≤ m*u := by simpa [Nat.mul_comm] using slot_capacity hτ
    obtain ⟨s',_,hs',hc'⟩ := extract_padded_deadline G m u sz L hL hlen
    have hu' : res.1 ≤ u := by by_contra! h; exact hmin u h ⟨s',hs',hc'⟩
    exact (show (res.1 : ℝ) ≤ u by exact_mod_cast hu').trans hu
  exact ⟨ρ,hr,⟨hf,fun s hs => hc.trans (lower s hs)⟩,le_antisymm hc (lower ρ hf)⟩
