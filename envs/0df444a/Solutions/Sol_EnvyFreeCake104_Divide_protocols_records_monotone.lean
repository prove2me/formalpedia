-- Prove2me | solution 1 for EnvyFreeCake104.Divide.protocols_records_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T17:18:26.644464+00:00
-- url     : https://prove2.me/submissions/39dfa2b9-24fd-40f7-96a9-f8323ce4aab7

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2
import Theorems.Thm_EnvyFreeCake104_Divide_split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2

open EnvyFreeCake104.Divide

namespace RMAux

theorem run_bind {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (f : α → Prog ι β) (tr : List (Event ι)) :
    Prog.run V o (Prog.bind p f) tr =
      match Prog.run V o p tr with
      | none => none
      | some (x, tr') => Prog.run V o (f x) tr' := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simp only [Prog.bind, Prog.run]
      exact ih (o tr m) (tr ++ [Event.choice m (o tr m)])

theorem run_stbind {ι α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (m : Proto ι α)
    (f : α → Proto ι β) (t : Rec ι) (tr₀ : List (Event ι)) :
    Prog.run V o ((m >>= f).run t) tr₀ =
      match Prog.run V o (m.run t) tr₀ with
      | none => none
      | some ((x, t'), tr') => Prog.run V o ((f x).run t') tr' := by
  rw [StateT.run_bind]
  change Prog.run V o (Prog.bind (m.run t) (fun p => (f p.1).run p.2)) tr₀ = _
  rw [run_bind]
  rcases Prog.run V o (m.run t) tr₀ with _ | ⟨⟨x, t'⟩, tr'⟩ <;> rfl

theorem run_get' {ι : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((get : Proto ι (Rec ι)).run t) tr₀ = some ((t, t), tr₀) := rfl

theorem run_pure' {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (x : α) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((pure x : Proto ι α).run t) tr₀ = some ((x, t), tr₀) := rfl

theorem run_fail' {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι) (t : Rec ι)
    (tr₀ : List (Event ι)) :
    Prog.run V o ((failP : Proto ι α).run t) tr₀ = none := rfl

theorem run_shift {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Prog ι α) (pretr tr : List (Event ι)) :
    Prog.run V o p (pretr ++ tr) =
      (Prog.run V (fun t m ↦ o (pretr ++ t) m) p tr).map
        (fun r : α × List (Event ι) ↦ (r.1, pretr ++ r.2)) := by
  induction p generalizing tr with
  | ret x => rfl
  | fail => rfl
  | eval i a b k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (evalAnswer V i a b) (tr ++ [Event.eval i a b (evalAnswer V i a b)])
  | cut i x w k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (cutAnswer V i x w) (tr ++ [Event.cut i x w (cutAnswer V i x w)])
  | choose m k ih =>
      simpa only [Prog.run, List.append_assoc] using
        ih (o (pretr ++ tr) m) (tr ++ [Event.choice m (o (pretr ++ tr) m)])

theorem exec_iff {ι α : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
    (p : Proto ι α) (s : Rec ι) (x : α) (s' : Rec ι) (tr : List (Event ι)) :
    exec V o p s = some (x, s', tr) ↔ Prog.run V o (p.run s) [] = some ((x, s'), tr) := by
  unfold exec
  rcases Prog.run V o (p.run s) [] with _ | ⟨⟨u, t⟩, l⟩
  · simp
  · simp only [Option.some.injEq, Prod.mk.injEq, and_assoc]


section
variable {ι : Type}



/-- A general invariant on a protocol, parametrized by a predicate on (start, end) records and
(start, end) transcripts, closed under bind when the predicate is transitive. -/
def Inv {α : Type} (V : ι → Valuation) (Rel : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop)
    (m : Proto ι α) : Prop :=
  ∀ (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι)) (x : α) (s' : Rec ι)
    (tr : List (Event ι)), Prog.run V o (m.run s) tr₀ = some ((x, s'), tr) → Rel s tr₀ s' tr

section
variable (V : ι → Valuation) (Rel : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop)
  (hrefl : ∀ s tr, Rel s tr s tr)
  (htrans : ∀ s₁ t₁ s₂ t₂ s₃ t₃, Rel s₁ t₁ s₂ t₂ → Rel s₂ t₂ s₃ t₃ → Rel s₁ t₁ s₃ t₃)
include hrefl

theorem inv_pure {α : Type} (x : α) : Inv V Rel (pure x : Proto ι α) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.ret (x, s)) tr₀ = _ at h
  simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; exact hrefl _ _

theorem inv_get : Inv V Rel (get : Proto ι (Rec ι)) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.ret (s, s)) tr₀ = _ at h
  simp only [Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; exact hrefl _ _

theorem inv_fail {α : Type} : Inv V Rel (failP : Proto ι α) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.bind (Prog.fail : Prog ι α) (fun a => Prog.ret (a, s))) tr₀ = _ at h
  simp [Prog.bind, Prog.run] at h

include htrans in
theorem inv_bind {α β : Type} {m : Proto ι α} {f : α → Proto ι β} (hm : Inv V Rel m)
    (hf : ∀ x, Inv V Rel (f x)) : Inv V Rel (m >>= f) := by
  intro s o tr₀ y s'' tr h
  rw [StateT.run_bind] at h
  change Prog.run V o (Prog.bind (m.run s) (fun p => (f p.1).run p.2)) tr₀ = _ at h
  rw [run_bind] at h
  rcases h1 : Prog.run V o (m.run s) tr₀ with _ | ⟨⟨x, s'⟩, tr1⟩
  · rw [h1] at h; exact absurd h (by simp)
  rw [h1] at h
  exact htrans _ _ _ _ _ _ (hm s o tr₀ x s' tr1 h1) (hf x s' o tr1 y s'' tr h)

theorem inv_ite {α : Type} (c : Prop) [Decidable c] {a b : Proto ι α} (ha : Inv V Rel a)
    (hb : Inv V Rel b) : Inv V Rel (if c then a else b) := by
  split_ifs; exacts [ha, hb]
end

end
section recmono
variable {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)

/-- The record relation: validity is preserved and recorded points only grow. -/
def RM : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop :=
  fun s _ s' _ => (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts

theorem rm_refl : ∀ (s : Rec ι) tr, RM V N s tr s tr := fun _ _ => ⟨id, subset_rfl⟩
theorem rm_trans : ∀ (s₁ : Rec ι) t₁ s₂ t₂ s₃ t₃, RM V N s₁ t₁ s₂ t₂ → RM V N s₂ t₂ s₃ t₃ →
    RM V N s₁ t₁ s₃ t₃ := fun _ _ _ _ _ _ h1 h2 => ⟨h2.1 ∘ h1.1, h1.2.trans h2.2⟩

theorem findCell_mem (s : Rec ι) (i : ι) : ∀ (l : List ℝ) (w c w' : ℝ),
    findCell s i l w = some (c, w') → c ∈ l := by
  intro l
  induction l with
  | nil => intro w c w' h; simp [findCell] at h
  | cons x xs ih =>
    intro w c w' h
    simp only [findCell] at h
    split_ifs at h with hx
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih _ c w' h)

theorem rm_choose {β : Type} (l : List β) : Inv V (RM V N) (chooseP l : Proto ι β) := by
  cases l with
  | nil => exact inv_fail V _ (rm_refl V N)
  | cons b bs =>
    intro s o tr₀ y s' tr h
    change Prog.run V o (Prog.bind (Prog.choose bs.length (fun c => Prog.ret ((b :: bs).get c)))
      (fun a => Prog.ret (a, s))) tr₀ = _ at h
    simp only [Prog.bind, Prog.run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, rfl⟩ := h
    exact ⟨id, subset_rfl⟩

theorem rm_prefixCut (i : ι) (P : Piece) (w : ℝ) : Inv V (RM V N) (prefixCut N i P w) := by
  intro s o tr₀ p s' tr h
  simp only [prefixCut, StateT.run_bind, StateT.run_modify, StateT.run_get] at h
  set s1 : Rec ι := { s with prefixCuts := s.prefixCuts + 1 } with hs1
  have hv1 : s.Valid V N → s1.Valid V N := fun hv => hv
  change Prog.run V o (StateT.run (match findInterval s1 i P 0 w with
    | none => if w ≤ 0 then pure (P.length, 0) else failP
    | some (k, w') =>
      if w' ≤ 0 then pure (k, (P.getD k default).a)
      else
        match findCell s1 i
            ((s1.pts.filter (fun c => (P.getD k default).a ≤ c ∧ c < (P.getD k default).b)).sort
              (· ≤ ·)) w' with
        | none => failP
        | some (c, w'') => do
          let y ← cutQ i c w''
          if c < y ∧ y < s1.nextPt c then
            splitCell N c y
          return (k, y)) s1) tr₀ = _ at h
  have hfin : ∀ {m : Proto ι Pos}, Inv V (RM V N) m →
      Prog.run V o (m.run s1) tr₀ = some ((p, s'), tr) → RM V N s tr₀ s' tr := by
    intro m hm hh
    have := hm s1 o tr₀ p s' tr hh
    exact ⟨this.1 ∘ hv1, this.2⟩
  split at h
  · split_ifs at h
    · exact hfin (inv_pure V _ (rm_refl V N) _) h
    · exact hfin (inv_fail V _ (rm_refl V N)) h
  · rename_i k w' _
    split_ifs at h
    · exact hfin (inv_pure V _ (rm_refl V N) _) h
    · split at h
      · exact hfin (inv_fail V _ (rm_refl V N)) h
      · rename_i c w'' hcell
        have hc : c ∈ s1.pts := by
          have := findCell_mem s1 i _ w' c w'' hcell
          rw [Finset.mem_sort] at this
          exact (Finset.mem_filter.mp this).1
        rw [run_stbind] at h
        change (match some ((cutAnswer V i c w'', s1), tr₀ ++ [Event.cut i c w'' (cutAnswer V i c w'')]) with
          | none => none
          | some ((x, t'), tr') => _) = _ at h
        dsimp only at h
        split_ifs at h with hcy
        · rw [run_stbind] at h
          obtain ⟨trs, hsc⟩ := splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s1
            c (cutAnswer V i c w'') o (tr₀ ++ [Event.cut i c w'' (cutAnswer V i c w'')])
          rw [hsc] at h
          dsimp only at h
          rw [run_pure'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨-, rfl⟩, -⟩ := h
          refine ⟨fun hv => split_update_valid__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s1 (hv1 hv) c _
            hc hcy.1 hcy.2, ?_⟩
          intro x hx; exact Finset.mem_insert_of_mem hx
        · rw [run_pure'] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨-, rfl⟩, -⟩ := h
          exact ⟨hv1, subset_rfl⟩

theorem rm_trim (Y : ι → Piece) : ∀ (earlier : List ι) (piece removed : Piece),
    Inv V (RM V N) (trimAgainst N Y earlier piece removed) := by
  intro earlier
  induction earlier with
  | nil => intro piece removed; exact inv_pure V _ (rm_refl V N) _
  | cons a rest ih =>
    intro piece removed
    simp only [trimAgainst]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    apply inv_ite V _ (rm_refl V N)
    · exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _) (fun p => ih _ _)
    · exact ih _ _

theorem rm_candLoop (P : ι → Piece) : ∀ (pairs : List (ι × ι)) (earlier : List ι)
    (Y : ι → Piece) (R : Piece), Inv V (RM V N) (candidateLoop N P pairs earlier Y R) := by
  intro pairs
  induction pairs with
  | nil => intro earlier Y R; exact inv_pure V _ (rm_refl V N) _
  | cons q rest ih =>
    intro earlier Y R
    obtain ⟨i, j⟩ := q
    simp only [candidateLoop]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_trim V N Y _ _ _)
      (fun x => by obtain ⟨pc, rm⟩ := x; exact ih _ _ _)

theorem rm_permute (P : ι → Piece) : Inv V (RM V N) (permute N P) := by
  have : ∀ (k : ℕ) (gs : List (List ι × List ι)), Inv V (RM V N) (permuteLoop N P k gs) := by
    intro k
    induction k with
    | zero => intro gs; exact inv_fail V _ (rm_refl V N)
    | succ k ih =>
      intro gs
      simp only [permuteLoop]
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N gs) (fun g => ?_)
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_candLoop V N P _ _ _ _) (fun x => ?_)
      obtain ⟨Y, R⟩ := x
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
      split_ifs
      · exact inv_pure V _ (rm_refl V N) _
      · exact ih _
  exact this _ _

theorem rm_equalCuts (c : ι) (w : ℝ) : ∀ (m : ℕ) (rest : Piece),
    Inv V (RM V N) (equalCuts N c w m rest) := by
  intro m
  induction m with
  | zero => intro rest; exact inv_pure V _ (rm_refl V N) _
  | succ m ih =>
    intro rest
    simp only [equalCuts]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) (ih _) (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_core (c : ι) (C : Piece) : Inv V (RM V N) (core N c C) := by
  unfold core
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_equalCuts V N _ _ _ _)
    (fun ps => rm_permute V N _)

theorem rm_marksOf (R : Piece) (i : ι) (v : ℝ) (M : ℕ) : ∀ ts : List ℕ,
    Inv V (RM V N) (marksOf N R i v M ts) := by
  intro ts
  induction ts with
  | nil => exact inv_pure V _ (rm_refl V N) _
  | cons t ts ih =>
    simp only [marksOf]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_prefixCut V N _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) ih (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_allMarks (R : Piece) (v : ι → ℝ) (M : ℕ) : ∀ l : List ι,
    Inv V (RM V N) (allMarks N R v M l) := by
  intro l
  induction l with
  | nil => exact inv_pure V _ (rm_refl V N) _
  | cons i l ih =>
    simp only [allMarks]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_marksOf V N _ _ _ _ _)
      (fun p => inv_bind V _ (rm_refl V N) (rm_trans V N) ih (fun _ => inv_pure V _ (rm_refl V N) _))

theorem rm_rrPick (cells : List Piece) (avail : List ℕ) (i : ι) :
    Inv V (RM V N) (rrPick cells avail i) := by
  unfold rrPick
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N))
    (fun st => rm_choose V N _)

theorem rm_rrRound (cells : List Piece) : ∀ (order : List ι) (avail : List ℕ) (Q : ι → List ℕ),
    Inv V (RM V N) (rrRound cells order avail Q) := by
  intro order
  induction order with
  | nil => intro avail Q; exact inv_pure V _ (rm_refl V N) _
  | cons i is ih =>
    intro avail Q
    simp only [rrRound]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_rrPick V N _ _ _) (fun c => ih _ _)

theorem rm_roundRobin (cells : List Piece) (order : List ι) : ∀ (r : ℕ) (avail : List ℕ)
    (Q : ι → List ℕ), Inv V (RM V N) (roundRobin cells order r avail Q) := by
  intro r
  induction r with
  | zero => intro avail Q; exact inv_pure V _ (rm_refl V N) _
  | succ r ih =>
    intro avail Q
    simp only [roundRobin]
    exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_rrRound V N _ _ _ _)
      (fun x => by obtain ⟨Q', a'⟩ := x; exact ih _ _)

theorem rm_repair (D : ι → Piece) (R : Piece) (ε : ℝ) : Inv V (RM V N) (repair N D R ε) := by
  unfold repair
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_allMarks V N _ _ _ _) (fun marks => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _) (fun order => ?_)
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_roundRobin V N _ _ _ _ _) (fun x => ?_)
  obtain ⟨Q, avail⟩ := x
  refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_permute V N _) (fun x => ?_)
  obtain ⟨W, U⟩ := x
  exact inv_pure V _ (rm_refl V N) _

theorem rm_shrink (istar : ι) (α : ℝ) (U : Piece) : ∀ (fuel : ℕ) (W : ι → Piece) (R' : Piece),
    Inv V (RM V N) (shrink N istar α U fuel W R') := by
  intro fuel
  induction fuel with
  | zero =>
    intro W R'
    rw [shrink.eq_def]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    split_ifs
    · exact inv_fail V _ (rm_refl V N)
    · exact inv_pure V _ (rm_refl V N) _
  | succ f ih =>
    intro W R'
    rw [shrink.eq_def]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    split_ifs
    · dsimp only
      exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_core V N _ _)
        (fun x => by obtain ⟨F, R''⟩ := x; exact ih _ _)
    · exact inv_pure V _ (rm_refl V N) _

theorem rm_dominateLoop (c : ι) : ∀ (fuel : ℕ) (X : ι → Piece) (R : Piece),
    Inv V (RM V N) (dominateLoop N c fuel X R) := by
  intro fuel
  induction fuel with
  | zero => intro X R; rw [dominateLoop]; exact inv_fail V _ (rm_refl V N)
  | succ f ih =>
    intro X R
    rw [dominateLoop]
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_core V N _ _) (fun x => ?_)
    obtain ⟨Y, U⟩ := x
    try dsimp only
    refine inv_bind V _ (rm_refl V N) (rm_trans V N) (inv_get V _ (rm_refl V N)) (fun st => ?_)
    try dsimp only
    split_ifs
    · exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _)
        (fun _ => inv_pure V _ (rm_refl V N) _)
    · refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _) (fun x => ?_)
      obtain ⟨t, istar, jstar, l'⟩ := x
      try dsimp only
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_repair V N _ _ _) (fun x => ?_)
      obtain ⟨W, R'⟩ := x
      try dsimp only
      refine inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_shrink V N _ _ _ _ _ _) (fun x => ?_)
      obtain ⟨W', R''⟩ := x
      exact ih _ _

theorem rm_dominate (fuel : ℕ) (C : Piece) : Inv V (RM V N) (dominate fuel N C) := by
  unfold dominate
  exact inv_bind V _ (rm_refl V N) (rm_trans V N) (rm_choose V N _)
    (fun c => rm_dominateLoop V N c _ _ _)

end recmono

end RMAux

open RMAux in
theorem solution {ι : Type} [DecidableEq ι] (V : ι → Valuation)
    (N : Finset ι) :
    (∀ (P : ι → Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((permute N P).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (c : ι) (C : Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((core N c C).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (D : ι → Piece) (R : Piece) (ε : ℝ) (s : Rec ι) (o : ChoiceOracle ι)
        (tr₀ : List (Event ι)) (x : (ι → Piece) × Piece) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((repair N D R ε).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (istar : ι) (α : ℝ) (U : Piece) (fuel : ℕ) (W : ι → Piece) (R' : Piece) (s : Rec ι)
        (o : ChoiceOracle ι) (tr₀ : List (Event ι)) (x : (ι → Piece) × Piece) (s' : Rec ι)
        (tr : List (Event ι)),
        Prog.run V o ((shrink N istar α U fuel W R').run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) ∧
    (∀ (fuel : ℕ) (C : Piece) (s : Rec ι) (o : ChoiceOracle ι) (tr₀ : List (Event ι))
        (x : (ι → Piece) × Piece × Finset ι) (s' : Rec ι) (tr : List (Event ι)),
        Prog.run V o ((dominate fuel N C).run s) tr₀ = some ((x, s'), tr) →
        (s.Valid V N → s'.Valid V N) ∧ s.pts ⊆ s'.pts) :=
  ⟨fun P s o tr₀ x s' tr h => rm_permute V N P s o tr₀ x s' tr h,
   fun c C s o tr₀ x s' tr h => rm_core V N c C s o tr₀ x s' tr h,
   fun D R ε s o tr₀ x s' tr h => rm_repair V N D R ε s o tr₀ x s' tr h,
   fun i α U f W R' s o tr₀ x s' tr h => rm_shrink V N i α U f W R' s o tr₀ x s' tr h,
   fun f C s o tr₀ x s' tr h => rm_dominate V N f C s o tr₀ x s' tr h⟩
