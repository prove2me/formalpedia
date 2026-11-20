-- Prove2me | solution 1 for EnvyFreeCake104.Divide.permute_query_meter__p2m_285187a7_b6ea_4e38_bca1_5cfc5b97af68_a2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-19T16:20:04.920445+00:00
-- url     : https://prove2.me/submissions/7ce1e535-1e24-4786-be4e-9824de74a4f3

import Definitions.Def_EnvyFreeCake104_Divide_Protocols
import Theorems.Thm_EnvyFreeCake104_Divide_prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
import Theorems.Thm_EnvyFreeCake104_Divide_splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2

open EnvyFreeCake104.Divide

namespace PQMAux

variable {ι : Type}

theorem run_bind {α β : Type} (V : ι → Valuation) (o : ChoiceOracle ι)
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

/-- The query meter: prefix cuts never decrease, and queries grow by at most `K` per prefix cut. -/
def Meter (K : ℕ) : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop :=
  fun s tr₀ s' tr => s.prefixCuts ≤ s'.prefixCuts ∧
    queryCount tr + K * s.prefixCuts ≤ queryCount tr₀ + K * s'.prefixCuts

theorem meter_refl (K : ℕ) : ∀ (s : Rec ι) tr, Meter K s tr s tr := fun _ _ => ⟨le_rfl, le_rfl⟩

theorem meter_trans (K : ℕ) : ∀ (s₁ : Rec ι) t₁ s₂ t₂ s₃ t₃, Meter K s₁ t₁ s₂ t₂ →
    Meter K s₂ t₂ s₃ t₃ → Meter K s₁ t₁ s₃ t₃ := by
  intro s₁ t₁ s₂ t₂ s₃ t₃ ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨h1.trans h3, ?_⟩
  have : K * s₂.prefixCuts ≤ K * s₃.prefixCuts := Nat.mul_le_mul_left _ h3
  nlinarith

theorem meter_choose (V : ι → Valuation) (K : ℕ) {β : Type} (l : List β) :
    Inv V (Meter K) (chooseP l : Proto ι β) := by
  cases l with
  | nil => exact inv_fail V _ (meter_refl K)
  | cons b bs =>
    intro s o tr₀ y s' tr h
    change Prog.run V o (Prog.bind (Prog.choose bs.length (fun c => Prog.ret ((b :: bs).get c)))
      (fun a => Prog.ret (a, s))) tr₀ = _ at h
    simp only [Prog.bind, Prog.run, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, rfl⟩ := h
    refine ⟨le_rfl, ?_⟩
    simp [queryCount, List.countP_append, Event.isQuery]

def PC0 : Rec ι → List (Event ι) → Rec ι → List (Event ι) → Prop :=
  fun s _ s' _ => s'.prefixCuts = s.prefixCuts

theorem pc0_refl : ∀ (s : Rec ι) tr, PC0 s tr s tr := fun _ _ => rfl
theorem pc0_trans : ∀ (s₁ : Rec ι) t₁ s₂ t₂ s₃ t₃, PC0 s₁ t₁ s₂ t₂ →
    PC0 s₂ t₂ s₃ t₃ → PC0 s₁ t₁ s₃ t₃ := fun _ _ _ _ _ _ h1 h2 => h2.trans h1

theorem cut_pc0 (V : ι → Valuation) (i : ι) (x w : ℝ) : Inv V PC0 (cutQ i x w : Proto ι ℝ) := by
  intro s o tr₀ y s' tr h
  change Prog.run V o (Prog.bind (Prog.cut i x w Prog.ret) (fun a => Prog.ret (a, s))) tr₀ = _ at h
  simp only [Prog.bind, Prog.run, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, rfl⟩ := h; rfl

theorem split_pc0 [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (c y : ℝ) :
    Inv V PC0 (splitCell N c y) := by
  intro s o tr₀ u s' tr h
  obtain ⟨tr', h'⟩ :=
    splitCell_run_explicit__p2m_1bf3b025_64da_41d3_a86c_e0243aee6483_a2 V N s c y o tr₀
  rw [h'] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨-, rfl⟩, -⟩ := h; rfl

theorem prefixCut_pc [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (i : ι) (P : Piece)
    (w : ℝ) : Inv V (fun s _ s' _ => s'.prefixCuts = s.prefixCuts + 1) (prefixCut N i P w) := by
  intro s o tr₀ p s' tr h
  simp only [prefixCut, StateT.run_bind, StateT.run_modify, StateT.run_get] at h
  change Prog.run V o (StateT.run (match findInterval { s with prefixCuts := s.prefixCuts + 1 } i P 0 w with
    | none => if w ≤ 0 then pure (P.length, 0) else failP
    | some (k, w') =>
      if w' ≤ 0 then pure (k, (P.getD k default).a)
      else
        match findCell { s with prefixCuts := s.prefixCuts + 1 } i
            (({ s with prefixCuts := s.prefixCuts + 1 } : Rec ι).pts.filter
              (fun c => (P.getD k default).a ≤ c ∧ c < (P.getD k default).b) |>.sort (· ≤ ·)) w' with
        | none => failP
        | some (c, w'') => do
          let y ← cutQ i c w''
          if c < y ∧ y < ({ s with prefixCuts := s.prefixCuts + 1 } : Rec ι).nextPt c then
            splitCell N c y
          return (k, y)) { s with prefixCuts := s.prefixCuts + 1 }) tr₀ = _ at h
  have hpc : ∀ {m : Proto ι Pos}, Inv V PC0 m →
      Prog.run V o (m.run { s with prefixCuts := s.prefixCuts + 1 }) tr₀ = some ((p, s'), tr) →
      s'.prefixCuts = s.prefixCuts + 1 := fun hm hh => hm _ o tr₀ p s' tr hh
  split at h
  · split_ifs at h
    · exact hpc (inv_pure V PC0 pc0_refl _) h
    · exact hpc (inv_fail V PC0 pc0_refl) h
  · split_ifs at h
    · exact hpc (inv_pure V PC0 pc0_refl _) h
    · split at h
      · exact hpc (inv_fail V PC0 pc0_refl) h
      · refine hpc ?_ h
        refine inv_bind V PC0 pc0_refl pc0_trans (cut_pc0 V _ _ _) (fun y => ?_)
        dsimp only
        split_ifs
        · exact inv_bind V PC0 pc0_refl pc0_trans (split_pc0 V N _ _)
            (fun _ => inv_pure V PC0 pc0_refl _)
        · exact inv_pure V PC0 pc0_refl _

theorem prefixCut_meter [DecidableEq ι] (V : ι → Valuation) (N : Finset ι) (i : ι) (P : Piece)
    (w : ℝ) : Inv V (Meter (N.card + 1)) (prefixCut N i P w) := by
  intro s o tr₀ p s' tr h
  have h1 := prefixCut_pc V N i P w s o tr₀ p s' tr h
  have h2 := prefixCut_query_bound__p2m_c286858a_9e65_4696_8505_9d74071d7a32_a1
    V N i P w s o tr₀ p s' tr h
  refine ⟨by omega, ?_⟩
  rw [h1, Nat.mul_add, Nat.mul_one]; omega

section protocols
variable [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)

local notation "M" => Meter (ι := ι) (N.card + 1)

theorem trim_meter (Y : ι → Piece) : ∀ (earlier : List ι) (piece removed : Piece),
    Inv V M (trimAgainst N Y earlier piece removed) := by
  intro earlier
  induction earlier with
  | nil => intro piece removed; exact inv_pure V _ (meter_refl _) _
  | cons a rest ih =>
    intro piece removed
    simp only [trimAgainst]
    refine inv_bind V _ (meter_refl _) (meter_trans _) (inv_get V _ (meter_refl _)) (fun st => ?_)
    apply inv_ite V _ (meter_refl _)
    · exact inv_bind V _ (meter_refl _) (meter_trans _) (prefixCut_meter V N _ _ _) (fun p => ih _ _)
    · exact ih _ _

theorem candLoop_meter (P : ι → Piece) : ∀ (pairs : List (ι × ι)) (earlier : List ι)
    (Y : ι → Piece) (R : Piece), Inv V M (candidateLoop N P pairs earlier Y R) := by
  intro pairs
  induction pairs with
  | nil => intro earlier Y R; exact inv_pure V _ (meter_refl _) _
  | cons q rest ih =>
    intro earlier Y R
    obtain ⟨i, j⟩ := q
    simp only [candidateLoop]
    exact inv_bind V _ (meter_refl _) (meter_trans _) (trim_meter V N Y _ _ _)
      (fun x => by obtain ⟨pc, rm⟩ := x; exact ih _ _ _)

theorem permLoop_meter (P : ι → Piece) : ∀ (k : ℕ) (gs : List (List ι × List ι)),
    Inv V M (permuteLoop N P k gs) := by
  intro k
  induction k with
  | zero => intro gs; exact inv_fail V _ (meter_refl _)
  | succ k ih =>
    intro gs
    simp only [permuteLoop]
    refine inv_bind V _ (meter_refl _) (meter_trans _) (meter_choose V _ gs) (fun g => ?_)
    refine inv_bind V _ (meter_refl _) (meter_trans _) (candLoop_meter V N P _ _ _ _) (fun x => ?_)
    obtain ⟨Y, R⟩ := x
    refine inv_bind V _ (meter_refl _) (meter_trans _) (inv_get V _ (meter_refl _)) (fun st => ?_)
    split_ifs
    · exact inv_pure V _ (meter_refl _) _
    · exact ih _

end protocols

end PQMAux

open PQMAux in
theorem solution
    {ι : Type} [DecidableEq ι] (V : ι → Valuation) (N : Finset ι)
    (P : ι → Piece) (s : Rec ι) (o : ChoiceOracle ι)
    (Y : ι → Piece) (R : Piece) (s' : Rec ι) (tr : List (Event ι))
    (hrun : exec V o (permute N P) s = some ((Y, R), s', tr)) :
    queryCount tr ≤ (N.card + 1) * (s'.prefixCuts - s.prefixCuts) := by
  have hrun' : Prog.run V o ((permute N P).run s) [] = some (((Y, R), s'), tr) := by
    unfold exec at hrun
    rcases h : Prog.run V o ((permute N P).run s) [] with _ | ⟨⟨⟨x, u⟩, l⟩⟩
    · rw [h] at hrun; simp at hrun
    · rw [h] at hrun
      simp only [Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl, rfl⟩ := hrun; rfl
  obtain ⟨h1, h2⟩ := permLoop_meter V N P _ _ s o [] (Y, R) s' tr hrun'
  simp only [queryCount, List.countP_nil, zero_add] at h2
  rw [Nat.mul_sub]
  unfold queryCount
  omega
