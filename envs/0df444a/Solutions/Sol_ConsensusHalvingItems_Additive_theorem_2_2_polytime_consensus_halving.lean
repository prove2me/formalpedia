-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.theorem_2_2_polytime_consensus_halving
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-08T00:04:29.556398+00:00
-- url     : https://prove2.me/submissions/70ba7194-01ab-40a8-bf1e-87723874090a

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_halve
import Definitions.Def_ConsensusHalvingItems_Additive_IsConsensusHalving
import Definitions.Def_ConsensusHalvingItems_Additive_numCuts
import Definitions.Def_ConsensusHalvingItems_Additive_inputSize
import Theorems.Thm_ConsensusHalvingItems_Additive_findSolution_spec
import Theorems.Thm_ConsensusHalvingItems_Additive_loopStep_freezes
import Theorems.Thm_ConsensusHalvingItems_Additive_reachable_invariant
import Theorems.Thm_ConsensusHalvingItems_Additive_card_T_ge_of_unique
import Theorems.Thm_ConsensusHalvingItems_Additive_reachable_step_polytime

set_option autoImplicit false

namespace ConsensusHalvingItems.Additive
namespace RedA74

/-! Tick-shift: every program of the mission returns the same value from every start counter
and adds the same amount to it. -/

def Shift {α : Type} (p : StateM ℕ α) : Prop :=
  ∀ t, (p.run t).1 = (p.run 0).1 ∧ (p.run t).2 = (p.run 0).2 + t

theorem run_bind' {α β : Type} (p : StateM ℕ α) (f : α → StateM ℕ β) (t : ℕ) :
    (p >>= f).run t = (f (p.run t).1).run (p.run t).2 := rfl

theorem shift_pure {α : Type} (a : α) : Shift (pure a : StateM ℕ α) := by
  intro t; exact ⟨rfl, (Nat.zero_add t).symm⟩

theorem shift_tick (c : ℕ) : Shift (tick c) := by
  intro t
  refine ⟨rfl, ?_⟩
  show t + c = (0 + c) + t
  omega

theorem shift_bind {α β : Type} {p : StateM ℕ α} {f : α → StateM ℕ β} (hp : Shift p)
    (hf : ∀ a, Shift (f a)) : Shift (p >>= f) := by
  intro t
  have h1 := hp t
  have h2 := hf (p.run 0).1 ((p.run 0).2 + t)
  have h3 := hf (p.run 0).1 ((p.run 0).2)
  rw [run_bind', run_bind', h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  exact ⟨rfl, by omega⟩

theorem pure_run {α : Type} (a : α) (s : ℕ) : (pure a : StateM ℕ α).run s = (a, s) := rfl

theorem shift_mapM {α β : Type} (f : α → StateM ℕ β) (hf : ∀ a, Shift (f a)) :
    ∀ l : List α, Shift (l.mapM f)
  | [] => by simpa using shift_pure ([] : List β)
  | a :: l => by
    rw [List.mapM_cons]
    exact shift_bind (hf a) fun _ => shift_bind (shift_mapM f hf l) fun _ => shift_pure _

theorem shift_foldlM {α β : Type} (f : β → α → StateM ℕ β) (hf : ∀ b a, Shift (f b a)) :
    ∀ (l : List α) (b : β), Shift (l.foldlM f b)
  | [], b => by simpa using shift_pure b
  | a :: l, b => by
    rw [List.foldlM_cons]
    exact shift_bind (hf b a) fun b' => shift_foldlM f hf l b'

theorem shift_filterMapM {α β : Type} (f : α → StateM ℕ (Option β)) (hf : ∀ a, Shift (f a)) :
    ∀ l : List α, Shift (l.filterMapM f)
  | [] => by simpa using shift_pure ([] : List β)
  | a :: l => by
    rw [List.filterMapM_cons]
    refine shift_bind (hf a) fun o => ?_
    rcases o with _ | b
    · exact shift_filterMapM f hf l
    · exact shift_bind (shift_filterMapM f hf l) fun _ => shift_pure _

theorem shift_qadd (a b : ℚ) : Shift (qadd a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_qsub (a b : ℚ) : Shift (qsub a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_qmul (a b : ℚ) : Shift (qmul a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_qdiv (a b : ℚ) : Shift (qdiv a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_qeq (a b : ℚ) : Shift (qeq a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_qlt (a b : ℚ) : Shift (qlt a b) :=
  shift_bind (shift_tick _) fun _ => shift_pure _
theorem shift_uAt {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) :
    Shift (uAt u i j) :=
  shift_bind (shift_tick _) fun _ => shift_pure _

theorem shift_findPivot (c : ℕ) :
    ∀ l : List (List ℚ), Shift (kernelDir.findPivot c l)
  | [] => by rw [kernelDir.findPivot]; exact shift_pure _
  | r :: rs => by
    rw [kernelDir.findPivot]
    refine shift_bind (shift_tick _) fun _ => shift_bind (shift_qeq _ _) fun z => ?_
    split
    · refine shift_bind (shift_findPivot c rs) fun o => ?_
      rcases o with _ | ⟨p, rest⟩
      · exact shift_pure _
      · exact shift_pure _
    · exact shift_pure _

theorem shift_elim (c : ℕ) (p r : List ℚ) : Shift (kernelDir.elim c p r) := by
  unfold kernelDir.elim
  refine shift_mapM _ (fun ab => ?_) _
  rcases ab with ⟨a, b⟩
  exact shift_bind (shift_tick _) fun _ => shift_bind (shift_qmul _ _) fun _ => shift_qsub _ _

theorem shift_kernelDir {m : ℕ} (rows : List (Fin m → ℚ)) : Shift (kernelDir rows) := by
  unfold kernelDir
  refine shift_bind (shift_mapM _ (fun r => shift_mapM _
    (fun c => shift_bind (shift_tick _) fun _ => shift_pure _) _) _) fun mat => ?_
  refine shift_bind (shift_foldlM _ (fun st c => ?_) _ _) fun st => ?_
  · refine shift_bind (shift_tick _) fun _ => shift_bind (shift_findPivot _ _) fun o => ?_
    rcases o with _ | ⟨p, rest⟩
    · exact shift_pure _
    · refine shift_bind (shift_mapM _ (fun a => shift_bind (shift_tick _) fun _ =>
        shift_qdiv _ _) _) fun p' => ?_
      refine shift_bind (shift_mapM _ (fun qr => ?_) _) fun piv' => ?_
      · rcases qr with ⟨q, r⟩
        exact shift_bind (shift_elim _ _ _) fun _ => shift_pure _
      · exact shift_bind (shift_mapM _ (fun r => shift_elim _ _ _) _) fun _ => shift_pure _
  · refine shift_bind (shift_tick _) fun _ => ?_
    split
    · exact shift_pure _
    · refine shift_bind (shift_mapM _ (fun c => ?_) _) fun _ => shift_pure _
      refine shift_bind (shift_tick _) fun _ => ?_
      split
      · exact shift_pure _
      · split
        · exact shift_qsub _ _
        · exact shift_pure _

theorem shift_findSolution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Shift (findSolution u T x) := by
  unfold findSolution
  refine shift_bind (shift_mapM _ (fun i => shift_bind (shift_mapM _ (fun j => shift_uAt _ _ _) _)
    fun _ => shift_pure _) _) fun urows => ?_
  refine shift_bind (shift_filterMapM _ (fun j => shift_bind (shift_tick _) fun _ =>
    shift_pure _) _) fun trows => ?_
  refine shift_bind (shift_kernelDir _) fun o => ?_
  rcases o with _ | d
  · exact shift_pure _
  · exact shift_bind (shift_mapM _ (fun j => shift_qadd _ _) _) fun _ => shift_pure _

theorem shift_loopStep {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Shift (loopStep u T x) := by
  unfold loopStep
  refine shift_bind (shift_findSolution _ _ _) fun o => ?_
  rcases o with _ | y
  · exact shift_pure _
  · refine shift_bind (shift_foldlM _ (fun acc j => ?_) _ _) fun best => ?_
    · refine shift_bind (shift_tick _) fun _ => shift_bind (shift_qeq _ _) fun same => ?_
      split
      · exact shift_pure _
      · refine shift_bind (shift_qlt _ _) fun up => ?_
        dsimp only
        split
        · refine shift_bind (shift_qsub _ _) fun _ => shift_bind (shift_qsub _ _) fun _ =>
            shift_bind (shift_qdiv _ _) fun g => ?_
          rcases acc with _ | ⟨j0, g0⟩
          · exact shift_pure _
          · exact shift_bind (shift_qlt _ _) fun _ => shift_pure _
        · refine shift_bind (shift_qsub _ _) fun _ => shift_bind (shift_qdiv _ _) fun g => ?_
          rcases acc with _ | ⟨j0, g0⟩
          · exact shift_pure _
          · exact shift_bind (shift_qlt _ _) fun _ => shift_pure _
    · rcases best with _ | ⟨js, g⟩
      · exact shift_pure _
      · refine shift_bind (shift_mapM _ (fun j => ?_) _) fun _ => shift_pure _
        exact shift_bind (shift_tick _) fun _ => shift_bind (shift_qsub _ _) fun _ =>
          shift_bind (shift_qmul _ _) fun _ => shift_bind (shift_qmul _ _) fun _ => shift_qadd _ _

/-! The scan of `loopStep` finds an index as soon as one coordinate differs. -/

theorem tick_run (c s : ℕ) : (tick c).run s = ((), s + c) := rfl
theorem qeq_run (a b : ℚ) (s : ℕ) : (qeq a b).run s = (decide (a = b), s + opCost a b) := rfl
theorem qlt_run (a b : ℚ) (s : ℕ) : (qlt a b).run s = (decide (a < b), s + opCost a b) := rfl
theorem qsub_run (a b : ℚ) (s : ℕ) : (qsub a b).run s = (a - b, s + opCost a b) := rfl
theorem qdiv_run (a b : ℚ) (s : ℕ) : (qdiv a b).run s = (a / b, s + opCost a b) := rfl

theorem ite_some_isSome {α : Type} (c : Bool) (a b : α) :
    (if c = true then some a else some b).isSome = true := by
  cases c <;> rfl

theorem fold_isSome {m : ℕ} {α : Type} (F : Option α → Fin m → StateM ℕ (Option α))
    (P : Fin m → Prop)
    (hF : ∀ acc j s, (acc.isSome = true ∨ P j) → ((F acc j).run s).1.isSome = true) :
    ∀ (l : List (Fin m)) (acc : Option α) (s : ℕ), (acc.isSome = true ∨ ∃ j ∈ l, P j) →
      ((l.foldlM F acc).run s).1.isSome = true
  | [], acc, s, h => by
    rcases h with h | ⟨j, hj, _⟩
    · exact h
    · simp at hj
  | j :: l, acc, s, h => by
    rw [List.foldlM_cons, run_bind']
    by_cases hj : acc.isSome = true ∨ P j
    · exact fold_isSome F P hF l _ _ (Or.inl (hF acc j s hj))
    · refine fold_isSome F P hF l _ _ (Or.inr ?_)
      rcases h with h | ⟨j', hj', hP⟩
      · exact absurd (Or.inl h) hj
      · rcases List.mem_cons.mp hj' with rfl | hl
        · exact absurd (Or.inr hP) hj
        · exact ⟨j', hl, hP⟩

theorem fold_ne_none {m : ℕ} {α : Type} (F : Option α → Fin m → StateM ℕ (Option α))
    (P : Fin m → Prop)
    (hF : ∀ acc j s, (acc.isSome = true ∨ P j) → ((F acc j).run s).1.isSome = true)
    (l : List (Fin m)) (acc : Option α) (s : ℕ) (h : acc.isSome = true ∨ ∃ j ∈ l, P j) :
    ((l.foldlM F acc).run s).1 ≠ none := by
  intro h0
  have := fold_isSome F P hF l acc s h
  rw [h0] at this
  exact absurd this (by simp)

theorem solvesS_of_ch {n m : ℕ} (u : Fin n → Fin m → ℚ) (x : Fin m → ℚ)
    (h : IsConsensusHalving u x) : SolvesS u x := by
  intro i
  have h2 := h.2 i
  unfold additiveUtil at h2
  have e : ∑ j, (x j - 1 / 2) * u i j =
      (∑ j, x j * u i j - ∑ j, (1 - x j) * u i j) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, h2, sub_self, zero_div]

theorem loopStep_none_unique {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (s : ℕ) (hS : SolvesS u x) (h : ((loopStep u T x).run s).1 = none) :
    ∀ y, SolvesST u T x y → y = x := by
  obtain ⟨C, k, hfs⟩ := findSolution_spec
  have hspec := (hfs u T x s).2 hS
  rcases hr : ((findSolution u T x).run s) with ⟨r, s'⟩
  rcases r with _ | y
  · exact hspec.2.mp (by rw [hr])
  · exfalso
    have hyx : y ≠ x := (hspec.1 y (by rw [hr])).1
    obtain ⟨j0, hj0⟩ : ∃ j, y j ≠ x j := by
      by_contra hc
      push Not at hc
      exact hyx (funext hc)
    unfold loopStep at h
    rw [run_bind', hr] at h
    simp only at h
    rw [run_bind'] at h
    split at h
    · rename_i heq
      refine fold_ne_none _ (fun j => y j ≠ x j) ?_ _ _ _
        (Or.inr ⟨j0, List.mem_finRange j0, hj0⟩) heq
      intro acc j s0 hacc
      try dsimp only
      by_cases hj : y j = x j
      · have hacc' : acc.isSome = true := hacc.resolve_right (fun h => h hj)
        have hd : decide (y j = x j) = true := decide_eq_true hj
        simp only [run_bind', tick_run, qeq_run, pure_run, hd, eq_self_iff_true, if_true,
          ite_true]
        exact hacc'
      · have hd : decide (y j = x j) = false := decide_eq_false hj
        by_cases hup : x j < y j
        · have hu : decide (x j < y j) = true := decide_eq_true hup
          rcases acc with _ | ⟨j1, g1⟩ <;>
            simp only [run_bind', tick_run, qeq_run, qlt_run, qsub_run, qdiv_run, pure_run, hd,
              hu, eq_self_iff_true, Bool.false_eq_true, if_true, if_false, ite_true,
              ite_false] <;>
            first | rfl | exact ite_some_isSome _ _ _
        · have hu : decide (x j < y j) = false := decide_eq_false hup
          rcases acc with _ | ⟨j1, g1⟩ <;>
            simp only [run_bind', tick_run, qeq_run, qlt_run, qsub_run, qdiv_run, pure_run, hd,
              hu, eq_self_iff_true, Bool.false_eq_true, if_true, if_false, ite_true,
              ite_false] <;>
            first | rfl | exact ite_some_isSome _ _ _
    · rw [run_bind'] at h
      cases h

theorem halveLoop_none {n m : ℕ} (u : Fin n → Fin m → ℚ) (f : ℕ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (h : ((loopStep u T x).run (t + 1)).1 = none) :
    (halveLoop u (f + 1) T x).run t = (x, ((loopStep u T x).run (t + 1)).2) := by
  rw [halveLoop, run_bind', tick_run]
  dsimp only
  rw [run_bind', h]
  all_goals rfl

theorem halveLoop_some {n m : ℕ} (u : Fin n → Fin m → ℚ) (f : ℕ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (t : ℕ) (T' : Finset (Fin m)) (x' : Fin m → ℚ)
    (h : ((loopStep u T x).run (t + 1)).1 = some (T', x')) :
    (halveLoop u (f + 1) T x).run t = (halveLoop u f T' x').run ((loopStep u T x).run (t + 1)).2 := by
  rw [halveLoop, run_bind', tick_run]
  dsimp only
  rw [run_bind', h]

theorem loop_main {n m : ℕ} (u : Fin n → Fin m → ℚ) (B : ℕ)
    (hB : ∀ T x, Reachable u (T, x) → ∀ t, ((loopStep u T x).run t).2 ≤ t + B) :
    ∀ (f : ℕ) (T : Finset (Fin m)) (x : Fin m → ℚ) (t : ℕ), Reachable u (T, x) →
      m + 1 ≤ f + T.card →
      ∃ T' x' s, Reachable u (T', x') ∧ ((loopStep u T' x').run s).1 = none ∧
        ((halveLoop u f T x).run t).1 = x' ∧ ((halveLoop u f T x).run t).2 ≤ t + f * (B + 1)
  | 0, T, x, t, _, hf => by
    have := Finset.card_le_univ T
    simp only [Fintype.card_fin] at this
    omega
  | f + 1, T, x, t, hR, hf => by
    have hc := hB T x hR (t + 1)
    rcases hr : ((loopStep u T x).run (t + 1)).1 with _ | ⟨T1, x1⟩
    · refine ⟨T, x, t + 1, hR, hr, ?_, ?_⟩
      · rw [halveLoop_none u f T x t hr]
      · rw [halveLoop_none u f T x t hr]
        dsimp only
        nlinarith [Nat.zero_le (f * B), Nat.zero_le f]
    · have hR1 : Reachable u (T1, x1) :=
        Reachable.step hR (by rw [← (shift_loopStep u T x (t + 1)).1, hr])
      have hinv := reachable_invariant u T x hR
      obtain ⟨js, hjs, hT1, -, -⟩ := loopStep_freezes u T x (t + 1) T1 x1 hinv.1 hr
      have hcard : T1.card = T.card + 1 := by
        rw [hT1, Finset.card_insert_of_notMem hjs]
      obtain ⟨T', x', s, h1, h2, h3, h4⟩ :=
        loop_main u B hB f T1 x1 (((loopStep u T x).run (t + 1)).2) hR1 (by omega)
      refine ⟨T', x', s, h1, h2, ?_, ?_⟩
      · rw [halveLoop_some u f T x t T1 x1 hr]
        exact h3
      · rw [halveLoop_some u f T x t T1 x1 hr]
        nlinarith [Nat.zero_le (f * B), Nat.zero_le f]

end RedA74
end ConsensusHalvingItems.Additive

open ConsensusHalvingItems.Additive ConsensusHalvingItems.Additive.RedA74 in
theorem solution :
    ∃ C k : ℕ, ∀ {n m : ℕ} (u : Fin n → Fin m → ℚ),
      IsConsensusHalving u ((halve u).run 0).1 ∧
      numCuts ((halve u).run 0).1 ≤ min n m ∧
      ((halve u).run 0).2 ≤ C * (inputSize u + 1) ^ k := by
  obtain ⟨C, k, hpoly⟩ := reachable_step_polytime
  refine ⟨C + 1, k + 1, fun {n m} u => ?_⟩
  have hI : m ≤ inputSize u := by unfold inputSize; omega
  have hpow : 1 ≤ (inputSize u + 1) ^ k := Nat.one_le_pow _ _ (Nat.succ_pos _)
  by_cases hmn : m ≤ n
  · have hrun : (halve u).run 0 = ((fun _ => (1 / 2 : ℚ)), 0 + (m + 1)) := by
      unfold halve
      rw [if_pos hmn]
      rfl
    rw [hrun]
    refine ⟨⟨fun j => by norm_num, fun i => ?_⟩, ?_, ?_⟩
    · unfold additiveUtil
      exact Finset.sum_congr rfl fun j _ => by norm_num
    · rw [min_eq_right hmn]
      unfold numCuts
      exact (Finset.card_filter_le _ _).trans (by simp)
    · calc 0 + (m + 1) ≤ inputSize u + 1 := by omega
        _ ≤ (inputSize u + 1) ^ (k + 1) := Nat.le_self_pow (by omega) _
        _ ≤ (C + 1) * (inputSize u + 1) ^ (k + 1) := Nat.le_mul_of_pos_left _ (by omega)
  · have hrun : halve u = halveLoop u (m + 1) ∅ (fun _ => 1 / 2) := by
      unfold halve
      rw [if_neg hmn]
    rw [hrun]
    have hB : ∀ T x, Reachable u (T, x) → ∀ t,
        ((loopStep u T x).run t).2 ≤ t + C * (inputSize u + 1) ^ k :=
      fun T x h t => (hpoly u T x h).2 t
    obtain ⟨T', x', s, hR, hnone, hx, hcost⟩ :=
      loop_main u _ hB (m + 1) ∅ _ 0 Reachable.init (by simp)
    rw [hx]
    have hinv := reachable_invariant u T' x' hR
    have hS := solvesS_of_ch u x' hinv.1
    have huniq := loopStep_none_unique u T' x' s hS hnone
    have hcardT := card_T_ge_of_unique u T' x' hS huniq
    refine ⟨hinv.1, ?_, ?_⟩
    · have hsub : (Finset.univ.filter fun j => 0 < x' j ∧ 0 < 1 - x' j) ⊆ T'ᶜ := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [Finset.mem_compl]
        intro hjT
        rcases hinv.2 j hjT with h0 | h1
        · rw [h0] at hj
          exact lt_irrefl _ hj.1
        · rw [h1] at hj
          norm_num at hj
      have h1 : numCuts x' ≤ m - T'.card := by
        unfold numCuts
        refine (Finset.card_le_card hsub).trans ?_
        rw [Finset.card_compl, Fintype.card_fin]
      have h2 : numCuts x' ≤ m := by
        unfold numCuts
        exact (Finset.card_filter_le _ _).trans (by simp)
      exact le_min (by omega) h2
    · have h1 : m + 1 ≤ inputSize u + 1 := by omega
      have h2 : C * (inputSize u + 1) ^ k + 1 ≤ (C + 1) * (inputSize u + 1) ^ k := by
        nlinarith
      calc ((halveLoop u (m + 1) ∅ (fun _ => 1 / 2)).run 0).2
          ≤ 0 + (m + 1) * (C * (inputSize u + 1) ^ k + 1) := hcost
        _ ≤ (inputSize u + 1) * ((C + 1) * (inputSize u + 1) ^ k) := by
          rw [Nat.zero_add]
          exact Nat.mul_le_mul h1 h2
        _ = (C + 1) * (inputSize u + 1) ^ (k + 1) := by ring

