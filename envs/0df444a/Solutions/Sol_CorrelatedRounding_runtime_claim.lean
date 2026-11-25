-- Prove2me | solution 1 for CorrelatedRounding.runtime_claim
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:21:44.702297+00:00
-- url     : https://prove2.me/submissions/3f9d8ab4-27de-4793-9ed2-1e826bc77fec

import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.EReal.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_alg1Prog

open LNTopology.Hermetization

namespace CorrelatedRounding.RuntimeSol

theorem forIn_spec {α β : Type} (l : List α) (f : α → β → StateM ℕ (ForInStep β))
    (g : α → β → β) (B : ℕ)
    (h : ∀ x b s, ((f x b).run s).1 = ForInStep.yield (g x b) ∧ ((f x b).run s).2 ≤ s + B) :
    ∀ b s, ((forIn l b f).run s).1 = l.foldl (fun b x => g x b) b ∧
      ((forIn l b f).run s).2 ≤ s + l.length * B := by
  induction l with
  | nil => intro b s; exact ⟨rfl, show s ≤ s + 0 * B by simp⟩
  | cons x l ih =>
    intro b s
    obtain ⟨h1, h2⟩ := h x b s
    obtain ⟨ih1, ih2⟩ := ih (g x b) ((f x b).run s).2
    rw [List.forIn_cons, StateT.run_bind]
    rcases hfx : (f x b).run s with ⟨r, s'⟩
    rw [hfx] at h1 h2 ih1 ih2
    simp only at h1 h2
    subst h1
    simp only [List.foldl_cons, List.length_cons]
    refine ⟨ih1, ?_⟩
    calc _ = (StateT.run (forIn l (g x b) f) s').2 := rfl
      _ ≤ s' + l.length * B := ih2
      _ ≤ s + (l.length + 1) * B := by rw [add_mul]; omega

theorem run_bind' {α β : Type} (m : StateM ℕ α) (f : α → StateM ℕ β) (s : ℕ) :
    (m >>= f).run s = (f (m.run s).1).run (m.run s).2 := rfl

theorem forIn_spec_map {α β γ : Type} (l : List α) (f : α → β → StateM ℕ (ForInStep β))
    (g : α → β → β) (B : ℕ)
    (h : ∀ x b s, ((f x b).run s).1 = ForInStep.yield (g x b) ∧ ((f x b).run s).2 ≤ s + B)
    (b : β) (s : ℕ) (k : β → γ) :
    ((forIn l b f >>= fun r => pure (k r)).run s).1 = k (l.foldl (fun b x => g x b) b) ∧
      ((forIn l b f >>= fun r => pure (k r)).run s).2 ≤ s + l.length * B := by
  rw [run_bind']
  obtain ⟨h1, h2⟩ := forIn_spec l f g B h b s
  exact ⟨congrArg k h1, h2⟩

noncomputable def rowStep {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) (i : Fin q) (m : ℝ) : ℝ :=
  if m ≤ u k i then u k i else m

theorem rowMax_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) (s : ℕ) :
    ((rowMaxProg u k).run s).1 = (List.finRange q).foldl (fun m i => rowStep u k i m) 0 ∧
      ((rowMaxProg u k).run s).2 ≤ s + q * 3 := by
  simp only [rowMaxProg, bind_pure]
  rw [show q * 3 = (List.finRange q).length * 3 by simp]
  refine forIn_spec _ _ (rowStep u k) 3 ?_ 0 s
  intro i m s
  simp [tick, uAt, rle, rowStep]
  split_ifs <;> exact ⟨rfl, show s + 1 + 1 + 1 ≤ s + 3 by omega⟩

noncomputable def rowVal {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) : ℝ :=
  (List.finRange q).foldl (fun m i => rowStep u k i m) 0

theorem yProg_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (s : ℕ) :
    ((yProg u).run s).1 =
      (List.finRange K).foldl (fun ys k => Function.update ys k (rowVal u k)) (fun _ => 0) ∧
      ((yProg u).run s).2 ≤ s + K * (1 + q * 3) := by
  simp only [yProg, bind_pure]
  rw [show K * (1 + q * 3) = (List.finRange K).length * (1 + q * 3) by simp]
  refine forIn_spec _ _ (fun k ys => Function.update ys k (rowVal u k)) _ ?_ _ s
  intro k ys s
  obtain ⟨h1, h2⟩ := rowMax_spec u k (s + 1)
  simp only [tick, run_bind']
  refine ⟨?_, ?_⟩
  · show ForInStep.yield (Function.update ys k ((rowMaxProg u k).run (s + 1)).1) = _
    rw [h1]; rfl
  · show ((rowMaxProg u k).run (s + 1)).2 ≤ _
    omega

theorem drawProg_spec {K : ℕ} (E : Fin K → ℝ) (s : ℕ) :
    ((drawProg E).run s).1 =
      (List.finRange K).foldl (fun es k => Function.update es k (E k)) (fun _ => 0) ∧
      ((drawProg E).run s).2 ≤ s + K * 2 := by
  simp only [drawProg, bind_pure]
  rw [show K * 2 = (List.finRange K).length * 2 by simp]
  refine forIn_spec _ _ (fun k es => Function.update es k (E k)) _ ?_ _ s
  intro k es s
  simp [tick, drawAt]
  exact ⟨rfl, show s + 1 + 1 ≤ s + 2 by omega⟩

noncomputable def amStep {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q)
    (k : Fin K) (best : Option (Fin K × ℝ)) : Option (Fin K × ℝ) :=
  if u k i = 0 then best else
    match best with
    | none => some (k, ys k / u k i * es k)
    | some (k₀, b) => if b ≤ ys k / u k i * es k then some (k₀, b) else some (k, ys k / u k i * es k)

noncomputable def amVal {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q) :
    Option (Fin K × ℝ) :=
  (List.finRange K).foldl (fun b k => amStep u ys es i k b) none

theorem itemArgMin_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q) (s : ℕ) :
    ((itemArgMinProg u ys es i).run s).1 = (amVal u ys es i).map Prod.fst ∧
      ((itemArgMinProg u ys es i).run s).2 ≤ s + K * 6 := by
  simp only [itemArgMinProg]
  rw [show K * 6 = (List.finRange K).length * 6 by simp]
  refine forIn_spec_map _ _ (amStep u ys es i) 6 ?_ none s (Option.map Prod.fst)
  · intro k best s
    simp [tick, uAt, req, rdiv, rmul, rle, amStep]
    split_ifs with h0
    · exact ⟨rfl, show s + 1 + 1 + 1 ≤ s + 6 by omega⟩
    · rcases best with _ | ⟨k₀, b⟩
      · exact ⟨rfl, show s + 1 + 1 + 1 + 1 + 1 ≤ s + 6 by omega⟩
      · exact ⟨rfl, show s + 1 + 1 + 1 + 1 + 1 + 1 ≤ s + 6 by omega⟩

theorem assign_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (s : ℕ) :
    ((assignProg u ys es).run s).1 = (List.finRange q).foldl
      (fun z i => Function.update z i ((amVal u ys es i).map Prod.fst)) (fun _ => none) ∧
      ((assignProg u ys es).run s).2 ≤ s + q * (1 + K * 6) := by
  simp only [assignProg, bind_pure]
  rw [show q * (1 + K * 6) = (List.finRange q).length * (1 + K * 6) by simp]
  refine forIn_spec _ _ (fun i z => Function.update z i ((amVal u ys es i).map Prod.fst)) _ ?_ _ s
  intro i z s
  obtain ⟨h1, h2⟩ := itemArgMin_spec u ys es i (s + 1)
  simp only [tick, run_bind']
  refine ⟨?_, ?_⟩
  · show ForInStep.yield (Function.update z i ((itemArgMinProg u ys es i).run (s + 1)).1) = _
    rw [h1]
  · show ((itemArgMinProg u ys es i).run (s + 1)).2 ≤ _
    omega

theorem alg1_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (E : Fin K → ℝ) :
    ((alg1Prog u E).run 0).1 = (List.finRange q).foldl
      (fun z i => Function.update z i ((amVal u
        ((List.finRange K).foldl (fun ys k => Function.update ys k (rowVal u k)) (fun _ => 0))
        ((List.finRange K).foldl (fun es k => Function.update es k (E k)) (fun _ => 0))
        i).map Prod.fst)) (fun _ => none) ∧
      ((alg1Prog u E).run 0).2 ≤ K * (1 + q * 3) + K * 2 + q * (1 + K * 6) := by
  obtain ⟨y1, y2⟩ := yProg_spec u 0
  obtain ⟨d1, d2⟩ := drawProg_spec E ((yProg u).run 0).2
  obtain ⟨a1, a2⟩ := assign_spec u ((yProg u).run 0).1 ((drawProg E).run ((yProg u).run 0).2).1
    ((drawProg E).run ((yProg u).run 0).2).2
  simp only [alg1Prog, run_bind']
  rw [a1, ← y1, ← d1]
  refine ⟨rfl, ?_⟩
  omega

theorem update_fold {α β : Type} [DecidableEq α] (m : α → β) (l : List α) :
    ∀ (init : α → β) (x : α),
      (l.foldl (fun f k => Function.update f k (m k)) init) x = if x ∈ l then m x else init x := by
  induction l with
  | nil => intro init x; simp
  | cons a l ih =>
    intro init x
    rw [List.foldl_cons, ih]
    by_cases hx : x ∈ l
    · simp [hx]
    · by_cases hxa : x = a
      · subst hxa; simp
      · simp [hx, hxa]

theorem rowFold_inv {q K : ℕ} (u : Fin K → Fin q → ℝ) (k : Fin K) (l : List (Fin q)) :
    ∀ m0 : ℝ, m0 ≤ l.foldl (fun m i => rowStep u k i m) m0 ∧
      (∀ i ∈ l, u k i ≤ l.foldl (fun m i => rowStep u k i m) m0) ∧
      (l.foldl (fun m i => rowStep u k i m) m0 = m0 ∨
        ∃ i ∈ l, l.foldl (fun m i => rowStep u k i m) m0 = u k i) := by
  induction l with
  | nil => intro m0; simp
  | cons a l ih =>
    intro m0
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    obtain ⟨i1, i2, i3⟩ := ih (rowStep u k a m0)
    have ha1 : m0 ≤ rowStep u k a m0 := by
      unfold rowStep; split_ifs with h <;> linarith
    have ha2 : u k a ≤ rowStep u k a m0 := by
      unfold rowStep; split_ifs with h <;> linarith
    refine ⟨le_trans ha1 i1, ⟨le_trans ha2 i1, i2⟩, ?_⟩
    rcases i3 with h | h
    · rw [h]; unfold rowStep; split_ifs with h' <;> simp
    · right; right; exact h

theorem rowVal_eq {q K : ℕ} (u : Fin K → Fin q → ℝ) (hu : IsInstance u) (hq : 1 ≤ q) (k : Fin K) :
    rowVal u k = y u k := by
  have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨i1, i2, i3⟩ := rowFold_inv u k (List.finRange q) 0
  unfold rowVal y
  apply le_antisymm
  · rcases i3 with h | ⟨i, -, h⟩
    · rw [h]
      exact le_trans (hu.1 k ⟨0, hq⟩) (le_ciSup (Finite.bddAbove_range _) _)
    · rw [h]; exact le_ciSup (Finite.bddAbove_range _) _
  · exact ciSup_le fun i => i2 i (List.mem_finRange i)

def AmInv {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q) (l : List (Fin K))
    (best : Option (Fin K × ℝ)) : Prop :=
  (best = none → ∀ k ∈ l, u k i = 0) ∧
  (∀ k₀ b, best = some (k₀, b) → u k₀ i ≠ 0 ∧ b = ys k₀ / u k₀ i * es k₀ ∧
    ∀ k ∈ l, u k i ≠ 0 → b ≤ ys k / u k i * es k)

theorem amInv_step {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q)
    (l : List (Fin K)) (best : Option (Fin K × ℝ)) (x : Fin K) (h : AmInv u ys es i l best) :
    AmInv u ys es i (l ++ [x]) (amStep u ys es i x best) := by
  obtain ⟨hn, hs⟩ := h
  unfold amStep
  by_cases hx : u x i = 0
  · simp only [hx, if_true]
    refine ⟨fun hb k hk => ?_, fun k₀ b hb => ?_⟩
    · rcases List.mem_append.1 hk with hk | hk
      · exact hn hb k hk
      · rw [List.mem_singleton.1 hk]; exact hx
    · obtain ⟨a1, a2, a3⟩ := hs k₀ b hb
      refine ⟨a1, a2, fun k hk hk0 => ?_⟩
      rcases List.mem_append.1 hk with hk | hk
      · exact a3 k hk hk0
      · rw [List.mem_singleton.1 hk] at hk0; exact absurd hx hk0
  · simp only [hx, if_false]
    rcases best with _ | ⟨k₁, b₁⟩
    · refine ⟨fun hb => by simp at hb, fun k₀ b hb => ?_⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl⟩ := hb
      refine ⟨hx, rfl, fun k hk hk0 => ?_⟩
      rcases List.mem_append.1 hk with hk | hk
      · exact absurd (hn rfl k hk) hk0
      · rw [List.mem_singleton.1 hk]
    · obtain ⟨a1, a2, a3⟩ := hs k₁ b₁ rfl
      dsimp only
      refine ⟨fun hb => by split_ifs at hb, fun k₀ b hb => ?_⟩
      split_ifs at hb with hle
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨a1, a2, fun k hk hk0 => ?_⟩
        rcases List.mem_append.1 hk with hk | hk
        · exact a3 k hk hk0
        · rw [List.mem_singleton.1 hk]; exact hle
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        refine ⟨hx, rfl, fun k hk hk0 => ?_⟩
        rcases List.mem_append.1 hk with hk | hk
        · exact le_trans (le_of_lt (not_le.1 hle)) (a3 k hk hk0)
        · rw [List.mem_singleton.1 hk]

theorem amInv_fold {q K : ℕ} (u : Fin K → Fin q → ℝ) (ys es : Fin K → ℝ) (i : Fin q)
    (l : List (Fin K)) : ∀ (l0 : List (Fin K)) (best : Option (Fin K × ℝ)),
    AmInv u ys es i l0 best →
      AmInv u ys es i (l0 ++ l) (l.foldl (fun b k => amStep u ys es i k b) best) := by
  induction l with
  | nil => intro l0 best h; simpa using h
  | cons x l ih =>
    intro l0 best h
    have := ih (l0 ++ [x]) _ (amInv_step u ys es i l0 best x h)
    simpa using this

theorem amVal_spec {q K : ℕ} (u : Fin K → Fin q → ℝ) (hu : IsInstance u) (ys es : Fin K → ℝ)
    (i : Fin q) : ∃ k₀ b, amVal u ys es i = some (k₀, b) ∧ u k₀ i ≠ 0 ∧
      b = ys k₀ / u k₀ i * es k₀ ∧ ∀ k, u k i ≠ 0 → b ≤ ys k / u k i * es k := by
  have H := amInv_fold u ys es i (List.finRange K) [] none ⟨fun _ k hk => by simp at hk,
    fun k₀ b hb => by simp at hb⟩
  simp only [List.nil_append] at H
  obtain ⟨hn, hs⟩ := H
  rcases hb : amVal u ys es i with _ | ⟨k₀, b⟩
  · exfalso
    have hz := hn hb
    have : ∑ k, u k i = 0 := Finset.sum_eq_zero fun k _ => hz k (List.mem_finRange k)
    rw [hu.2 i] at this; exact one_ne_zero this
  · obtain ⟨a1, a2, a3⟩ := hs k₀ b hb
    exact ⟨k₀, b, rfl, a1, a2, fun k hk => a3 k (List.mem_finRange k) hk⟩

end CorrelatedRounding.RuntimeSol

open CorrelatedRounding CorrelatedRounding.RuntimeSol in
theorem solution :
    ∃ C : ℕ, ∀ (q K : ℕ), 1 ≤ q → ∀ (u : Fin K → Fin q → ℝ), IsInstance u → ∀ E : Fin K → ℝ,
      ((alg1Prog u E).run 0).2 ≤ C * q * K ∧
      ∃ z : Fin q → Fin K, (∀ i, ((alg1Prog u E).run 0).1 i = some (z i)) ∧ IsAlg1Output u E z := by
  refine ⟨13, fun q K hq u hu E => ?_⟩
  obtain ⟨h1, h2⟩ := alg1_spec u E
  have hK : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK
      have := hu.2 ⟨0, hq⟩
      simp at this
    · exact hK
  refine ⟨by nlinarith, ?_⟩
  set ys := (List.finRange K).foldl (fun ys k => Function.update ys k (rowVal u k)) (fun _ => 0)
    with hys_def
  set es := (List.finRange K).foldl (fun es k => Function.update es k (E k)) (fun _ => 0)
    with hes_def
  have hys : ∀ k, ys k = y u k := by
    intro k; rw [hys_def, update_fold]; simp [rowVal_eq u hu hq]
  have hes : ∀ k, es k = E k := by
    intro k; rw [hes_def, update_fold]; simp
  have hspec := fun i => amVal_spec u hu ys es i
  choose k₀ b hb hne hbeq hmin using hspec
  refine ⟨k₀, fun i => ?_, fun i k' => ?_⟩
  · rw [h1, update_fold (fun i => (amVal u ys es i).map Prod.fst)]
    simp [hb i]
  · unfold clock
    rw [if_neg (hne i)]
    split_ifs with hk'
    · exact le_top
    · rw [EReal.coe_le_coe_iff, ← hys, ← hes, ← hys, ← hes, ← hbeq i]
      exact hmin i k' hk'
