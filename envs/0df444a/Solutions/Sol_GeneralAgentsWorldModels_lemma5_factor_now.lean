-- Prove2me | solution 1 for GeneralAgentsWorldModels.lemma5_factor_now
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T20:48:46.591609+00:00
-- url     : https://prove2.me/submissions/88a4b34b-2143-4fc2-a2d4-ca885f3398c5

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

set_option autoImplicit false

open Finset

universe u v

namespace GeneralAgentsWorldModels

section fz
variable {S : Type u} {A : Type v} [Fintype S]

/-! ### Path sums with an arbitrary starting history -/

open Classical in
/-- `succProbUpTo` started from an arbitrary history `h`. -/
noncomputable def fz_U (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (h : List (S × A))
    (s : S) (T : ℕ) : ℝ :=
  ∑ ss : Fin T → S, pathWeight M π h s (List.ofFn ss) *
    if Decides ψ (pathPrefix π h s (List.ofFn ss)) then 1 else 0

lemma fz_succProbUpTo_eq (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) (T : ℕ) :
    succProbUpTo M ψ π s T = fz_U M ψ π [] s T := rfl

lemma fz_sum_fin_succ {β : Type*} [AddCommMonoid β] (T : ℕ) (F : List S → β) :
    ∑ ss : Fin (T + 1) → S, F (List.ofFn ss) =
      ∑ s1 : S, ∑ ss : Fin T → S, F (s1 :: List.ofFn ss) := by
  rw [← (Fin.consEquiv fun _ => S).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun s1 _ => sum_congr rfl fun ss _ => ?_
  simp [Fin.consEquiv, List.ofFn_succ]

lemma fz_pathWeight_nonneg (M : CMP S A) (π : Policy S A) :
    ∀ (l : List S) (h : List (S × A)) (s : S), 0 ≤ pathWeight M π h s l
  | [], _, _ => by simp [pathWeight]
  | s' :: l, h, s => by
    simp only [pathWeight]
    exact mul_nonneg (M.nonneg _ _ _) (fz_pathWeight_nonneg M π l _ _)

lemma fz_sum_pathWeight (M : CMP S A) (π : Policy S A) :
    ∀ (T : ℕ) (h : List (S × A)) (s : S),
      ∑ ss : Fin T → S, pathWeight M π h s (List.ofFn ss) = 1
  | 0, h, s => by simp [pathWeight]
  | T + 1, h, s => by
    rw [fz_sum_fin_succ]
    simp only [pathWeight, ← mul_sum, fz_sum_pathWeight M π T, mul_one]
    exact M.sum_one _ _

omit [Fintype S] in
lemma fz_pathPrefix_head (π : Policy S A) :
    ∀ (l : List S) (h : List (S × A)) (s : S),
      ∃ t, pathPrefix π h s l = h ++ (s, π h s) :: t
  | [], h, s => ⟨[], by simp [pathPrefix]⟩
  | s' :: l, h, s => by
    obtain ⟨t, ht⟩ := fz_pathPrefix_head π l (h ++ [(s, π h s)]) s'
    exact ⟨(s', π (h ++ [(s, π h s)]) s') :: t, by simp [pathPrefix, ht]⟩

lemma fz_U_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (h : List (S × A))
    (s : S) (T : ℕ) : 0 ≤ fz_U M ψ π h s T :=
  sum_nonneg fun _ _ => mul_nonneg (fz_pathWeight_nonneg _ _ _ _ _) (by split_ifs <;> norm_num)

lemma fz_U_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (h : List (S × A))
    (s : S) (T : ℕ) : fz_U M ψ π h s T ≤ 1 := by
  rw [← fz_sum_pathWeight M π T h s]
  refine sum_le_sum fun ss _ => ?_
  have := fz_pathWeight_nonneg M π (List.ofFn ss) h s
  split_ifs <;> simp [this]

lemma fz_U_zero (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (h : List (S × A))
    (s : S) [Decidable (Decides ψ (h ++ [(s, π h s)]))] :
    fz_U M ψ π h s 0 = if Decides ψ (h ++ [(s, π h s)]) then 1 else 0 := by
  simp [fz_U, pathWeight, pathPrefix]

open Classical in
lemma fz_U_succ (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (h : List (S × A))
    (s : S) (T : ℕ) :
    fz_U M ψ π h s (T + 1) =
      ∑ s1, M.P s (π h s) s1 * fz_U M ψ π (h ++ [(s, π h s)]) s1 T := by
  unfold fz_U
  rw [fz_sum_fin_succ T (fun l => pathWeight M π h s l *
    if Decides ψ (pathPrefix π h s l) then 1 else 0)]
  simp only [pathWeight, pathPrefix, mul_sum, mul_assoc]
  rfl

omit [Fintype S] in
lemma fz_decides_append (ψ : CompGoal S A) (l l' : List (S × A)) (hd : Decides ψ l) :
    Decides ψ (l ++ l') := by
  intro τ hτ
  apply hd
  intro i hi
  rw [hτ i (by simp; omega), List.getElem_append_left]

lemma fz_U_le_succ (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) :
    ∀ (T : ℕ) (h : List (S × A)) (s : S), fz_U M ψ π h s T ≤ fz_U M ψ π h s (T + 1)
  | 0, h, s => by
    classical
    rw [fz_U_succ, fz_U_zero]
    simp only [fz_U_zero]
    by_cases hd : Decides ψ (h ++ [(s, π h s)])
    · rw [if_pos hd]
      refine le_of_eq ?_
      calc (1:ℝ) = ∑ s1, M.P s (π h s) s1 := (M.sum_one _ _).symm
        _ = _ := sum_congr rfl fun s1 _ => by rw [if_pos (fz_decides_append _ _ _ hd), mul_one]
    · rw [if_neg hd]
      exact sum_nonneg fun s1 _ => mul_nonneg (M.nonneg _ _ _) (by split_ifs <;> norm_num)
  | T + 1, h, s => by
    rw [fz_U_succ, fz_U_succ M ψ π h s (T + 1)]
    exact sum_le_sum fun s1 _ =>
      mul_le_mul_of_nonneg_left (fz_U_le_succ M ψ π T _ _) (M.nonneg _ _ _)

/-! ### `succProb` as a monotone limit -/

lemma fz_succProbUpTo_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S)
    (T : ℕ) : 0 ≤ succProbUpTo M ψ π s T := fz_U_nonneg _ _ _ _ _ _

lemma fz_succProbUpTo_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S)
    (T : ℕ) : succProbUpTo M ψ π s T ≤ 1 := fz_U_le_one _ _ _ _ _ _

lemma fz_succProbUpTo_mono (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    Monotone (succProbUpTo M ψ π s) :=
  monotone_nat_of_le_succ fun T => fz_U_le_succ M ψ π T [] s

lemma fz_bdd (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    BddAbove (Set.range (succProbUpTo M ψ π s)) :=
  ⟨1, by rintro _ ⟨T, rfl⟩; exact fz_succProbUpTo_le_one _ _ _ _ _⟩

lemma fz_le_succProb (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) (T : ℕ) :
    succProbUpTo M ψ π s T ≤ succProb M ψ π s :=
  le_ciSup (fz_bdd M ψ π s) T

lemma fz_succProb_nonneg (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    0 ≤ succProb M ψ π s :=
  (fz_succProbUpTo_nonneg M ψ π s 0).trans (fz_le_succProb M ψ π s 0)

lemma fz_succProb_le_one (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    succProb M ψ π s ≤ 1 :=
  ciSup_le fun T => fz_succProbUpTo_le_one M ψ π s T

lemma fz_tendsto (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s : S) :
    Filter.Tendsto (succProbUpTo M ψ π s) Filter.atTop (nhds (succProb M ψ π s)) :=
  tendsto_atTop_ciSup (fz_succProbUpTo_mono M ψ π s) (fz_bdd M ψ π s)


/-! ### Prefixes, extensions and shifts -/

omit [Fintype S] in
lemma fz_ext_cons (τ : ℕ → S × A) (x : S × A) (l : List (S × A)) :
    (∀ i (hi : i < (x :: l).length), τ i = (x :: l)[i]) ↔
      τ 0 = x ∧ ∀ i (hi : i < l.length), τ (i + 1) = l[i] := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun i hi => h (i + 1) (by simp; omega)⟩
  · rintro ⟨h0, h⟩ i hi
    cases i with
    | zero => simpa using h0
    | succ i => simpa using h i (by simpa using hi)

omit [Fintype S] in
lemma fz_exists_ext (l : List (S × A)) (x : S × A) :
    ∃ τ : ℕ → S × A, ∀ i (hi : i < l.length), τ i = l[i] :=
  ⟨fun i => l.getD i x, fun i hi => by simp [List.getElem?_eq_getElem hi]⟩

omit [Fintype S] in
lemma fz_compSat_single (φ : SeqGoal S A) (τ : ℕ → S × A) :
    compSat [φ] τ ↔ seqSat τ φ 0 := by
  simp [compSat]

omit [Fintype S] in
lemma fz_seqSat_shift (τ : ℕ → S × A) :
    ∀ (φ : SeqGoal S A) (t : ℕ), seqSat τ φ (t + 1) ↔ seqSat (fun i => τ (i + 1)) φ t
  | [], t => by simp [seqSat]
  | φ :: rest, t => by
    simp only [seqSat]
    split_ifs with h1 h2
    · rw [fz_seqSat_shift τ rest t]
    · rw [fz_seqSat_shift τ rest (t + 1)]
    · constructor
      · rintro ⟨u, htu, hv, hu, hr⟩
        obtain ⟨w, rfl⟩ : ∃ w, u = w + 1 := ⟨u - 1, by omega⟩
        exact ⟨w, by omega, fun v hv1 hv2 => hv (v + 1) (by omega) (by omega), hu,
          (fz_seqSat_shift τ rest w).1 hr⟩
      · rintro ⟨w, htw, hv, hu, hr⟩
        refine ⟨w + 1, by omega, fun v hv1 hv2 => ?_, hu, (fz_seqSat_shift τ rest w).2 hr⟩
        obtain ⟨v', rfl⟩ : ∃ v', v = v' + 1 := ⟨v - 1, by omega⟩
        exact hv v' (by omega) (by omega)

omit [Fintype S] in
/-- Two goals that agree on every trajectory through `x` at time `0` are decided by the same
prefixes starting with `x`. -/
lemma fz_decides_congr_head (φ φ' : SeqGoal S A) (x : S × A) (l : List (S × A))
    (H : ∀ τ : ℕ → S × A, τ 0 = x → (seqSat τ φ 0 ↔ seqSat τ φ' 0)) :
    Decides [φ] (x :: l) ↔ Decides [φ'] (x :: l) := by
  unfold Decides
  simp only [fz_compSat_single]
  constructor
  · intro hd τ hτ; exact (H τ ((fz_ext_cons τ x l).1 hτ).1).1 (hd τ hτ)
  · intro hd τ hτ; exact (H τ ((fz_ext_cons τ x l).1 hτ).1).2 (hd τ hτ)

omit [Fintype S] in
/-- A goal that, through `x` at time `0`, reduces to a condition `q` on time `1` and a goal `φ'`
evaluated from time `1`: deciding prefixes shift by one step. -/
lemma fz_decides_shift (φ φ' : SeqGoal S A) (q : S × A → Prop) (x y : S × A)
    (l : List (S × A))
    (H : ∀ τ : ℕ → S × A, τ 0 = x → (seqSat τ φ 0 ↔ (q (τ 1) ∧ seqSat τ φ' 1))) :
    Decides [φ] (x :: y :: l) ↔ (q y ∧ Decides [φ'] (y :: l)) := by
  unfold Decides
  simp only [fz_compSat_single]
  constructor
  · intro hd
    refine ⟨?_, fun τ' hτ' => ?_⟩
    · obtain ⟨τ, hτ⟩ := fz_exists_ext (x :: y :: l) x
      have h0 : τ 0 = x := hτ 0 (by simp)
      have h1 : τ 1 = y := hτ 1 (by simp)
      have := (H τ h0).1 (hd τ hτ)
      rw [h1] at this
      exact this.1
    · let τ : ℕ → S × A := fun n => match n with
        | 0 => x
        | n + 1 => τ' n
      have hτ : ∀ i (hi : i < (x :: y :: l).length), τ i = (x :: y :: l)[i] := by
        rw [fz_ext_cons]; exact ⟨rfl, hτ'⟩
      have := ((H τ rfl).1 (hd τ hτ)).2
      rw [fz_seqSat_shift] at this
      exact this
  · rintro ⟨hq, hd⟩ τ hτ
    rw [fz_ext_cons] at hτ
    obtain ⟨h0, hτ'⟩ := hτ
    rw [H τ h0]
    have h1 : τ 1 = y := hτ' 0 (by simp)
    refine ⟨h1 ▸ hq, ?_⟩
    rw [fz_seqSat_shift]
    exact hd _ hτ'

/-! ### Unfolding the three sub-goal shapes -/

omit [Fintype S] in
lemma fz_seqSat_evVisit (τ : ℕ → S × A) (sg : S) (ag : A) (rest : SeqGoal S A) (t : ℕ) :
    seqSat τ (evVisit sg ag :: rest) t ↔
      ∃ u, t ≤ u ∧ (∀ v, t ≤ v → v < u → τ v ≠ (sg, ag)) ∧ τ u = (sg, ag) ∧
        seqSat τ rest u := by
  simp [seqSat, evVisit, opEventually, opNow, opNext]

omit [Fintype S] in
lemma fz_seqSat_nowAct (τ : ℕ → S × A) (a : A) (rest : SeqGoal S A) :
    seqSat τ (nowAct a :: rest) 0 ↔ (τ 0).2 = a ∧ seqSat τ rest 0 := by
  simp [seqSat, nowAct, opNow]

omit [Fintype S] in
lemma fz_seqSat_nextIn (τ : ℕ → S × A) (g : Set S) (rest : SeqGoal S A) :
    seqSat τ (nextIn g :: rest) 0 ↔ (τ 1).1 ∈ g ∧ seqSat τ rest 1 := by
  simp [seqSat, nextIn, opNow, opNext]

omit [Fintype S] in
lemma fz_seqSat_ev_hit (τ : ℕ → S × A) (sg : S) (ag : A) (rest : SeqGoal S A)
    (h0 : τ 0 = (sg, ag)) : seqSat τ (evVisit sg ag :: rest) 0 ↔ seqSat τ rest 0 := by
  rw [fz_seqSat_evVisit]
  constructor
  · rintro ⟨u, -, hv, hu, hr⟩
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · exact hr
    · exact absurd h0 (hv 0 le_rfl hpos)
  · intro hr
    exact ⟨0, le_rfl, fun v _ h2 => absurd h2 (by omega), h0, hr⟩

omit [Fintype S] in
lemma fz_seqSat_ev_miss (τ : ℕ → S × A) (sg : S) (ag : A) (rest : SeqGoal S A)
    (h0 : τ 0 ≠ (sg, ag)) :
    seqSat τ (evVisit sg ag :: rest) 0 ↔ (True ∧ seqSat τ (evVisit sg ag :: rest) 1) := by
  rw [fz_seqSat_evVisit, fz_seqSat_evVisit, true_and]
  constructor
  · rintro ⟨u, -, hv, hu, hr⟩
    have : u ≠ 0 := by rintro rfl; exact h0 hu
    exact ⟨u, by omega, fun v h1 h2 => hv v (by omega) h2, hu, hr⟩
  · rintro ⟨u, hu1, hv, hu, hr⟩
    refine ⟨u, by omega, fun v _ h2 => ?_, hu, hr⟩
    rcases Nat.eq_zero_or_pos v with rfl | hpos
    · exact h0
    · exact hv v hpos h2

/-! ### Path sums: congruence and Markov policies -/

open Classical in
/-- Goals that agree on trajectories through the first pair `(s, π [] s)` have the same
finite-horizon success probabilities (for any policy). -/
lemma fz_congr_head (M : CMP S A) (π : Policy S A) (φ φ' : SeqGoal S A) (s : S)
    (H : ∀ τ : ℕ → S × A, τ 0 = (s, π [] s) → (seqSat τ φ 0 ↔ seqSat τ φ' 0)) (T : ℕ) :
    succProbUpTo M [φ] π s T = succProbUpTo M [φ'] π s T := by
  unfold succProbUpTo
  refine sum_congr rfl fun ss _ => ?_
  obtain ⟨t, ht⟩ := fz_pathPrefix_head π (List.ofFn ss) [] s
  rw [ht]
  simp only [List.nil_append, fz_decides_congr_head φ φ' _ t H]

lemma fz_pathWeight_markov (M : CMP S A) (μ : S → A) :
    ∀ (l : List S) (h h' : List (S × A)) (s : S),
      pathWeight M (fun _ x => μ x) h s l = pathWeight M (fun _ x => μ x) h' s l
  | [], _, _, _ => rfl
  | s' :: l, h, h', s => by
    simp only [pathWeight]
    rw [fz_pathWeight_markov M μ l _ (h' ++ [(s, μ s)])]

omit [Fintype S] in
lemma fz_pathPrefix_markov (μ : S → A) :
    ∀ (l : List S) (h : List (S × A)) (s : S),
      pathPrefix (fun _ x => μ x) h s l = h ++ pathPrefix (fun _ x => μ x) [] s l
  | [], h, s => by simp [pathPrefix]
  | s' :: l, h, s => by
    simp only [pathPrefix]
    rw [fz_pathPrefix_markov μ l (h ++ _), fz_pathPrefix_markov μ l ([] ++ _)]
    simp

/-- One step of a Markov policy: the success probability over `T + 1` steps is the average,
over the next state, of the path sum from that state with the first pair as history. -/
lemma fz_markov_succ (M : CMP S A) (μ : S → A) (Φ : CompGoal S A) (s : S) (T : ℕ) :
    succProbUpTo M Φ (fun _ y => μ y) s (T + 1) =
      ∑ s1, M.P s (μ s) s1 * fz_U M Φ (fun _ y => μ y) [(s, μ s)] s1 T := by
  rw [fz_succProbUpTo_eq, fz_U_succ]
  rfl

open Classical in
/-- A history of one pair `x` in front of a Markov policy is absorbed into the goal. -/
lemma fz_markov_step (M : CMP S A) (μ : S → A) (Φ Ψ : CompGoal S A) (x : S × A) (s : S)
    (p : Prop) (hD : ∀ l, Decides Φ (x :: (s, μ s) :: l) ↔ (p ∧ Decides Ψ ((s, μ s) :: l)))
    (T : ℕ) :
    fz_U M Φ (fun _ y => μ y) [x] s T =
      if p then succProbUpTo M Ψ (fun _ y => μ y) s T else 0 := by
  rw [fz_succProbUpTo_eq]
  unfold fz_U
  have key : ∀ ss : Fin T → S,
      (pathWeight M (fun _ y => μ y) [x] s (List.ofFn ss) *
        if Decides Φ (pathPrefix (fun _ y => μ y) [x] s (List.ofFn ss)) then 1 else 0) =
      if p then (pathWeight M (fun _ y => μ y) [] s (List.ofFn ss) *
        if Decides Ψ (pathPrefix (fun _ y => μ y) [] s (List.ofFn ss)) then 1 else 0)
      else 0 := by
    intro ss
    rw [fz_pathWeight_markov M μ _ [x] [], fz_pathPrefix_markov μ _ [x]]
    obtain ⟨t, ht⟩ := fz_pathPrefix_head (fun _ y => μ y) (List.ofFn ss) [] s
    rw [ht]
    simp only [List.nil_append, List.singleton_append, hD]
    by_cases hp : p <;> simp [hp]
  simp only [key]
  split_ifs <;> simp

lemma fz_succProbUpTo_nil (M : CMP S A) (π : Policy S A) (s : S) (T : ℕ) :
    succProbUpTo M [[]] π s T = 1 := by
  have hd : ∀ l, Decides ([[]] : CompGoal S A) l := fun l τ _ => by
    rw [fz_compSat_single]; trivial
  unfold succProbUpTo
  simp only [hd, if_true, mul_one]
  exact fz_sum_pathWeight M π T [] s

lemma fz_succProb_nil (M : CMP S A) (π : Policy S A) (s : S) :
    succProb M [[]] π s = 1 := by
  simp [succProb, fz_succProbUpTo_nil]

/-! ### Eventually-visit under a Markov policy (strong Markov property on path sums) -/

lemma fz_ev_hit (M : CMP S A) (μ : S → A) (sg : S) (ag : A) (rest : SeqGoal S A) (s : S)
    (hs : (s, μ s) = (sg, ag)) (T : ℕ) :
    succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s T =
      succProbUpTo M [rest] (fun _ y => μ y) s T :=
  fz_congr_head M _ _ _ s (fun τ h0 => fz_seqSat_ev_hit τ sg ag rest (h0.trans hs)) T

lemma fz_ev_miss_zero (M : CMP S A) (μ : S → A) (sg : S) (ag : A) (rest : SeqGoal S A)
    (s : S) (hs : (s, μ s) ≠ (sg, ag)) :
    succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s 0 = 0 := by
  have hnd : ¬ Decides [evVisit sg ag :: rest] [(s, μ s)] := by
    intro hd
    have := hd (fun _ => (s, μ s)) (fun i hi => by
      simp only [List.length_singleton, Nat.lt_one_iff] at hi; subst hi; rfl)
    rw [fz_compSat_single, fz_seqSat_evVisit] at this
    obtain ⟨u, -, -, hu, -⟩ := this
    exact hs hu
  unfold succProbUpTo
  simp [pathWeight, pathPrefix, hnd]

lemma fz_ev_miss_succ (M : CMP S A) (μ : S → A) (sg : S) (ag : A) (rest : SeqGoal S A)
    (s : S) (hs : (s, μ s) ≠ (sg, ag)) (T : ℕ) :
    succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s (T + 1) =
      ∑ s1, M.P s (μ s) s1 * succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s1 T := by
  rw [fz_markov_succ]
  refine sum_congr rfl fun s1 _ => ?_
  rw [fz_markov_step M μ _ [evVisit sg ag :: rest] (s, μ s) s1 True
    (fun l => fz_decides_shift _ _ (fun _ => True) _ _ l
      (fun τ h0 => fz_seqSat_ev_miss τ sg ag rest (fun h => hs (h0.symm.trans h)))),
    if_pos trivial]

/-- Upper bound: `P_T(◇(sg,ag) then rest) ≤ P_T(◇(sg,ag)) · R` for any bound `R` of `rest` from
`sg`. -/
lemma fz_ev_upper (M : CMP S A) (μ : S → A) (sg : S) (ag : A) (rest : SeqGoal S A) (R : ℝ)
    (hR : ∀ T, succProbUpTo M [rest] (fun _ y => μ y) sg T ≤ R) :
    ∀ T s, succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s T ≤
      succProbUpTo M [[evVisit sg ag]] (fun _ y => μ y) s T * R := by
  have hit : ∀ s, (s, μ s) = (sg, ag) → ∀ T,
      succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s T ≤
        succProbUpTo M [[evVisit sg ag]] (fun _ y => μ y) s T * R := by
    intro s hs T
    rw [fz_ev_hit M μ sg ag rest s hs, fz_ev_hit M μ sg ag [] s hs, fz_succProbUpTo_nil,
      one_mul]
    obtain rfl : s = sg := congrArg Prod.fst hs
    exact hR T
  intro T
  induction T with
  | zero =>
    intro s
    by_cases hs : (s, μ s) = (sg, ag)
    · exact hit s hs 0
    · rw [fz_ev_miss_zero M μ sg ag rest s hs, fz_ev_miss_zero M μ sg ag [] s hs, zero_mul]
  | succ T ih =>
    intro s
    by_cases hs : (s, μ s) = (sg, ag)
    · exact hit s hs _
    · rw [fz_ev_miss_succ M μ sg ag rest s hs, fz_ev_miss_succ M μ sg ag [] s hs, sum_mul]
      exact sum_le_sum fun s1 _ => by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (ih s1) (M.nonneg _ _ _)

/-- Lower bound: `P_T(◇(sg,ag)) · P_K(rest from sg) ≤ P_{T+K}(◇(sg,ag) then rest)`. -/
lemma fz_ev_lower (M : CMP S A) (μ : S → A) (sg : S) (ag : A) (rest : SeqGoal S A) (K : ℕ) :
    ∀ T s, succProbUpTo M [[evVisit sg ag]] (fun _ y => μ y) s T *
        succProbUpTo M [rest] (fun _ y => μ y) sg K ≤
      succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s (T + K) := by
  have hit : ∀ s, (s, μ s) = (sg, ag) → ∀ T,
      succProbUpTo M [[evVisit sg ag]] (fun _ y => μ y) s T *
        succProbUpTo M [rest] (fun _ y => μ y) sg K ≤
      succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s (T + K) := by
    intro s hs T
    rw [fz_ev_hit M μ sg ag rest s hs, fz_ev_hit M μ sg ag [] s hs, fz_succProbUpTo_nil,
      one_mul]
    obtain rfl : s = sg := congrArg Prod.fst hs
    exact fz_succProbUpTo_mono _ _ _ _ (by omega)
  intro T
  induction T with
  | zero =>
    intro s
    by_cases hs : (s, μ s) = (sg, ag)
    · exact hit s hs 0
    · rw [fz_ev_miss_zero M μ sg ag [] s hs, zero_mul]
      exact fz_succProbUpTo_nonneg _ _ _ _ _
  | succ T ih =>
    intro s
    by_cases hs : (s, μ s) = (sg, ag)
    · exact hit s hs _
    · rw [fz_ev_miss_succ M μ sg ag [] s hs, show T + 1 + K = T + K + 1 by omega,
        fz_ev_miss_succ M μ sg ag rest s hs, sum_mul]
      exact sum_le_sum fun s1 _ => by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (ih s1) (M.nonneg _ _ _)

/-- Lemma 3 (factorisation of an almost-sure eventually-visit). -/
theorem fz_factor_eventually (M : CMP S A) (μ : S → A) (sg : S) (ag : A)
    (rest : SeqGoal S A) (s₀ : S)
    (hreach : succProb M [[evVisit sg ag]] (fun _ x => μ x) s₀ = 1) :
    succProb M [evVisit sg ag :: rest] (fun _ x => μ x) s₀ =
      succProb M [rest] (fun _ x => μ x) sg := by
  have hR0 := fz_succProb_nonneg M [rest] (fun _ x => μ x) sg
  apply le_antisymm
  · refine ciSup_le fun T => ?_
    calc _ ≤ succProbUpTo M [[evVisit sg ag]] (fun _ x => μ x) s₀ T *
          succProb M [rest] (fun _ x => μ x) sg :=
          fz_ev_upper M μ sg ag rest _ (fz_le_succProb M [rest] _ sg) T s₀
      _ ≤ 1 * succProb M [rest] (fun _ x => μ x) sg :=
          mul_le_mul_of_nonneg_right (fz_succProbUpTo_le_one _ _ _ _ _) hR0
      _ = _ := one_mul _
  · refine ciSup_le fun K => ?_
    have hK := fz_succProbUpTo_nonneg M [rest] (fun _ x => μ x) sg K
    have : succProbUpTo M [rest] (fun _ x => μ x) sg K =
        ⨆ T, succProbUpTo M [[evVisit sg ag]] (fun _ x => μ x) s₀ T *
          succProbUpTo M [rest] (fun _ x => μ x) sg K := by
      rw [← Real.iSup_mul_of_nonneg hK]
      change _ = succProb M [[evVisit sg ag]] (fun _ x => μ x) s₀ * _
      rw [hreach, one_mul]
    rw [this]
    exact ciSup_le fun T =>
      (fz_ev_lower M μ sg ag rest K T s₀).trans (fz_le_succProb _ _ _ _ _)

/-- Lemma 4 (a `Next` step followed by an almost-sure eventually-visit). -/
theorem fz_factor_next_eventually (M : CMP S A) (μ : S → A) (g₁ : Set S) (sg : S) (ag : A)
    (rest : SeqGoal S A) (s₀ : S)
    (hreach : ∀ x ∈ g₁, succProb M [[evVisit sg ag]] (fun _ y => μ y) x = 1) :
    succProb M [nextIn g₁ :: evVisit sg ag :: rest] (fun _ y => μ y) s₀ =
      (∑ x : S, g₁.indicator (fun y => M.P s₀ (μ s₀) y) x) *
        succProb M [rest] (fun _ y => μ y) sg := by
  classical
  have hstep : ∀ T,
      succProbUpTo M [nextIn g₁ :: evVisit sg ag :: rest] (fun _ y => μ y) s₀ (T + 1) =
        ∑ s1, M.P s₀ (μ s₀) s1 * (if s1 ∈ g₁ then
          succProbUpTo M [evVisit sg ag :: rest] (fun _ y => μ y) s1 T else 0) := by
    intro T
    rw [fz_markov_succ]
    refine sum_congr rfl fun s1 _ => ?_
    rw [fz_markov_step M μ _ [evVisit sg ag :: rest] (s₀, μ s₀) s1 (s1 ∈ g₁)
      (fun l => fz_decides_shift _ _ (fun z => z.1 ∈ g₁) _ _ l
        (fun τ _ => fz_seqSat_nextIn τ g₁ _))]
  have h1 := (fz_tendsto M [nextIn g₁ :: evVisit sg ag :: rest] (fun _ y => μ y) s₀).comp
    (Filter.tendsto_add_atTop_nat 1)
  have h2 : Filter.Tendsto
      (fun T => succProbUpTo M [nextIn g₁ :: evVisit sg ag :: rest] (fun _ y => μ y) s₀ (T + 1))
      Filter.atTop (nhds (∑ s1, M.P s₀ (μ s₀) s1 * (if s1 ∈ g₁ then
          succProb M [evVisit sg ag :: rest] (fun _ y => μ y) s1 else 0))) := by
    simp only [hstep]
    refine tendsto_finsetSum _ fun s1 _ => Filter.Tendsto.const_mul _ ?_
    by_cases h : s1 ∈ g₁
    · simp only [h, if_true]; exact fz_tendsto _ _ _ _
    · simp only [h, if_false]; exact tendsto_const_nhds
  rw [tendsto_nhds_unique h1 h2, sum_mul]
  refine sum_congr rfl fun s1 _ => ?_
  by_cases h : s1 ∈ g₁
  · simp [h, fz_factor_eventually M μ sg ag rest s1 (hreach s1 h)]
  · simp [h]

/-- Lemma 5 (a `Now` sub-goal met by the first action factors out). -/
theorem fz_factor_now (M : CMP S A) (π : Policy S A) (a : A) (rest : SeqGoal S A) (s₀ : S)
    (h₀ : π [] s₀ = a) :
    succProb M [nowAct a :: rest] π s₀ = succProb M [rest] π s₀ := by
  unfold succProb
  congr 1
  funext T
  exact fz_congr_head M π _ _ s₀ (fun τ h0 => by rw [fz_seqSat_nowAct, h0, h₀]; simp) T

end fz

end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (π : Policy S A) (a : A)
    (rest : SeqGoal S A) (s₀ : S) (h₀ : π [] s₀ = a) :
    succProb M [nowAct a :: rest] π s₀ = succProb M [rest] π s₀ :=
  fz_factor_now M π a rest s₀ h₀
