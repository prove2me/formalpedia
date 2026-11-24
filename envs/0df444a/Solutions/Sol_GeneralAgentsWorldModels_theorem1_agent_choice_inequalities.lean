-- Prove2me | solution 1 for GeneralAgentsWorldModels.theorem1_agent_choice_inequalities
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T21:02:25.470317+00:00
-- url     : https://prove2.me/submissions/2010b554-d9e8-41d3-b308-26ead7d16baf

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset Classical

set_option autoImplicit false

universe u v

namespace GeneralAgentsWorldModels


section bnE
variable {S A : Type*} [Fintype S]

/-- Expectation of `f` (a function of the future trajectory segment) over the next `T` states. -/
def bn_E (M : CMP S A) (π : Policy S A) : ℕ → List (S × A) → S → (List (S × A) → ℝ) → ℝ
  | 0, h, x, f => f [(x, π h x)]
  | T + 1, h, x, f => ∑ y, M.P x (π h x) y *
      bn_E M π T (h ++ [(x, π h x)]) y (fun l => f ((x, π h x) :: l))

lemma bn_E_zero (M : CMP S A) (π : Policy S A) (h : List (S × A)) (x : S)
    (f : List (S × A) → ℝ) : bn_E M π 0 h x f = f [(x, π h x)] := rfl

lemma bn_E_succ (M : CMP S A) (π : Policy S A) (T : ℕ) (h : List (S × A)) (x : S)
    (f : List (S × A) → ℝ) : bn_E M π (T + 1) h x f = ∑ y, M.P x (π h x) y *
      bn_E M π T (h ++ [(x, π h x)]) y (fun l => f ((x, π h x) :: l)) := rfl

lemma bn_E_congr_head (M : CMP S A) (π : Policy S A) (T : ℕ) (h : List (S × A)) (x : S)
    (f g : List (S × A) → ℝ) (hfg : ∀ l, f ((x, π h x) :: l) = g ((x, π h x) :: l)) :
    bn_E M π T h x f = bn_E M π T h x g := by
  cases T with
  | zero => exact hfg []
  | succ T =>
    simp only [bn_E_succ]
    have : (fun l => f ((x, π h x) :: l)) = (fun l => g ((x, π h x) :: l)) := funext hfg
    rw [this]

lemma bn_E_mono (M : CMP S A) (π : Policy S A) (T : ℕ) :
    ∀ (h : List (S × A)) (x : S) (f g : List (S × A) → ℝ), (∀ l, f l ≤ g l) →
    bn_E M π T h x f ≤ bn_E M π T h x g := by
  induction T with
  | zero => intro h x f g hfg; exact hfg _
  | succ T ih =>
    intro h x f g hfg
    simp only [bn_E_succ]
    apply sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (ih _ _ _ _ (fun l => hfg _)) (M.nonneg _ _ _)

lemma bn_E_mono_head (M : CMP S A) (π : Policy S A) (T : ℕ) (h : List (S × A)) (x : S)
    (f g : List (S × A) → ℝ) (hfg : ∀ l, f ((x, π h x) :: l) ≤ g ((x, π h x) :: l)) :
    bn_E M π T h x f ≤ bn_E M π T h x g := by
  cases T with
  | zero => exact hfg []
  | succ T =>
    simp only [bn_E_succ]
    apply sum_le_sum
    intro y _
    exact mul_le_mul_of_nonneg_left (bn_E_mono M π T _ _ _ _ (fun l => hfg _)) (M.nonneg _ _ _)

lemma bn_E_const (M : CMP S A) (π : Policy S A) (T : ℕ) :
    ∀ (h : List (S × A)) (x : S) (c : ℝ), bn_E M π T h x (fun _ => c) = c := by
  induction T with
  | zero => intro h x c; rfl
  | succ T ih =>
    intro h x c
    simp only [bn_E_succ, ih, ← sum_mul, M.sum_one, one_mul]

lemma bn_E_sum (M : CMP S A) (π : Policy S A) (T : ℕ) {ι : Type*} (I : Finset ι) :
    ∀ (h : List (S × A)) (x : S) (F : ι → List (S × A) → ℝ),
    bn_E M π T h x (fun l => ∑ i ∈ I, F i l) = ∑ i ∈ I, bn_E M π T h x (F i) := by
  induction T with
  | zero => intro h x F; rfl
  | succ T ih =>
    intro h x F
    simp only [bn_E_succ]
    rw [Finset.sum_comm]
    apply sum_congr rfl
    intro y _
    rw [← mul_sum, ← ih]

lemma bn_E_mul (M : CMP S A) (π : Policy S A) (T : ℕ) :
    ∀ (h : List (S × A)) (x : S) (c : ℝ) (f : List (S × A) → ℝ),
    bn_E M π T h x (fun l => c * f l) = c * bn_E M π T h x f := by
  induction T with
  | zero => intro h x c f; rfl
  | succ T ih =>
    intro h x c f
    simp only [bn_E_succ, ih, mul_sum]
    apply sum_congr rfl
    intro y _
    ring

lemma bn_E_nonneg (M : CMP S A) (π : Policy S A) (T : ℕ) (h : List (S × A)) (x : S)
    (f : List (S × A) → ℝ) (hf : ∀ l, 0 ≤ f l) : 0 ≤ bn_E M π T h x f := by
  have := bn_E_mono M π T h x (fun _ => 0) f hf
  rwa [bn_E_const] at this

lemma bn_E_ext (M : CMP S A) (π : Policy S A) (T : ℕ) :
    ∀ (h : List (S × A)) (x : S) (f g : List (S × A) → ℝ),
    (∀ l y, g l ≤ f (l ++ [y])) → bn_E M π T h x g ≤ bn_E M π (T + 1) h x f := by
  induction T with
  | zero =>
    intro h x f g hfg
    simp only [bn_E_succ, bn_E_zero]
    calc g [(x, π h x)] = ∑ y, M.P x (π h x) y * g [(x, π h x)] := by
          rw [← sum_mul, M.sum_one, one_mul]
      _ ≤ _ := by
          apply sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (hfg _ _) (M.nonneg _ _ _)
  | succ T ih =>
    intro h x f g hfg
    rw [bn_E_succ, bn_E_succ M π (T + 1)]
    apply sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
    exact ih _ _ _ _ (fun l z => by simpa using hfg ((x, π h x) :: l) z)

lemma bn_E_ext_head (M : CMP S A) (π : Policy S A) (T : ℕ) (h : List (S × A)) (x : S)
    (f g : List (S × A) → ℝ)
    (hfg : ∀ l y, g ((x, π h x) :: l) ≤ f ((x, π h x) :: (l ++ [y]))) :
    bn_E M π T h x g ≤ bn_E M π (T + 1) h x f := by
  cases T with
  | zero =>
    simp only [bn_E_succ, bn_E_zero]
    calc g [(x, π h x)] = ∑ y, M.P x (π h x) y * g [(x, π h x)] := by
          rw [← sum_mul, M.sum_one, one_mul]
      _ ≤ _ := by
          apply sum_le_sum
          intro y _
          exact mul_le_mul_of_nonneg_left (hfg [] _) (M.nonneg _ _ _)
  | succ T =>
    rw [bn_E_succ, bn_E_succ M π (T + 1)]
    apply sum_le_sum
    intro y _
    apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
    exact bn_E_ext M π T _ _ _ _ (fun l z => hfg l z)

omit [Fintype S] in
lemma bn_pathPrefix_cons (π : Policy S A) (h : List (S × A)) (x y : S) (ss : List S) :
    pathPrefix π h x (y :: ss) = pathPrefix π (h ++ [(x, π h x)]) y ss := rfl

/-- Bridge between path sums over `Fin T → S` and `bn_E`. -/
lemma bn_sum_path_eq_E (M : CMP S A) (π : Policy S A) (T : ℕ) :
    ∀ (h : List (S × A)) (x : S) (g : List (S × A) → ℝ),
    ∑ ss : Fin T → S, pathWeight M π h x (List.ofFn ss) * g (pathPrefix π h x (List.ofFn ss))
      = bn_E M π T h x (fun l => g (h ++ l)) := by
  induction T with
  | zero =>
    intro h x g
    simp [pathWeight, pathPrefix, bn_E_zero]
  | succ T ih =>
    intro h x g
    rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => S)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]
    rw [bn_E_succ]
    apply sum_congr rfl
    intro y _
    simp only [pathWeight, bn_pathPrefix_cons, mul_assoc, ← mul_sum]
    rw [ih]
    congr 1
    apply congrArg
    funext l
    simp

open Classical in
lemma bn_succProbUpTo_eq (M : CMP S A) (ψ : CompGoal S A) (π : Policy S A) (s₀ : S) (T : ℕ) :
    succProbUpTo M ψ π s₀ T = bn_E M π T [] s₀ (fun l => if Decides ψ l then 1 else 0) := by
  unfold succProbUpTo
  exact (bn_sum_path_eq_E M π T [] s₀ (fun l => if Decides ψ l then 1 else 0)).trans (by simp)

end bnE



section bnScan
variable {S A : Type*}

/-- Scanner of trial outcomes. The phase `true` means the previous element was a visit to `(s,a)`,
so the current state is the outcome of a trial. -/
noncomputable def bn_sc (s : S) (a : A) (s' : S) : Bool → List (S × A) → List Bool
  | _, [] => []
  | ph, e :: l => (if ph then [decide (e.1 = s')] else []) ++ bn_sc s a s' (decide (e = (s, a))) l

/-- The phase after scanning a list. -/
noncomputable def bn_endph (s : S) (a : A) : Bool → List (S × A) → Bool
  | ph, [] => ph
  | _, e :: l => bn_endph s a (decide (e = (s, a))) l

lemma bn_sc_nil (s : S) (a : A) (s' : S) (ph : Bool) : bn_sc s a s' ph [] = [] := by
  cases ph <;> rfl

lemma bn_sc_false_cons (s : S) (a : A) (s' : S) (e : S × A) (l : List (S × A)) :
    bn_sc s a s' false (e :: l) = bn_sc s a s' (decide (e = (s, a))) l := by
  simp [bn_sc]

lemma bn_sc_false_cons_nv (s : S) (a : A) (s' : S) (e : S × A) (l : List (S × A))
    (he : e ≠ (s, a)) : bn_sc s a s' false (e :: l) = bn_sc s a s' false l := by
  simp [bn_sc, he]

lemma bn_sc_false_cons_v (s : S) (a : A) (s' : S) (l : List (S × A)) :
    bn_sc s a s' false ((s, a) :: l) = bn_sc s a s' true l := by
  simp [bn_sc]

lemma bn_sc_true_cons (s : S) (a : A) (s' : S) (e : S × A) (l : List (S × A)) :
    bn_sc s a s' true (e :: l) = decide (e.1 = s') :: bn_sc s a s' false (e :: l) := by
  simp [bn_sc]

lemma bn_sc_append (s : S) (a : A) (s' : S) (l : List (S × A)) :
    ∀ (ph : Bool) (l' : List (S × A)),
    bn_sc s a s' ph (l ++ l') = bn_sc s a s' ph l ++ bn_sc s a s' (bn_endph s a ph l) l' := by
  induction l with
  | nil => intro ph l'; simp [bn_sc_nil, bn_endph]
  | cons e l ih => intro ph l'; simp [bn_sc, bn_endph, ih]

lemma bn_sc_single_length (s : S) (a : A) (s' : S) (ph : Bool) (y : S × A) :
    (bn_sc s a s' ph [y]).length = if ph then 1 else 0 := by
  cases ph <;> simp [bn_sc]

/-- Trial semantics, inductively: `bn_TS τ t o` iff the successive first visits to `(s,a)` from
time `t` exist and their outcomes are `o`. -/
inductive bn_TS (s : S) (a : A) (s' : S) (τ : ℕ → S × A) : ℕ → List Bool → Prop
  | nil (t : ℕ) : bn_TS s a s' τ t []
  | skip (t : ℕ) (c : Bool) (o : List Bool) : τ t ≠ (s, a) → bn_TS s a s' τ (t + 1) (c :: o) →
      bn_TS s a s' τ t (c :: o)
  | hit (t : ℕ) (c : Bool) (o : List Bool) : τ t = (s, a) → ((τ (t + 1)).1 = s' ↔ c = true) →
      bn_TS s a s' τ (t + 1) o → bn_TS s a s' τ t (c :: o)

/-- The goal part after the initial `nowAct`. -/
def bn_tg (s : S) (a : A) (s' : S) (o : List Bool) : SeqGoal S A :=
  o.flatMap fun c => [evVisit s a, nextIn (if c then {s'} else {s'}ᶜ)]

lemma bn_trialSeq_eq (b : A) (s : S) (a : A) (s' : S) (o : List Bool) :
    trialSeq b s a s' o = nowAct b :: bn_tg s a s' o := rfl

lemma bn_seqSat_now (τ : ℕ → S × A) (b : A) (rest : SeqGoal S A) (t : ℕ) :
    seqSat τ (nowAct b :: rest) t ↔ (τ t).2 = b ∧ seqSat τ rest t := by
  simp [seqSat, nowAct]

lemma bn_seqSat_next (τ : ℕ → S × A) (Y : Set S) (rest : SeqGoal S A) (t : ℕ) :
    seqSat τ (nextIn Y :: rest) t ↔ (τ (t + 1)).1 ∈ Y ∧ seqSat τ rest (t + 1) := by
  simp [seqSat, nextIn, opNow, opNext]

lemma bn_seqSat_ev (τ : ℕ → S × A) (s : S) (a : A) (rest : SeqGoal S A) (t : ℕ) :
    seqSat τ (evVisit s a :: rest) t ↔ ∃ u, t ≤ u ∧ (∀ v, t ≤ v → v < u → τ v ≠ (s, a)) ∧
      τ u = (s, a) ∧ seqSat τ rest u := by
  simp [seqSat, evVisit, opNow, opNext, opEventually]

lemma bn_mem_Y (s' x : S) (c : Bool) :
    x ∈ (if c then ({s'} : Set S) else {s'}ᶜ) ↔ (x = s' ↔ c = true) := by
  cases c <;> simp

lemma bn_TS_of_first (s : S) (a : A) (s' : S) (τ : ℕ → S × A) (c : Bool) (o : List Bool) :
    ∀ (d t : ℕ), (∀ v, t ≤ v → v < t + d → τ v ≠ (s, a)) → τ (t + d) = (s, a) →
    ((τ (t + d + 1)).1 = s' ↔ c = true) → bn_TS s a s' τ (t + d + 1) o →
    bn_TS s a s' τ t (c :: o) := by
  intro d
  induction d with
  | zero =>
    intro t _ h1 h2 h3
    exact bn_TS.hit t c o (by simpa using h1) (by simpa using h2) (by simpa using h3)
  | succ d ih =>
    intro t hf h1 h2 h3
    apply bn_TS.skip t c o (hf t le_rfl (by omega))
    apply ih (t + 1) (fun v hv1 hv2 => hf v (by omega) (by omega))
    · rw [show t + 1 + d = t + (d + 1) by omega]; exact h1
    · rw [show t + 1 + d + 1 = t + (d + 1) + 1 by omega]; exact h2
    · rw [show t + 1 + d + 1 = t + (d + 1) + 1 by omega]; exact h3

lemma bn_seqSat_tg_iff (s : S) (a : A) (s' : S) (τ : ℕ → S × A) (o : List Bool) :
    ∀ t, seqSat τ (bn_tg s a s' o) t ↔ bn_TS s a s' τ t o := by
  induction o with
  | nil => intro t; simp [bn_tg, seqSat, bn_TS.nil]
  | cons c o ih =>
    intro t
    have e1 : bn_tg s a s' (c :: o) =
        evVisit s a :: nextIn (if c then {s'} else {s'}ᶜ) :: bn_tg s a s' o := by
      simp [bn_tg]
    rw [e1, bn_seqSat_ev]
    constructor
    · rintro ⟨u, htu, hf, hu, hn⟩
      rw [bn_seqSat_next, bn_mem_Y, ih] at hn
      obtain ⟨d, rfl⟩ : ∃ d, u = t + d := ⟨u - t, by omega⟩
      exact bn_TS_of_first s a s' τ c o d t hf hu hn.1 hn.2
    · intro hT
      -- induction on the inductive predicate
      have key : ∀ t' o', bn_TS s a s' τ t' o' → ∀ c'' o'', o' = c'' :: o'' → o'' = o →
          c'' = c → ∃ u, t' ≤ u ∧ (∀ v, t' ≤ v → v < u → τ v ≠ (s, a)) ∧ τ u = (s, a) ∧
            ((τ (u + 1)).1 = s' ↔ c = true) ∧ bn_TS s a s' τ (u + 1) o := by
        intro t' o' hT'
        induction hT' with
        | nil t'' => intro c'' o'' h; cases h
        | skip t'' c1 o1 hne _ ih2 =>
          intro c'' o'' h1 h2 h3
          obtain ⟨u, hu1, hu2, hu3, hu4, hu5⟩ := ih2 c'' o'' h1 h2 h3
          refine ⟨u, by omega, fun v hv1 hv2 => ?_, hu3, hu4, hu5⟩
          rcases Nat.eq_or_lt_of_le hv1 with h | h
          · subst h; exact hne
          · exact hu2 v (by omega) hv2
        | hit t'' c1 o1 hv hc hrest _ =>
          intro c'' o'' h1 h2 h3
          simp only [List.cons.injEq] at h1
          obtain ⟨rfl, rfl⟩ := h1
          subst h2; subst h3
          exact ⟨t'', le_rfl, fun v h1 h2 => by omega, hv, hc, hrest⟩
      obtain ⟨u, h1, h2, h3, h4, h5⟩ := key t (c :: o) hT c o rfl rfl rfl
      refine ⟨u, h1, h2, h3, ?_⟩
      rw [bn_seqSat_next, bn_mem_Y, ih]
      exact ⟨h4, h5⟩

lemma bn_TS_visit (s : S) (a : A) (s' : S) (τ : ℕ → S × A) (t : ℕ) (o : List Bool)
    (hT : bn_TS s a s' τ t o) (ho : o ≠ []) : ∃ u, t ≤ u ∧ τ u = (s, a) := by
  induction hT with
  | nil t => exact absurd rfl ho
  | skip t c o _ _ ih => obtain ⟨u, h1, h2⟩ := ih (by simp); exact ⟨u, by omega, h2⟩
  | hit t c o hv _ _ _ => exact ⟨t, le_rfl, hv⟩

/-- (K1) a scanned prefix gives the trial semantics. -/
lemma bn_TS_of_prefix (s : S) (a : A) (s' : S) (τ : ℕ → S × A) (L : List (S × A)) :
    ∀ (t : ℕ) (o : List Bool), (∀ i (hi : i < L.length), τ (t + i) = L[i]) →
    o <+: bn_sc s a s' false L → bn_TS s a s' τ t o := by
  induction L with
  | nil =>
    intro t o _ ho
    rw [bn_sc_nil, List.prefix_nil] at ho
    subst ho; exact bn_TS.nil t
  | cons e L ih =>
    intro t o hL ho
    have he : τ t = e := by
        have := hL 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using this
    have hL' : ∀ i (hi : i < L.length), τ (t + 1 + i) = L[i] := by
      intro i hi
      have := hL (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
    by_cases hv : e = (s, a)
    · subst hv
      rw [bn_sc_false_cons_v] at ho
      cases L with
      | nil =>
        rw [bn_sc_nil, List.prefix_nil] at ho
        subst ho; exact bn_TS.nil t
      | cons e' L' =>
        rw [bn_sc_true_cons] at ho
        cases o with
        | nil => exact bn_TS.nil t
        | cons c o =>
          rw [List.cons_prefix_cons] at ho
          have he' : τ (t + 1) = e' := by
            have := hL' 0 (by simp)
            simpa only [Nat.add_zero, List.getElem_cons_zero] using this
          refine bn_TS.hit t c o he ?_ (ih (t + 1) o hL' ho.2)
          rw [he', ho.1]; simp
    · rw [bn_sc_false_cons_nv s a s' e L hv] at ho
      have := ih (t + 1) o hL' ho
      cases o with
      | nil => exact bn_TS.nil t
      | cons c o => exact bn_TS.skip t c o (by rw [he]; exact hv) this

/-- (K2) the trial semantics, with no visit after the window, gives a scanned prefix. -/
lemma bn_prefix_of_TS (s : S) (a : A) (s' : S) (τ : ℕ → S × A) (t : ℕ) (o : List Bool)
    (hT : bn_TS s a s' τ t o) : ∀ (L : List (S × A)), (∀ i (hi : i < L.length), τ (t + i) = L[i]) →
    (∀ i, t + L.length ≤ i + 1 → τ i ≠ (s, a)) → o <+: bn_sc s a s' false L := by
  induction hT with
  | nil t => intro L _ _; exact List.nil_prefix
  | skip t c o hne hT' ih =>
    intro L hL hnv
    cases L with
    | nil =>
      obtain ⟨u, hu1, hu2⟩ := bn_TS_visit s a s' τ _ _ hT' (by simp)
      exact absurd hu2 (hnv u (by simp; omega))
    | cons e L =>
      have he : τ t = e := by
        have := hL 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using this
      have hL' : ∀ i (hi : i < L.length), τ (t + 1 + i) = L[i] := by
        intro i hi
        have := hL (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      rw [← he, bn_sc_false_cons_nv s a s' _ L hne]
      exact ih L hL' (fun i hi => hnv i (by simp at hi ⊢; omega))
  | hit t c o hv hc hT' ih =>
    intro L hL hnv
    match L with
    | [] => exact absurd hv (hnv t (by simp))
    | [e] => exact absurd hv (hnv t (by simp))
    | e :: e' :: L =>
      have he : τ t = e := by
        have := hL 0 (by simp)
        simpa only [Nat.add_zero, List.getElem_cons_zero] using this
      have hL' : ∀ i (hi : i < (e' :: L).length), τ (t + 1 + i) = (e' :: L)[i] := by
        intro i hi
        have := hL (i + 1) (by simp at hi ⊢; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this
      have he' : τ (t + 1) = e' := by
            have := hL' 0 (by simp)
            simpa only [Nat.add_zero, List.getElem_cons_zero] using this
      rw [← he, hv, bn_sc_false_cons_v, bn_sc_true_cons, List.cons_prefix_cons]
      refine ⟨?_, ih (e' :: L) hL' (fun i hi => hnv i (by simp at hi ⊢; omega))⟩
      rw [← he']
      cases c <;> simp_all

end bnScan


section bnUpper
variable {S A : Type*} [Fintype S]

/-- A composite goal `ψ` is a disjunction of trial patterns of length `m`, selected by `G`
according to the first action. -/
def bn_Hyp (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) : Prop :=
  ∀ τ : ℕ → S × A, compSat ψ τ ↔ ∃ f : Fin m → Bool, G (τ 0).2 f ∧ bn_TS s a s' τ 0 (List.ofFn f)

omit [Fintype S] in
lemma bn_decides_of_prefix (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) (hψ : bn_Hyp s a s' ψ m G) (e : S × A) (l : List (S × A))
    (f : Fin m → Bool) (hG : G e.2 f) (hp : List.ofFn f <+: bn_sc s a s' false (e :: l)) :
    Decides ψ (e :: l) := by
  intro τ hτ
  rw [hψ]
  have h0 : τ 0 = e := by
    have := hτ 0 (by simp)
    simpa only [List.getElem_cons_zero] using this
  refine ⟨f, by rw [h0]; exact hG, ?_⟩
  exact bn_TS_of_prefix s a s' τ (e :: l) 0 _ (fun i hi => by rw [Nat.zero_add]; exact hτ i hi) hp

lemma bn_getD_agree {α : Type*} (L : List α) (c : α) :
    ∀ i (hi : i < (L ++ [c]).length), L.getD i c = (L ++ [c])[i] := by
  intro i hi
  by_cases h : i < L.length
  · simp [List.getElem?_eq_getElem h, List.getElem_append_left h]
  · have : i = L.length := by simp at hi; omega
    subst this
    simp

omit [Fintype S] in
lemma bn_prefix_of_decides (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) (hψ : bn_Hyp s a s' ψ m G) (c₀ : S × A) (hc₀ : c₀ ≠ (s, a))
    (e : S × A) (l : List (S × A)) (hD : Decides ψ (e :: l)) (y : S × A) :
    ∃ f : Fin m → Bool, G e.2 f ∧ List.ofFn f <+: bn_sc s a s' false (e :: (l ++ [y])) := by
  set pre := e :: l with hpre_def
  -- the extension of `pre` that never visits `(s,a)` again
  obtain ⟨fc, -, hTc⟩ := (hψ (fun i => pre.getD i c₀)).1 (hD _ (fun i hi => by
    simp [List.getElem?_eq_getElem hi]))
  have hpc : List.ofFn fc <+: bn_sc s a s' false (pre ++ [c₀]) :=
    bn_prefix_of_TS s a s' _ 0 _ hTc (pre ++ [c₀])
      (fun i hi => by rw [Nat.zero_add]; exact bn_getD_agree pre c₀ i hi)
      (fun i hi => by
        rw [List.getD_eq_default _ _ (by simp at hi; omega)]
        exact hc₀)
  have hlen : m ≤ (bn_sc s a s' false (pre ++ [y])).length := by
    have h1 := hpc.length_le
    rw [bn_sc_append] at h1 ⊢
    simpa [List.length_append, bn_sc_single_length] using h1
  obtain ⟨fy, hGy, hTy⟩ := (hψ (fun i => (pre ++ [y]).getD i c₀)).1 (hD _ (fun i hi => by
    simp [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]))
  have h0 : (pre ++ [y]).getD 0 c₀ = e := by simp [hpre_def]
  have hpy : List.ofFn fy <+: bn_sc s a s' false (pre ++ [y] ++ [c₀]) :=
    bn_prefix_of_TS s a s' _ 0 _ hTy (pre ++ [y] ++ [c₀])
      (fun i hi => by rw [Nat.zero_add]; exact bn_getD_agree (pre ++ [y]) c₀ i hi)
      (fun i hi => by
        rw [List.getD_eq_default _ _ (by simp at hi ⊢; omega)]
        exact hc₀)
  have hpre : bn_sc s a s' false (pre ++ [y]) <+: bn_sc s a s' false (pre ++ [y] ++ [c₀]) := by
    rw [bn_sc_append _ _ _ (pre ++ [y])]
    exact List.prefix_append _ _
  refine ⟨fy, by rw [h0] at hGy; exact hGy, ?_⟩
  have := List.prefix_of_prefix_length_le hpy hpre (by simpa using hlen)
  simpa [hpre_def] using this

/-- Weight of an outcome pattern. -/
def bn_w (p : ℝ) : List Bool → ℝ
  | [] => 1
  | c :: o => (if c then p else 1 - p) * bn_w p o

lemma bn_w_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∀ o, 0 ≤ bn_w p o
  | [] => zero_le_one
  | c :: o => by
    have := bn_w_nonneg p hp0 hp1 o
    cases c <;> simp [bn_w] <;> nlinarith

lemma bn_w_le_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∀ o, bn_w p o ≤ 1
  | [] => le_rfl
  | c :: o => by
    have := bn_w_le_one p hp0 hp1 o
    have := bn_w_nonneg p hp0 hp1 o
    cases c <;> simp [bn_w] <;> nlinarith

/-- Indicator that the scanned outcomes start with `o`. -/
noncomputable def bn_ind (s : S) (a : A) (s' : S) (o : List Bool) : List (S × A) → ℝ :=
  fun l => if o <+: bn_sc s a s' false l then 1 else 0

omit [Fintype S] in
lemma bn_ind_nonneg (s : S) (a : A) (s' : S) (o : List Bool) (l : List (S × A)) :
    0 ≤ bn_ind s a s' o l := by
  unfold bn_ind; split_ifs <;> norm_num

omit [Fintype S] in
lemma bn_ind_nil (s : S) (a : A) (s' : S) : bn_ind s a s' ([] : List Bool) = fun _ => 1 := by
  funext l; simp [bn_ind]

lemma bn_E_ind_nv (M : CMP S A) (π : Policy S A) (s : S) (a : A) (s' : S) (T : ℕ)
    (h : List (S × A)) (x : S) (o : List Bool) (hv : (x, π h x) ≠ (s, a)) :
    bn_E M π (T + 1) h x (bn_ind s a s' o) = ∑ y, M.P x (π h x) y *
      bn_E M π T (h ++ [(x, π h x)]) y (bn_ind s a s' o) := by
  rw [bn_E_succ]
  apply sum_congr rfl
  intro y _
  congr 2
  funext l
  simp only [bn_ind, bn_sc_false_cons_nv s a s' _ l hv]

lemma bn_E_ind_v (M : CMP S A) (π : Policy S A) (s : S) (a : A) (s' : S) (T : ℕ)
    (h : List (S × A)) (x : S) (c : Bool) (o : List Bool) (hv : (x, π h x) = (s, a)) :
    bn_E M π (T + 1) h x (bn_ind s a s' (c :: o)) = ∑ y, M.P s a y *
      ((if decide (y = s') = c then 1 else 0) *
        bn_E M π T (h ++ [(s, a)]) y (bn_ind s a s' o)) := by
  rw [bn_E_succ, hv]
  have hx : x = s := congrArg Prod.fst hv
  have ha : π h x = a := congrArg Prod.snd hv
  rw [ha, hx]
  apply sum_congr rfl
  intro y _
  congr 1
  rw [← bn_E_mul]
  apply bn_E_congr_head
  intro l
  simp only [bn_ind, bn_sc_false_cons_v, bn_sc_true_cons, List.cons_prefix_cons]
  by_cases hc : decide (y = s') = c
  · simp [hc]
  · have : ¬ (c = decide (y = s')) := fun h => hc h.symm
    simp [hc, this]

lemma bn_sum_out (M : CMP S A) (s : S) (a : A) (s' : S) (c : Bool) :
    ∑ y, M.P s a y * (if decide (y = s') = c then 1 else 0) =
      if c then M.P s a s' else 1 - M.P s a s' := by
  cases c
  · have : ∀ y, M.P s a y * (if decide (y = s') = false then (1 : ℝ) else 0) =
        M.P s a y - (if y = s' then M.P s a y else 0) := by
      intro y; by_cases hy : y = s' <;> simp [hy]
    simp only [this, sum_sub_distrib, M.sum_one, sum_ite_eq', mem_univ, if_true]
    simp
  · simp [sum_ite_eq']

lemma bn_P_le_one (M : CMP S A) (s : S) (a : A) (s' : S) : M.P s a s' ≤ 1 := by
  rw [← M.sum_one s a]
  exact single_le_sum (fun y _ => M.nonneg s a y) (mem_univ _)

/-- (U) core: under any policy, the probability that the first trials have outcomes `o` is at
most `bn_w p o`. -/
lemma bn_upper_core (M : CMP S A) (s : S) (a : A) (s' : S) (T : ℕ) :
    ∀ (π : Policy S A) (h : List (S × A)) (x : S) (o : List Bool),
    bn_E M π T h x (bn_ind s a s' o) ≤ bn_w (M.P s a s') o := by
  have hp0 := M.nonneg s a s'
  have hp1 := bn_P_le_one M s a s'
  induction T with
  | zero =>
    intro π h x o
    cases o with
    | nil => simp [bn_E_zero, bn_ind, bn_w]
    | cons c o =>
      have : ¬ (c :: o <+: bn_sc s a s' false [(x, π h x)]) := by
        simp [bn_sc_false_cons, bn_sc_nil]
      simp only [bn_E_zero, bn_ind, this, if_false]
      exact bn_w_nonneg _ hp0 hp1 _
  | succ T ih =>
    intro π h x o
    cases o with
    | nil => rw [bn_ind_nil, bn_E_const]; simp [bn_w]
    | cons c o =>
      by_cases hv : (x, π h x) = (s, a)
      · rw [bn_E_ind_v M π s a s' T h x c o hv]
        calc ∑ y, M.P s a y * ((if decide (y = s') = c then 1 else 0) *
              bn_E M π T (h ++ [(s, a)]) y (bn_ind s a s' o))
            ≤ ∑ y, M.P s a y * ((if decide (y = s') = c then 1 else 0) *
              bn_w (M.P s a s') o) := by
              apply sum_le_sum; intro y _
              apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
              apply mul_le_mul_of_nonneg_left (ih _ _ _ _)
              split_ifs <;> norm_num
          _ = bn_w (M.P s a s') (c :: o) := by
              simp only [← mul_assoc, ← sum_mul, bn_sum_out, bn_w]
      · rw [bn_E_ind_nv M π s a s' T h x (c :: o) hv]
        calc ∑ y, M.P x (π h x) y * bn_E M π T (h ++ [(x, π h x)]) y (bn_ind s a s' (c :: o))
            ≤ ∑ y, M.P x (π h x) y * bn_w (M.P s a s') (c :: o) := by
              apply sum_le_sum; intro y _
              exact mul_le_mul_of_nonneg_left (ih _ _ _ _) (M.nonneg _ _ _)
          _ = bn_w (M.P s a s') (c :: o) := by rw [← sum_mul, M.sum_one, one_mul]

/-- (U) for the success probability up to time `T`. -/
lemma bn_succProbUpTo_le (M : CMP S A) (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) (hψ : bn_Hyp s a s' ψ m G) (c₀ : S × A)
    (hc₀ : c₀ ≠ (s, a)) (π : Policy S A) (s₀ : S) (T : ℕ) :
    succProbUpTo M ψ π s₀ T ≤
      ∑ f ∈ univ.filter (fun f => G (π [] s₀) f), bn_w (M.P s a s') (List.ofFn f) := by
  rw [bn_succProbUpTo_eq]
  calc bn_E M π T [] s₀ (fun l => if Decides ψ l then 1 else 0)
      ≤ bn_E M π (T + 1) [] s₀ (fun l => ∑ f ∈ univ.filter (fun f => G (π [] s₀) f),
          bn_ind s a s' (List.ofFn f) l) := by
        apply bn_E_ext_head
        intro l y
        split_ifs with hD
        · obtain ⟨f, hG, hp⟩ := bn_prefix_of_decides s a s' ψ m G hψ c₀ hc₀ _ l hD y
          calc (1 : ℝ) = bn_ind s a s' (List.ofFn f) ((s₀, π [] s₀) :: (l ++ [y])) := by
                simp [bn_ind, hp]
            _ ≤ _ := single_le_sum (f := fun f => bn_ind s a s' (List.ofFn f)
                    ((s₀, π [] s₀) :: (l ++ [y])))
                  (fun f _ => bn_ind_nonneg _ _ _ _ _) (by simpa using hG)
        · exact sum_nonneg (fun f _ => bn_ind_nonneg _ _ _ _ _)
    _ = ∑ f ∈ univ.filter (fun f => G (π [] s₀) f),
          bn_E M π (T + 1) [] s₀ (bn_ind s a s' (List.ofFn f)) := bn_E_sum _ _ _ _ _ _ _
    _ ≤ _ := sum_le_sum (fun f _ => bn_upper_core M s a s' _ _ _ _ _)

lemma bn_succProb_le (M : CMP S A) (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) (hψ : bn_Hyp s a s' ψ m G) (c₀ : S × A)
    (hc₀ : c₀ ≠ (s, a)) (π : Policy S A) (s₀ : S) :
    succProb M ψ π s₀ ≤
      ∑ f ∈ univ.filter (fun f => G (π [] s₀) f), bn_w (M.P s a s') (List.ofFn f) :=
  ciSup_le (fun T => bn_succProbUpTo_le M s a s' ψ m G hψ c₀ hc₀ π s₀ T)

end bnUpper

section bnReach
variable {S A : Type*} [Fintype S]

/-- Probability, under the Markov policy `μ`, of reaching `s` within `k` steps. -/
noncomputable def bn_reach (M : CMP S A) (μ : S → A) (s : S) : ℕ → S → ℝ
  | 0, x => if x = s then 1 else 0
  | k + 1, x => if x = s then 1 else ∑ y, M.P x (μ x) y * bn_reach M μ s k y

lemma bn_reach_s (M : CMP S A) (μ : S → A) (s : S) (k : ℕ) : bn_reach M μ s k s = 1 := by
  cases k <;> simp [bn_reach]

lemma bn_reach_succ_ne (M : CMP S A) (μ : S → A) (s : S) (k : ℕ) (x : S) (hx : x ≠ s) :
    bn_reach M μ s (k + 1) x = ∑ y, M.P x (μ x) y * bn_reach M μ s k y := by
  simp [bn_reach, hx]

lemma bn_reach_bounds (M : CMP S A) (μ : S → A) (s : S) :
    ∀ k x, 0 ≤ bn_reach M μ s k x ∧ bn_reach M μ s k x ≤ 1 := by
  intro k
  induction k with
  | zero => intro x; unfold bn_reach; split_ifs <;> norm_num
  | succ k ih =>
    intro x
    by_cases hx : x = s
    · subst hx; rw [bn_reach_s]; norm_num
    · rw [bn_reach_succ_ne M μ s k x hx]
      constructor
      · exact sum_nonneg (fun y _ => mul_nonneg (M.nonneg _ _ _) (ih y).1)
      · calc ∑ y, M.P x (μ x) y * bn_reach M μ s k y ≤ ∑ y, M.P x (μ x) y * 1 :=
              sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (ih y).2 (M.nonneg _ _ _))
          _ = 1 := by simp [M.sum_one]

lemma bn_one_sub_sum (M : CMP S A) (x : S) (b : A) (r : S → ℝ) :
    1 - ∑ y, M.P x b y * r y = ∑ y, M.P x b y * (1 - r y) := by
  simp only [mul_sub, mul_one, sum_sub_distrib, M.sum_one]

lemma bn_reach_mul (M : CMP S A) (μ : S → A) (s : S) (k' : ℕ) (β : ℝ) (_hβ : 0 ≤ β)
    (hk' : ∀ y, 1 - bn_reach M μ s k' y ≤ β) :
    ∀ k x, 1 - bn_reach M μ s (k + k') x ≤ (1 - bn_reach M μ s k x) * β := by
  intro k
  induction k with
  | zero =>
    intro x
    by_cases hx : x = s
    · subst hx; simp [bn_reach_s]
    · simpa [bn_reach, hx] using hk' x
  | succ k ih =>
    intro x
    by_cases hx : x = s
    · subst hx; simp [bn_reach_s]
    · rw [show k + 1 + k' = (k + k') + 1 by omega, bn_reach_succ_ne M μ s _ x hx,
        bn_reach_succ_ne M μ s _ x hx, bn_one_sub_sum, bn_one_sub_sum, sum_mul]
      apply sum_le_sum
      intro y _
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (ih y) (M.nonneg _ _ _)

/-- Distance-layers to `s`. -/
def bn_Z (M : CMP S A) (s : S) : ℕ → S → Prop
  | 0, y => y = s
  | d + 1, y => bn_Z M s d y ∨ ∃ a' z, 0 < M.P y a' z ∧ bn_Z M s d z

/-- Assumption 1 gives a Markov policy reaching `s` with probability tending to one, uniformly. -/
lemma bn_exists_reach (M : CMP S A) (hC : M.IsCommunicating) (s : S) (a : A) :
    ∃ μ : S → A, μ s = a ∧ ∀ ε > 0, ∃ K, ∀ x, 1 - ε ≤ bn_reach M μ s K x := by
  have hex : ∀ y, ∃ d, bn_Z M s d y := by
    intro y
    by_cases hys : y = s
    · exact ⟨0, hys⟩
    · refine Relation.TransGen.head_induction_on (hC y s hys)
        (motive := fun y _ => ∃ d, bn_Z M s d y) ?_ ?_
      · intro y ⟨a', ha'⟩; exact ⟨1, Or.inr ⟨a', s, ha', rfl⟩⟩
      · intro y z ⟨a', ha'⟩ _ ⟨d, hd⟩; exact ⟨d + 1, Or.inr ⟨a', z, ha', hd⟩⟩
  let dist : S → ℕ := fun y => Nat.find (hex y)
  have hdist : ∀ y, bn_Z M s (dist y) y := fun y => Nat.find_spec (hex y)
  have hdmin : ∀ y d, bn_Z M s d y → dist y ≤ d := fun y d h => Nat.find_min' (hex y) h
  have step : ∀ y, ∃ (a' : A) (z : S), y ≠ s → 0 < M.P y a' z ∧ dist z < dist y := by
    intro y
    by_cases hys : y = s
    · exact ⟨a, s, fun h => absurd hys h⟩
    have h1 := hdist y
    rcases hd : dist y with _ | d
    · rw [hd] at h1; exact absurd h1 hys
    · rw [hd] at h1
      rcases h1 with h1 | ⟨a', z, hpos, hz⟩
      · have := hdmin y d h1; omega
      · exact ⟨a', z, fun _ => ⟨hpos, by have := hdmin z d hz; omega⟩⟩
  choose α ζ hαζ using step
  let μ : S → A := fun y => if y = s then a else α y
  have hμ : ∀ y, y ≠ s → μ y = α y := fun y hy => by simp [μ, hy]
  let g : S → ℝ := fun y => if y = s then 1 else M.P y (α y) (ζ y)
  have hgpos : ∀ y, 0 < g y := by
    intro y; by_cases hy : y = s
    · simp [g, hy]
    · simp only [g, hy, if_false]; exact (hαζ y hy).1
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_min_image univ g ⟨s, mem_univ _⟩
  set q := g y₀ with hq_def
  have hq : 0 < q := hgpos y₀
  have hqg : ∀ y, q ≤ g y := fun y => hy₀ y (mem_univ _)
  have hq1 : q ≤ 1 := by have := hqg s; simpa [g] using this
  have R : ∀ d y, dist y ≤ d → q ^ dist y ≤ bn_reach M μ s d y := by
    intro d
    induction d with
    | zero =>
      intro y hy
      have h0 : dist y = 0 := by omega
      have := hdist y
      rw [h0] at this
      change y = s at this
      subst this
      rw [bn_reach_s, h0]; simp
    | succ d ih =>
      intro y hy
      by_cases hys : y = s
      · subst hys; rw [bn_reach_s]; exact pow_le_one₀ hq.le hq1
      · rw [bn_reach_succ_ne M μ s d y hys, hμ y hys]
        obtain ⟨hpos, hlt⟩ := hαζ y hys
        have hgy : q ≤ M.P y (α y) (ζ y) := by have := hqg y; simpa [g, hys] using this
        have hr := ih (ζ y) (by omega)
        have hr0 := (bn_reach_bounds M μ s d (ζ y)).1
        calc q ^ dist y = q * q ^ (dist y - 1) := by
              rw [← pow_succ']; congr 1; omega
          _ ≤ M.P y (α y) (ζ y) * bn_reach M μ s d (ζ y) := by
              apply mul_le_mul hgy _ (pow_nonneg hq.le _) hpos.le
              calc q ^ (dist y - 1) ≤ q ^ dist (ζ y) :=
                    pow_le_pow_of_le_one hq.le hq1 (by omega)
                _ ≤ _ := hr
          _ ≤ ∑ z, M.P y (α y) z * bn_reach M μ s d z :=
              single_le_sum (f := fun z => M.P y (α y) z * bn_reach M μ s d z)
                (fun z _ => mul_nonneg (M.nonneg _ _ _) (bn_reach_bounds M μ s d z).1)
                (mem_univ _)
  set D := univ.sup dist
  have hD : ∀ y, dist y ≤ D := fun y => Finset.le_sup (f := dist) (mem_univ y)
  set β := 1 - q ^ D
  have hqD : 0 < q ^ D := pow_pos hq D
  have hqD1 : q ^ D ≤ 1 := pow_le_one₀ hq.le hq1
  have hβ0 : 0 ≤ β := by simp only [β]; linarith
  have hβ1 : β < 1 := by simp only [β]; linarith
  have hβD : ∀ y, 1 - bn_reach M μ s D y ≤ β := by
    intro y
    have h1 := R D y (hD y)
    have h2 : q ^ D ≤ q ^ dist y := pow_le_pow_of_le_one hq.le hq1 (hD y)
    simp only [β]; linarith
  have iter : ∀ j y, 1 - bn_reach M μ s (j * D) y ≤ β ^ j := by
    intro j
    induction j with
    | zero => intro y; simp [(bn_reach_bounds M μ s 0 y).1]
    | succ j ih =>
      intro y
      have := bn_reach_mul M μ s (j * D) (β ^ j) (pow_nonneg hβ0 j) ih D y
      rw [show (j + 1) * D = D + j * D by ring]
      calc 1 - bn_reach M μ s (D + j * D) y ≤ (1 - bn_reach M μ s D y) * β ^ j := this
        _ ≤ β * β ^ j := mul_le_mul_of_nonneg_right (hβD y) (pow_nonneg hβ0 j)
        _ = β ^ (j + 1) := by ring
  refine ⟨μ, by simp [μ], fun ε hε => ?_⟩
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε hβ1
  exact ⟨j * D, fun x => by have := iter j x; linarith⟩

end bnReach

section bnLower
variable {S A : Type*} [Fintype S]

lemma bn_sum_out_mul (M : CMP S A) (s : S) (a : A) (s' : S) (c : Bool) (z : ℝ) :
    ∑ y, M.P s a y * ((if decide (y = s') = c then 1 else 0) * z) =
      (if c then M.P s a s' else 1 - M.P s a s') * z := by
  simp only [← mul_assoc, ← sum_mul, bn_sum_out]

/-- (L) core: under a policy that follows the reaching Markov policy `μ` (with `μ s = a`) after the
first step, every pattern has probability close to its weight for large horizons. -/
lemma bn_lower_core (M : CMP S A) (s : S) (a : A) (s' : S) (μ : S → A) (hμ : μ s = a)
    (hreach : ∀ ε > 0, ∃ K, ∀ x, 1 - ε ≤ bn_reach M μ s K x) (π : Policy S A)
    (hπ : ∀ h x, h ≠ [] → π h x = μ x) :
    ∀ m : ℕ, ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, ∀ (o : List Bool), o.length ≤ m → ∀ h x, h ≠ [] →
      bn_w (M.P s a s') o - ε ≤ bn_E M π T h x (bn_ind s a s' o) := by
  have hp0 := M.nonneg s a s'
  have hp1 := bn_P_le_one M s a s'
  intro m
  induction m with
  | zero =>
    intro ε hε
    refine ⟨0, fun T _ o ho h x _ => ?_⟩
    have : o = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [bn_ind_nil, bn_E_const]; simp [bn_w]; linarith
  | succ m ih =>
    intro ε hε
    obtain ⟨T₀', hT₀'⟩ := ih (ε / 2) (by linarith)
    obtain ⟨K, hK⟩ := hreach (ε / 2) (by linarith)
    set ε' := ε / 2 with hε'
    -- at the state `s`, the action is `a`: a trial happens now
    have at_s : ∀ T ≥ T₀' + 1, ∀ (c : Bool) (o : List Bool), o.length ≤ m → ∀ h, h ≠ [] →
        (if c then M.P s a s' else 1 - M.P s a s') * (bn_w (M.P s a s') o - ε') ≤
          bn_E M π T h s (bn_ind s a s' (c :: o)) := by
      intro T hT c o ho h hh
      obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      have hv : (s, π h s) = (s, a) := by rw [hπ h s hh, hμ]
      rw [bn_E_ind_v M π s a s' T' h s c o hv, ← bn_sum_out_mul]
      apply sum_le_sum; intro y _
      apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
      apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> norm_num)
      exact hT₀' T' (by omega) o ho _ y (by simp)
    have layer : ∀ k, ∀ T ≥ T₀' + 1 + k, ∀ (c : Bool) (o : List Bool), o.length ≤ m →
        ∀ h, h ≠ [] → ∀ x,
        (if c then M.P s a s' else 1 - M.P s a s') * (bn_w (M.P s a s') o - ε') *
          bn_reach M μ s k x ≤ bn_E M π T h x (bn_ind s a s' (c :: o)) := by
      intro k
      induction k with
      | zero =>
        intro T hT c o ho h hh x
        by_cases hx : x = s
        · subst hx; simp only [bn_reach, if_true, mul_one]; exact at_s T (by omega) c o ho h hh
        · simp only [bn_reach, hx, if_false, mul_zero]
          exact bn_E_nonneg _ _ _ _ _ _ (bn_ind_nonneg _ _ _ _)
      | succ k ihk =>
        intro T hT c o ho h hh x
        by_cases hx : x = s
        · subst hx; rw [bn_reach_s, mul_one]; exact at_s T (by omega) c o ho h hh
        · obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
          have hv : (x, π h x) ≠ (s, a) := fun h' => hx (congrArg Prod.fst h')
          rw [bn_E_ind_nv M π s a s' T' h x (c :: o) hv, bn_reach_succ_ne M μ s k x hx, mul_sum]
          apply sum_le_sum; intro y _
          rw [hπ h x hh, mul_left_comm]
          apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
          exact ihk T' (by omega) c o ho _ (by simp) y
    refine ⟨T₀' + 1 + K, fun T hT o ho h x hh => ?_⟩
    cases o with
    | nil => rw [bn_ind_nil, bn_E_const]; simp [bn_w]; linarith
    | cons c o =>
      have ho' : o.length ≤ m := by simp at ho; omega
      have h1 := layer K T hT c o ho' h hh x
      have h2 := hK x
      have h3 := bn_reach_bounds M μ s K x
      have h4 : 0 ≤ bn_E M π T h x (bn_ind s a s' (c :: o)) :=
        bn_E_nonneg _ _ _ _ _ _ (bn_ind_nonneg _ _ _ _)
      have hw0 := bn_w_nonneg _ hp0 hp1 o
      have hw1 := bn_w_le_one _ hp0 hp1 o
      set wc := (if c then M.P s a s' else 1 - M.P s a s') with hwc
      have hwc0 : 0 ≤ wc := by rw [hwc]; split_ifs <;> linarith
      have hwc1 : wc ≤ 1 := by rw [hwc]; split_ifs <;> linarith
      have hw : bn_w (M.P s a s') (c :: o) = wc * bn_w (M.P s a s') o := rfl
      rw [hw]
      set r := bn_reach M μ s K x
      set E := bn_E M π T h x (bn_ind s a s' (c :: o))
      set w := bn_w (M.P s a s') o
      by_cases hα : 0 ≤ wc * (w - ε')
      · have k0 : wc * (w - ε') * (1 - ε') ≤ wc * (w - ε') * r :=
          mul_le_mul_of_nonneg_left h2 hα
        have k1 : wc * (w - ε') ≤ 1 := by nlinarith
        have k2 : wc * (w - ε') * ε' ≤ ε' := by nlinarith
        have k3 : wc * ε' ≤ ε' := by nlinarith
        nlinarith
      · have k3 : wc * ε' ≤ ε' := by nlinarith
        nlinarith

end bnLower

section bnFinal
variable {S A : Type*} [Fintype S]

omit [Fintype S] in
lemma bn_sum_ind_le_one (s : S) (a : A) (s' : S) (m : ℕ) (F : Finset (Fin m → Bool))
    (L : List (S × A)) : ∑ f ∈ F, bn_ind s a s' (List.ofFn f) L ≤ 1 := by
  simp only [bn_ind]
  rw [Finset.sum_boole]
  have : (F.filter (fun f => List.ofFn f <+: bn_sc s a s' false L)).card ≤ 1 := by
    apply Finset.card_le_one.2
    intro f hf g hg
    simp only [mem_filter] at hf hg
    apply List.ofFn_injective
    exact List.IsPrefix.eq_of_length (List.prefix_of_prefix_length_le hf.2 hg.2 (by simp))
      (by simp)
  exact_mod_cast this

/-- (L) the success probability of the policy "first `b₀`, then reach `(s,a)` again and again"
is at least the total weight of the patterns selected by `G b₀`. -/
lemma bn_succProb_ge (M : CMP S A) (s : S) (a : A) (s' : S) (ψ : CompGoal S A) (m : ℕ)
    (G : A → (Fin m → Bool) → Prop) (hψ : bn_Hyp s a s' ψ m G) (c₀ : S × A)
    (hc₀ : c₀ ≠ (s, a)) (hC : M.IsCommunicating) (b₀ : A) (s₀ : S) :
    ∃ π : Policy S A, π [] s₀ = b₀ ∧
      ∑ f ∈ univ.filter (fun f => G b₀ f), bn_w (M.P s a s') (List.ofFn f) ≤
        succProb M ψ π s₀ := by
  obtain ⟨μ, hμ, hreach⟩ := bn_exists_reach M hC s a
  let π : Policy S A := fun h x => if h = [] then b₀ else μ x
  have hπ : ∀ h x, h ≠ [] → π h x = μ x := fun h x hh => by simp [π, hh]
  have hπ0 : π [] s₀ = b₀ := by simp [π]
  refine ⟨π, hπ0, ?_⟩
  set F := univ.filter (fun f => G b₀ f) with hF
  set B := ∑ f ∈ F, bn_w (M.P s a s') (List.ofFn f)
  have hp0 := M.nonneg s a s'
  have hp1 := bn_P_le_one M s a s'
  have hbdd : BddAbove (Set.range fun T => succProbUpTo M ψ π s₀ T) :=
    ⟨_, by rintro _ ⟨T, rfl⟩; exact bn_succProbUpTo_le M s a s' ψ m G hψ c₀ hc₀ π s₀ T⟩
  apply le_of_forall_pos_le_add
  intro ε hε
  set ε' := ε / (F.card + 1) with hε'_def
  have hε' : 0 < ε' := div_pos hε (by positivity)
  obtain ⟨T₀, hT₀⟩ := bn_lower_core M s a s' μ hμ hreach π hπ m ε' hε'
  have first : ∀ o : List Bool, o.length ≤ m → bn_w (M.P s a s') o - ε' ≤
      bn_E M π (T₀ + 1) [] s₀ (bn_ind s a s' o) := by
    intro o ho
    by_cases hv : (s₀, π [] s₀) = (s, a)
    · cases o with
      | nil => rw [bn_ind_nil, bn_E_const]; simp [bn_w]; linarith
      | cons c o =>
        rw [bn_E_ind_v M π s a s' T₀ [] s₀ c o hv]
        have ho' : o.length ≤ m := by simp at ho; omega
        have hwc1 : (if c then M.P s a s' else 1 - M.P s a s') ≤ 1 := by
          split_ifs <;> linarith
        have hwc0 : 0 ≤ (if c then M.P s a s' else 1 - M.P s a s') := by
          split_ifs <;> linarith
        calc bn_w (M.P s a s') (c :: o) - ε'
            ≤ (if c then M.P s a s' else 1 - M.P s a s') * (bn_w (M.P s a s') o - ε') := by
              simp only [bn_w]; nlinarith
          _ = ∑ y, M.P s a y * ((if decide (y = s') = c then 1 else 0) *
                (bn_w (M.P s a s') o - ε')) := (bn_sum_out_mul M s a s' c _).symm
          _ ≤ _ := by
              apply sum_le_sum; intro y _
              apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
              apply mul_le_mul_of_nonneg_left _ (by split_ifs <;> norm_num)
              exact hT₀ T₀ le_rfl o ho' _ y (by simp)
    · rw [bn_E_ind_nv M π s a s' T₀ [] s₀ o hv]
      calc bn_w (M.P s a s') o - ε'
          = ∑ y, M.P s₀ (π [] s₀) y * (bn_w (M.P s a s') o - ε') := by
            rw [← sum_mul, M.sum_one, one_mul]
        _ ≤ _ := by
            apply sum_le_sum; intro y _
            apply mul_le_mul_of_nonneg_left _ (M.nonneg _ _ _)
            exact hT₀ T₀ le_rfl o ho _ y (by simp)
  have main : B - F.card * ε' ≤ succProbUpTo M ψ π s₀ (T₀ + 1) := by
    rw [bn_succProbUpTo_eq]
    calc B - F.card * ε' = ∑ f ∈ F, (bn_w (M.P s a s') (List.ofFn f) - ε') := by
          rw [sum_sub_distrib, sum_const, nsmul_eq_mul]
      _ ≤ ∑ f ∈ F, bn_E M π (T₀ + 1) [] s₀ (bn_ind s a s' (List.ofFn f)) :=
          sum_le_sum (fun f _ => first _ (by simp))
      _ = bn_E M π (T₀ + 1) [] s₀ (fun l => ∑ f ∈ F, bn_ind s a s' (List.ofFn f) l) :=
          (bn_E_sum _ _ _ _ _ _ _).symm
      _ ≤ bn_E M π (T₀ + 1) [] s₀ (fun l => if Decides ψ l then 1 else 0) := by
          apply bn_E_mono_head
          intro l
          by_cases hex : ∃ f ∈ F, List.ofFn f <+: bn_sc s a s' false ((s₀, π [] s₀) :: l)
          · obtain ⟨f, hf, hp⟩ := hex
            have hG : G (s₀, π [] s₀).2 f := by
              rw [hF, mem_filter] at hf; simpa [hπ0] using hf.2
            have hD : Decides ψ ((s₀, π [] s₀) :: l) :=
              bn_decides_of_prefix s a s' ψ m G hψ _ l f hG hp
            rw [if_pos hD]
            exact bn_sum_ind_le_one s a s' m F _
          · push Not at hex
            have : ∑ f ∈ F, bn_ind s a s' (List.ofFn f) ((s₀, π [] s₀) :: l) = 0 :=
              sum_eq_zero (fun f hf => by simp [bn_ind, hex f hf])
            rw [this]; split_ifs <;> norm_num
  have hcard : (F.card : ℝ) * ε' ≤ ε := by
    rw [hε'_def, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have := le_ciSup hbdd (T₀ + 1)
  unfold succProb
  linarith

lemma bn_w_ofFn (p : ℝ) : ∀ (m : ℕ) (f : Fin m → Bool),
    bn_w p (List.ofFn f) = ∏ i, (if f i then p else 1 - p) := by
  intro m
  induction m with
  | zero => intro f; simp [bn_w]
  | succ m ih => intro f; rw [List.ofFn_succ, Fin.prod_univ_succ, bn_w, ih]

lemma bn_w_ofFn_eq (p : ℝ) (m : ℕ) (f : Fin m → Bool) :
    bn_w p (List.ofFn f) = p ^ (univ.filter fun i => f i = true).card *
      (1 - p) ^ (m - (univ.filter fun i => f i = true).card) := by
  rw [bn_w_ofFn, Finset.prod_ite, prod_const, prod_const]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun i => f i = true)
  simp only [card_univ, Fintype.card_fin] at this
  congr 2
  omega

/-- Sum of pattern weights over the patterns whose number of successes satisfies `P`. -/
lemma bn_pattern_sum (p : ℝ) (m : ℕ) (P : ℕ → Prop) :
    ∑ f ∈ univ.filter (fun f : Fin m → Bool => P (univ.filter fun i => f i = true).card),
        bn_w p (List.ofFn f) =
      ∑ r ∈ (range (m + 1)).filter P, (m.choose r : ℝ) * p ^ r * (1 - p) ^ (m - r) := by
  rw [sum_filter, sum_filter]
  simp_rw [bn_w_ofFn_eq]
  set g : ℕ → ℝ := fun r => if P r then p ^ r * (1 - p) ^ (m - r) else 0
  have hbij : Function.Bijective
      (fun f : Fin m → Bool => (univ.filter fun i => f i = true)) := by
    constructor
    · intro f g hfg
      funext i
      have := congrArg (fun t => i ∈ t) hfg
      simp only [mem_filter, mem_univ, true_and] at this
      cases hf : f i <;> cases hg : g i <;> simp_all
    · intro t
      exact ⟨fun i => decide (i ∈ t), by ext i; simp⟩
  rw [Fintype.sum_bijective _ hbij _ (fun t => g t.card) (fun f => rfl)]
  rw [← Finset.powerset_univ, Finset.sum_powerset_apply_card]
  simp only [card_univ, Fintype.card_fin]
  apply sum_congr rfl
  intro r _
  simp only [g, nsmul_eq_mul]
  split_ifs <;> ring

lemma bn_total_weight (p : ℝ) (m : ℕ) :
    ∑ f : Fin m → Bool, bn_w p (List.ofFn f) = 1 := by
  simp_rw [bn_w_ofFn]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (c : Bool) => if c then p else 1 - p)]
  simp

omit [Fintype S] in
lemma bn_hyp_binGoal (b : A) (s : S) (a : A) (s' : S) (m : ℕ) (R : ℕ → Prop) :
    bn_Hyp s a s' (binGoal b s a s' m R) m
      (fun b' f => b' = b ∧ R (univ.filter fun i => f i = true).card) := by
  intro τ
  unfold compSat binGoal
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨φ, ⟨f, hR, rfl⟩, hsat⟩
    rw [bn_trialSeq_eq, bn_seqSat_now, bn_seqSat_tg_iff] at hsat
    exact ⟨f, ⟨hsat.1, hR⟩, hsat.2⟩
  · rintro ⟨f, ⟨hb, hR⟩, hT⟩
    exact ⟨_, ⟨f, hR, rfl⟩, by rw [bn_trialSeq_eq, bn_seqSat_now, bn_seqSat_tg_iff]; exact ⟨hb, hT⟩⟩

omit [Fintype S] in
lemma bn_hyp_abGoal (a b : A) (s s' : S) (m k : ℕ) :
    bn_Hyp s a s' (abGoal a b s s' m k) m
      (fun b' f => (b' = a ∧ (univ.filter fun i => f i = true).card ≤ k) ∨
        (b' = b ∧ k < (univ.filter fun i => f i = true).card)) := by
  intro τ
  have happ : ∀ ψ₁ ψ₂ : CompGoal S A, compSat (ψ₁ ++ ψ₂) τ ↔ compSat ψ₁ τ ∨ compSat ψ₂ τ := by
    intro ψ₁ ψ₂; simp only [compSat, List.mem_append, or_and_right, exists_or]
  unfold abGoal
  rw [happ, bn_hyp_binGoal a s a s' m (· ≤ k) τ, bn_hyp_binGoal b s a s' m (k < ·) τ]
  constructor
  · rintro (⟨f, h1, h2⟩ | ⟨f, h1, h2⟩)
    · exact ⟨f, Or.inl h1, h2⟩
    · exact ⟨f, Or.inr h1, h2⟩
  · rintro ⟨f, (h1 | h1), h2⟩
    · exact Or.inl ⟨f, h1, h2⟩
    · exact Or.inr ⟨f, h1, h2⟩

omit [Fintype S] in
lemma bn_tg_length (s : S) (a : A) (s' : S) (o : List Bool) :
    (bn_tg s a s' o).length = 2 * o.length := by
  induction o with
  | nil => simp [bn_tg]
  | cons c o ih => simp only [bn_tg, List.flatMap_cons] at ih ⊢; simp [ih]; ring

end bnFinal

end GeneralAgentsWorldModels

open GeneralAgentsWorldModels in
theorem solution {S : Type u} {A : Type v} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (π : GCPolicy S A) (δ : ℝ) (hδ : δ < 1)
    (n m : ℕ) (hm : 2 * m + 1 ≤ n) (hπ : IsBoundedAgent M π δ n)
    (s s' : S) (a b : A) (hab : a ≠ b) (k : ℕ) (s₀ : S) :
    (π (abGoal a b s s' m k) [] s₀ = a ∨ π (abGoal a b s s' m k) [] s₀ = b) ∧
    (π (abGoal a b s s' m k) [] s₀ = a →
      binGE m (M.P s a s') (k + 1) * (1 - δ) ≤ binLE m (M.P s a s') k) ∧
    (π (abGoal a b s s' m k) [] s₀ = b →
      binLE m (M.P s a s') k * (1 - δ) ≤ binGE m (M.P s a s') (k + 1)) := by
  obtain ⟨a'', ha''⟩ := Fintype.exists_ne_of_one_lt_card (by have := hM.2; omega) a
  have hc₀ : ((s, a'') : S × A) ≠ (s, a) := fun h => ha'' (congrArg Prod.snd h)
  have hψ := bn_hyp_abGoal a b s s' m k
  set ψ := abGoal a b s s' m k with hψdef
  set p := M.P s a s' with hp
  have hp0 : 0 ≤ p := M.nonneg s a s'
  have hp1 : p ≤ 1 := bn_P_le_one M s a s'
  have hw0 : ∀ f : Fin m → Bool, 0 ≤ bn_w p (List.ofFn f) :=
    fun f => bn_w_nonneg _ hp0 hp1 _
  have hLE := (bn_pattern_sum p m (· ≤ k)).trans (show _ = binLE m p k from by
    unfold binLE binPmf
    apply sum_subset
    · intro r hr; simp only [mem_filter, mem_range] at hr ⊢; omega
    · intro r hr hr'
      simp only [mem_filter, mem_range, not_and] at hr hr'
      have : m < r := by
        by_contra hcon
        exact hr' (by omega) (by omega)
      simp [Nat.choose_eq_zero_of_lt this])
  have hGE := (bn_pattern_sum p m (k < ·)).trans (show _ = binGE m p (k + 1) from by
    unfold binGE binPmf
    apply sum_congr _ (fun _ _ => rfl)
    ext r; simp only [mem_filter, mem_range, mem_Icc]; omega)
  have htot : binLE m p k + binGE m p (k + 1) = 1 := by
    rw [← hLE, ← hGE, ← bn_total_weight p m,
      ← sum_filter_add_sum_filter_not univ
        (fun f : Fin m → Bool => (univ.filter fun i => f i = true).card ≤ k)]
    congr 1 <;> exact Finset.sum_congr (by ext f; simp) (fun _ _ => rfl)
  have upper : ∀ π' : Policy S A, succProb M ψ π' s₀ ≤ 1 := by
    intro π'
    refine (bn_succProb_le M s a s' ψ m _ hψ _ hc₀ π' s₀).trans ?_
    rw [← bn_total_weight p m]
    exact sum_le_sum_of_subset_of_nonneg (fun f _ => mem_univ f) (fun f _ _ => hw0 f)
  have hbdd : BddAbove (Set.range fun π' => succProb M ψ π' s₀) :=
    ⟨1, by rintro _ ⟨π', rfl⟩; exact upper π'⟩
  have hoptA : binLE m p k ≤ optProb M ψ s₀ := by
    obtain ⟨π', -, hge⟩ := bn_succProb_ge M s a s' ψ m _ hψ _ hc₀ hM.1 a s₀
    rw [← hLE]
    refine le_trans (le_of_eq ?_) (hge.trans (le_ciSup hbdd π'))
    exact Finset.sum_congr (by ext f; simp [hab]) (fun _ _ => rfl)
  have hoptB : binGE m p (k + 1) ≤ optProb M ψ s₀ := by
    obtain ⟨π', -, hge⟩ := bn_succProb_ge M s a s' ψ m _ hψ _ hc₀ hM.1 b s₀
    rw [← hGE]
    refine le_trans (le_of_eq ?_) (hge.trans (le_ciSup hbdd π'))
    exact Finset.sum_congr (by ext f; simp [Ne.symm hab]) (fun _ _ => rfl)
  have hIn : InPsi n ψ := by
    refine ⟨?_, ?_⟩
    · intro hnil
      have hmem : trialSeq a s a s' (List.ofFn (fun _ : Fin m => false)) ∈ ψ := by
        simp only [hψdef, abGoal, binGoal, List.mem_append, List.mem_map, Finset.mem_toList,
          mem_filter, mem_univ, true_and]
        left; exact ⟨fun _ => false, by simp, rfl⟩
      rw [hnil] at hmem; simp at hmem
    · intro φ hφ
      simp only [hψdef, abGoal, binGoal, List.mem_append, List.mem_map, Finset.mem_toList,
        mem_filter, mem_univ, true_and] at hφ
      obtain ⟨f, -, rfl⟩ | ⟨f, -, rfl⟩ := hφ
      all_goals
        rw [bn_trialSeq_eq]
        refine ⟨List.cons_ne_nil _ _, ?_⟩
        simp only [List.length_cons, bn_tg_length, List.length_ofFn]
        omega
  have hB := hπ.2.2 ψ hIn s₀
  have hU := bn_succProb_le M s a s' ψ m _ hψ _ hc₀ (π ψ) s₀
  have h1δ : 0 < 1 - δ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra hne
    push Not at hne
    have hU0 : succProb M ψ (π ψ) s₀ ≤ 0 := by
      refine hU.trans (le_of_eq (Finset.sum_eq_zero ?_))
      intro f hf
      simp [hne.1, hne.2] at hf
    have hpos : 0 < optProb M ψ s₀ * (1 - δ) := mul_pos (by linarith) h1δ
    linarith
  · intro ha0
    have hU : succProb M ψ (π ψ) s₀ ≤ binLE m p k := hU.trans (le_of_eq (by
      rw [← hLE]; exact Finset.sum_congr (by ext f; simp [ha0, hab]) (fun _ _ => rfl)))
    calc binGE m p (k + 1) * (1 - δ) ≤ optProb M ψ s₀ * (1 - δ) :=
          mul_le_mul_of_nonneg_right hoptB h1δ.le
      _ ≤ succProb M ψ (π ψ) s₀ := hB
      _ ≤ binLE m p k := hU
  · intro hb0
    have hU : succProb M ψ (π ψ) s₀ ≤ binGE m p (k + 1) := hU.trans (le_of_eq (by
      rw [← hGE]; exact Finset.sum_congr (by ext f; simp [hb0, Ne.symm hab]) (fun _ _ => rfl)))
    calc binLE m p k * (1 - δ) ≤ optProb M ψ s₀ * (1 - δ) :=
          mul_le_mul_of_nonneg_right hoptA h1δ.le
      _ ≤ succProb M ψ (π ψ) s₀ := hB
      _ ≤ binGE m p (k + 1) := hU
