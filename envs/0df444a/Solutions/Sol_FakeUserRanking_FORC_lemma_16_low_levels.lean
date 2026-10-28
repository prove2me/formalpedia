-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_16_low_levels
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T20:11:06.685935+00:00
-- url     : https://prove2.me/submissions/7956ba2b-7a37-494d-8976-d6f1357dfe2c

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolLemma16LowLevels

variable {n L T : ℕ}

lemma foldl_fst (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (acc : List (Fin L × Obs n) × State n L) :
    (l.foldl (fun (acc : List (Fin L × Obs n) × State n L) (x : Fin L × Obs n) =>
      (acc.1 ++ [x], acc.2.update n T (forcRank tb fb acc.1 acc.2 x.1) x.1 x.2)) acc).1
      = acc.1 ++ l := by
  induction l generalizing acc with
  | nil => simp
  | cons x l ih => simp [List.foldl_cons, ih]

lemma forcState_snoc (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) (l : List (Fin L × Obs n))
    (x : Fin L × Obs n) :
    forcState n T tb fb (l ++ [x]) =
      (forcState n T tb fb l).update n T (forcRank tb fb l (forcState n T tb fb l) x.1) x.1 x.2 := by
  unfold forcState
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [foldl_fst]
  simp

lemma forcState_nil (T : ℕ) (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n)) :
    forcState n T tb fb [] = State.init := rfl

lemma algHist_succ {T : ℕ} (τ : Fin T → Step n L) (t : ℕ) (ht : t < T) :
    algHist τ (t + 1) = algHist τ t ++ [((τ ⟨t, ht⟩).1, (τ ⟨t, ht⟩).2.2)] := by
  unfold algHist
  rw [List.take_add_one]
  simp [ht]

lemma stateAt_succ_eq {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) :
    stateAt tb fb τ ((t : ℕ) + 1) =
      (stateAt tb fb τ t).update n T (ranking (forc n T tb fb) τ t) (τ t).1 (τ t).2.2 := by
  unfold stateAt
  rw [algHist_succ τ t t.isLt, forcState_snoc]
  rfl

lemma stateAt_succ {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : ℕ) (ht : t < T) :
    ∃ π, stateAt tb fb τ (t + 1) =
      (stateAt tb fb τ t).update n T π (τ ⟨t, ht⟩).1 (τ ⟨t, ht⟩).2.2 :=
  ⟨ranking (forc n T tb fb) τ ⟨t, ht⟩, stateAt_succ_eq tb fb τ ⟨t, ht⟩⟩

lemma stateAt_zero {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) : stateAt tb fb τ 0 = State.init := by
  unfold stateAt algHist; simp [forcState_nil]

lemma mem_graph_update (T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (k : Fin L) (o : Obs n)
    (g : Fin L) (e : Fin n × Fin n) :
    e ∈ (st.update n T π k o).graph g ↔ e ∈ st.graph g ∨
      (g ∉ st.elim ∧ ∃ m, g ≤ m ∧ m ∉ st.elim ∧ edgeCond n T (st.update n T π k o) m e.1 e.2) := by
  unfold State.update
  by_cases hg : g ∈ st.elim
  · simp [hg]
  · simp only [hg, if_false, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      not_false_eq_true]
    rfl

lemma elim_update (T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (k : Fin L) (o : Obs n)
    (g : Fin L) :
    g ∈ (st.update n T π k o).elim ↔ g ∈ st.elim ∨
      ∃ m, g ≤ m ∧ HasCycle ((st.update n T π k o).graph m) := by
  unfold State.update
  simp

lemma wbound (a b Δ η : ℝ) (ha : 1 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hΔ0 : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hη : 64 * a / Δ ^ 2 ≤ η) :
    Real.sqrt ((3 / 2) * a / η) + (b + 4) / η < Δ / 4 := by
  have hΔ2 : 0 < Δ ^ 2 := by positivity
  have hγ : 0 < 64 * a / Δ ^ 2 := by positivity
  have hη0 : 0 < η := lt_of_lt_of_le hγ hη
  have h64 : 64 * a ≤ η * Δ ^ 2 := by rwa [div_le_iff₀ hΔ2] at hη
  have h1 : (3 / 2) * a / η ≤ (0.154 * Δ) ^ 2 := by
    rw [div_le_iff₀ hη0]; nlinarith
  have h2 : Real.sqrt ((3 / 2) * a / η) ≤ 0.154 * Δ := by
    rw [Real.sqrt_le_left]
    · exact h1
    · positivity
  have h3 : (b + 4) / η ≤ 0.08 * Δ := by
    rw [div_le_iff₀ hη0]; nlinarith
  linarith

lemma window21_le (n T : ℕ) (st : State n L) (k : Fin L) (i : Fin n)
    (hA : 0 ≤ Real.log (4 * n * T / delta n T)) (hB : 0 ≤ Real.log (2 * L / delta n T) + 4)
    (hη : 0 < etaHat st k i) : window21 n T st k i ≤ window n T st k i := by
  unfold window21 window
  have hle : etaHat st k i ≤ max (etaHat st k i) 1 := le_max_left _ _
  apply add_le_add
  · apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_left (by positivity) hη hle
  · exact div_le_div_of_nonneg_left hB hη hle

lemma not_hasCycle (G : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.2 < e.1) : ¬ HasCycle G := by
  rintro ⟨i, h⟩
  have key : ∀ a b, Relation.TransGen (fun a b => (a, b) ∈ G) a b → b < a := by
    intro a b h
    induction h with
    | single h => exact hG _ h
    | tail _ h ih => exact lt_trans (hG _ h) ih
  exact lt_irrefl _ (key _ _ h)

def Inv (F : ℕ) (st : State n L) : Prop :=
  ∀ g : Fin L, F ≤ 2 ^ ((g : ℕ) + 1) → g ∉ st.elim ∧ ∀ e ∈ st.graph g, e.2 < e.1

def GoodSt (n T : ℕ) (inst : Instance n) (F : ℕ) (st : State n L) : Prop :=
  ∀ m : Fin L, F ≤ 2 ^ ((m : ℕ) + 1) → ∀ i : Fin n,
    rHat st m i - window21 n T st m i ≤ inst.μ i ∧ inst.μ i ≤ rHat st m i + window21 n T st m i

lemma edge_correct (T F : ℕ) (inst : Instance n) (hμ : StrictAnti inst.μ) (st : State n L)
    (hA : 0 ≤ Real.log (4 * n * T / delta n T)) (hB : 0 ≤ Real.log (2 * L / delta n T) + 4)
    (hgood : GoodSt n T inst F st) (m : Fin L) (hm : F ≤ 2 ^ ((m : ℕ) + 1)) (a b : Fin n)
    (he : edgeCond n T st m a b) : b < a := by
  obtain ⟨ha, hb, hlt⟩ := he
  have h1 := window21_le n T st m a hA hB ha
  have h2 := window21_le n T st m b hA hB hb
  have g1 := (hgood m hm a).2
  have g2 := (hgood m hm b).1
  have : inst.μ a < inst.μ b := by linarith
  exact lt_of_not_ge (fun h => (not_lt.mpr (hμ.antitone h)) this)

lemma inv_update (T F : ℕ) (inst : Instance n) (hμ : StrictAnti inst.μ) (st : State n L)
    (π : Equiv.Perm (Fin n)) (k : Fin L) (o : Obs n)
    (hA : 0 ≤ Real.log (4 * n * T / delta n T)) (hB : 0 ≤ Real.log (2 * L / delta n T) + 4)
    (hinv : Inv F st) (hgood : GoodSt n T inst F (st.update n T π k o)) :
    Inv F (st.update n T π k o) := by
  have hedges : ∀ g : Fin L, F ≤ 2 ^ ((g : ℕ) + 1) →
      ∀ e ∈ (st.update n T π k o).graph g, e.2 < e.1 := by
    intro g hg e he
    rcases (mem_graph_update T st π k o g e).mp he with h | ⟨_, m, hgm, _, hc⟩
    · exact (hinv g hg).2 e h
    · have hm : F ≤ 2 ^ ((m : ℕ) + 1) :=
        le_trans hg (Nat.pow_le_pow_right (by norm_num) (by have := Fin.le_def.mp hgm; omega))
      exact edge_correct T F inst hμ _ hA hB hgood m hm e.1 e.2 hc
  intro g hg
  refine ⟨?_, hedges g hg⟩
  rw [elim_update]
  rintro (h | ⟨m, hgm, hc⟩)
  · exact (hinv g hg).1 h
  · have hm : F ≤ 2 ^ ((m : ℕ) + 1) :=
      le_trans hg (Nat.pow_le_pow_right (by norm_num) (by have := Fin.le_def.mp hgm; omega))
    exact not_hasCycle _ (hedges m hm) hc

def InvLow (kStar : Fin L) (st : State n L) : Prop :=
  ∀ g : Fin L, g ≤ kStar → g ∉ st.elim →
    ¬ HasCycle (st.graph g) ∧ st.graph kStar ⊆ st.graph g

lemma invLow_init (kStar : Fin L) : InvLow kStar (State.init : State n L) := by
  intro g _ _
  refine ⟨?_, Finset.Subset.refl _⟩
  rintro ⟨i, h⟩
  cases h with
  | single h => simp [State.init] at h
  | tail _ h => simp [State.init] at h

lemma invLow_update (T : ℕ) (kStar : Fin L) (st : State n L)
    (π : Equiv.Perm (Fin n)) (k : Fin L) (o : Obs n)
    (hlow : InvLow kStar st) : InvLow kStar (st.update n T π k o) := by
  intro g hgk hnelim
  have hnelim' : g ∉ st.elim ∧ ¬ ∃ m, g ≤ m ∧ HasCycle ((st.update n T π k o).graph m) := by
    have := (elim_update T st π k o g).not.mp hnelim
    tauto
  have hno_cyc : ¬ HasCycle ((st.update n T π k o).graph g) := by
    intro hcyc
    exact hnelim'.2 ⟨g, le_rfl, hcyc⟩
  refine ⟨hno_cyc, ?_⟩
  intro e he
  rcases (mem_graph_update T st π k o kStar e).mp he with he_old | ⟨_, m, hkSm, hm_el, hec⟩
  · have he_g : e ∈ st.graph g := (hlow g hgk hnelim'.1).2 he_old
    exact (mem_graph_update T st π k o g e).mpr (Or.inl he_g)
  · exact (mem_graph_update T st π k o g e).mpr
      (Or.inr ⟨hnelim'.1, m, le_trans hgk hkSm, hm_el, hec⟩)

lemma log_facts (n T : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T) :
    1 ≤ Real.log (4 * n * T / delta n T) ∧ 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) ∧
    Real.log (2 * (numLevels T : ℝ) / delta n T) ≤ Real.log (4 * n * T / delta n T) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hL1 : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hLT : numLevels T ≤ T := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hL1' : (1 : ℝ) ≤ numLevels T := by exact_mod_cast hL1
  have hLT' : (numLevels T : ℝ) ≤ T := by exact_mod_cast hLT
  have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
    unfold delta; field_simp
  have e2 : 2 * (numLevels T : ℝ) / delta n T = 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 * T := by
    unfold delta; field_simp
  rw [e1, e2]
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn'
  have hn4 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn'
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
    have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hexp1 : Real.exp 1 ≤ 4 := by
    have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  refine ⟨?_, ?_, ?_⟩
  · have : Real.exp 1 ≤ 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by nlinarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  · apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 := by nlinarith
    nlinarith
  · apply Real.log_le_log (by positivity)
    have h1 : (n : ℝ) ^ 3 ≤ (n : ℝ) ^ 4 := by nlinarith
    have h2 : 2 * (numLevels T : ℝ) * T ≤ 4 * (T : ℝ) ^ 2 := by nlinarith
    calc 2 * (numLevels T : ℝ) * (n : ℝ) ^ 3 * T = (n : ℝ) ^ 3 * (2 * (numLevels T : ℝ) * T) := by ring
      _ ≤ (n : ℝ) ^ 4 * (4 * (T : ℝ) ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring

lemma edge_add (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T) (inst : Instance n)
    (hμ : StrictAnti inst.μ) (st : State n (numLevels T))
    (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) (hgood : GoodSt n T inst F st)
    (j i : Fin n) (hji : j < i)
    (hγi : gamma T inst j i ≤ etaHat st k i) (hγj : gamma T inst j i ≤ etaHat st k j) :
    edgeCond n T st k i j := by
  obtain ⟨ha, hb, hba⟩ := log_facts n T hn hT
  have hΔ0 : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hΔ1 : gap inst j i ≤ 1 := by
    unfold gap; have := (inst.μ_mem j).2; have := (inst.μ_mem i).1; linarith
  have hγ1 : 1 ≤ gamma T inst j i := by
    unfold gamma
    rw [le_div_iff₀ (by positivity)]
    have : gap inst j i ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hηi : 1 ≤ etaHat st k i := le_trans hγ1 hγi
  have hηj : 1 ≤ etaHat st k j := le_trans hγ1 hγj
  have wi := wbound _ _ _ _ ha hb hba hΔ0 hΔ1 hγi
  have wj := wbound _ _ _ _ ha hb hba hΔ0 hΔ1 hγj
  have e21i : window21 n T st k i = window n T st k i := by
    unfold window21 window; rw [max_eq_left hηi]
  have e21j : window21 n T st k j = window n T st k j := by
    unfold window21 window; rw [max_eq_left hηj]
  have gi := (hgood k hk i).1
  have gj := (hgood k hk j).2
  rw [e21i] at gi
  rw [e21j] at gj
  have hwi : window n T st k i < gap inst j i / 4 := wi
  have hwj : window n T st k j < gap inst j i / 4 := wj
  have hgap : gap inst j i = inst.μ j - inst.μ i := rfl
  refine ⟨by linarith, by linarith, ?_⟩
  linarith

inductive IsPeelList {n : ℕ} (η : Fin n → ℕ) (G : Finset (Fin n × Fin n)) : List (Fin n) → Prop
  | nil : IsPeelList η G []
  | cons (x : Fin n) (l : List (Fin n))
      (hno_edge : ∀ y ∈ x :: l, (x, y) ∉ G)
      (hbest : ∀ y ∈ x :: l, (∀ z ∈ x :: l, (y, z) ∉ G) → η x ≤ η y)
      (htail : IsPeelList η G l) :
      IsPeelList η G (x :: l)

lemma IsPeelList.drop {n : ℕ} {η : Fin n → ℕ} {G : Finset (Fin n × Fin n)} {l : List (Fin n)}
    (h : IsPeelList η G l) : ∀ m : ℕ, IsPeelList η G (l.drop m) := by
  induction h with
  | nil => intro m; simp [IsPeelList.nil]
  | cons x l hno hbest htail ih =>
    intro m
    cases m with
    | zero => exact IsPeelList.cons x l hno hbest htail
    | succ m => exact ih m

open Classical in
lemma exists_sink_of_not_hasCycle {n : ℕ} (G : Finset (Fin n × Fin n)) (hG : ¬ HasCycle G)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, (x, y) ∉ G := by
  let D : Fin n → Finset (Fin n) := fun x =>
    S.filter (fun y => Relation.TransGen (fun a b => (a, b) ∈ G) x y)
  obtain ⟨x, hxS, hxmin⟩ := Finset.exists_min_image S (fun z => (D z).card) hS
  refine ⟨x, hxS, ?_⟩
  intro y hyS hxy
  have hsub : D y ⊆ D x := by
    intro z hz
    simp only [D, Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, Relation.TransGen.head hxy hz.2⟩
  have hy_in_Dx : y ∈ D x := by
    simp only [D, Finset.mem_filter]
    exact ⟨hyS, Relation.TransGen.single hxy⟩
  have hy_not_Dy : y ∉ D y := by
    simp only [D, Finset.mem_filter, not_and]
    intro _ hyy
    exact hG ⟨y, hyy⟩
  have hssub : D y ⊂ D x := Finset.ssubset_iff_of_subset hsub |>.mpr ⟨y, hy_in_Dx, hy_not_Dy⟩
  have hlt := Finset.card_lt_card hssub
  exact not_lt_of_ge (hxmin y hyS) hlt

lemma peel_spec_of_not_hasCycle {n : ℕ} (tb : Finset (Fin n) → Fin n)
    (htb : ∀ S : Finset (Fin n), S.Nonempty → tb S ∈ S)
    (η : Fin n → ℕ) (G : Finset (Fin n × Fin n)) (hG : ¬ HasCycle G) :
    ∀ (m : ℕ) (S : Finset (Fin n)), S.card = m →
      ∃ l : List (Fin n),
        peel tb η G m S = some l ∧
        l.Nodup ∧
        (∀ x, x ∈ l ↔ x ∈ S) ∧
        l.length = m ∧
        IsPeelList η G l := by
  intro m
  induction m with
  | zero =>
    intro S hS
    have hS0 : S = ∅ := Finset.card_eq_zero.mp hS
    subst hS0
    refine ⟨[], rfl, List.nodup_nil, ?_, rfl, IsPeelList.nil⟩
    intro x; simp
  | succ m ih =>
    intro S hS
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    let cands := S.filter (fun i => ∀ j ∈ S, (i, j) ∉ G)
    let best := cands.filter (fun i => ∀ j ∈ cands, η i ≤ η j)
    obtain ⟨s0, hs0_S, hs0_no⟩ := exists_sink_of_not_hasCycle G hG S hSne
    have hs0_cands : s0 ∈ cands := Finset.mem_filter.mpr ⟨hs0_S, hs0_no⟩
    have hcands_ne : cands.Nonempty := ⟨s0, hs0_cands⟩
    obtain ⟨b, hb_mem, hb_min⟩ := Finset.exists_min_image cands η hcands_ne
    have hb_best : b ∈ best := Finset.mem_filter.mpr ⟨hb_mem, hb_min⟩
    have hbest_ne : best.Nonempty := ⟨b, hb_best⟩
    have htb_mem : tb best ∈ best := htb best hbest_ne
    have htb_cands : tb best ∈ cands := (Finset.mem_filter.mp htb_mem).1
    have htb_min : ∀ j ∈ cands, η (tb best) ≤ η j := (Finset.mem_filter.mp htb_mem).2
    have htb_S : tb best ∈ S := (Finset.mem_filter.mp htb_cands).1
    have htb_no_edge : ∀ j ∈ S, (tb best, j) ∉ G := (Finset.mem_filter.mp htb_cands).2
    have hcard_erase : (S.erase (tb best)).card = m := by
      rw [Finset.card_erase_of_mem htb_S, hS]; omega
    obtain ⟨l, hpeel, hnd, hmem, hlen, hplist⟩ := ih (S.erase (tb best)) hcard_erase
    have hmem_cons : ∀ x, x ∈ tb best :: l ↔ x ∈ S := by
      intro x
      rw [List.mem_cons, hmem, Finset.mem_erase]
      by_cases hx : x = tb best
      · subst hx; simp [htb_S]
      · simp [hx]
    refine ⟨tb best :: l, ?_, ?_, hmem_cons, ?_, ?_⟩
    · simp only [peel, cands, best, if_pos htb_mem, hpeel]; rfl
    · refine List.nodup_cons.mpr ⟨?_, hnd⟩
      intro hxl
      have hmem_er := (hmem (tb best)).mp hxl
      simp at hmem_er
    · simp [hlen]
    · refine IsPeelList.cons (tb best) l ?_ ?_ hplist
      · intro y hy
        exact htb_no_edge y ((hmem_cons y).mp hy)
      · intro y hy hy_no
        apply htb_min y
        simp only [cands, Finset.mem_filter]
        refine ⟨(hmem_cons y).mp hy, ?_⟩
        intro z hz
        exact hy_no z ((hmem_cons z).mpr hz)

lemma listPerm_apply {n : ℕ} (l : List (Fin n)) (nd : l.Nodup) (hall : ∀ x, x ∈ l)
    (hlen : l.length = n) (j : Fin n) :
    listPerm l nd hall hlen j = l[(j : ℕ)]'(by omega) := by
  unfold listPerm
  rfl

lemma symm_lt_of_edge {n : ℕ} (η : Fin n → ℕ) (G : Finset (Fin n × Fin n))
    (l : List (Fin n)) (nd : l.Nodup) (hall : ∀ x, x ∈ l) (hlen : l.length = n)
    (hplist : IsPeelList η G l) (i u : Fin n) (he : (i, u) ∈ G) :
    (listPerm l nd hall hlen).symm u < (listPerm l nd hall hlen).symm i := by
  set π := listPerm l nd hall hlen
  set p := π.symm i
  set q := π.symm u
  have hp : l[(p : ℕ)]'(by omega) = i := by
    rw [← listPerm_apply l nd hall hlen p]
    exact π.apply_symm_apply i
  have hq : l[(q : ℕ)]'(by omega) = u := by
    rw [← listPerm_apply l nd hall hlen q]
    exact π.apply_symm_apply u
  by_contra hnot_lt
  have hpq : (p : ℕ) ≤ (q : ℕ) := by
    have := not_lt.mp hnot_lt
    exact Fin.le_def.mp this
  have hdrop_eq : l.drop (p : ℕ) = i :: l.drop ((p : ℕ) + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), hp]
  have hplist_drop : IsPeelList η G (i :: l.drop ((p : ℕ) + 1)) := by
    have hd := hplist.drop (p : ℕ)
    rwa [hdrop_eq] at hd
  have hu_mem : u ∈ i :: l.drop ((p : ℕ) + 1) := by
    rw [← hdrop_eq]
    have hidx : (q : ℕ) - (p : ℕ) < (l.drop (p : ℕ)).length := by
      rw [List.length_drop, hlen]; omega
    have hget : (l.drop (p : ℕ))[(q : ℕ) - (p : ℕ)]'hidx = u := by
      rw [List.getElem_drop]
      convert hq using 2
      omega
    rw [← hget]
    exact List.getElem_mem hidx
  cases hplist_drop with
  | cons _ _ hno _ _ =>
    exact hno u hu_mem he

lemma usedGraph_low (kStar : Fin L) (st : State n L) (hlow : InvLow kStar st)
    (hkStar : kStar ∉ st.elim) (k : Fin L) (hk : k ≤ kStar) :
    ∃ g : Fin L, g ≤ kStar ∧ g ∉ st.elim ∧ usedGraph st k = some (st.graph g) ∧
      ¬ HasCycle (st.graph g) ∧ st.graph kStar ⊆ st.graph g := by
  unfold usedGraph
  by_cases hkel : k ∉ st.elim
  · obtain ⟨h1, h2⟩ := hlow k hk hkel
    exact ⟨k, hk, hkel, by simp [hkel], h1, h2⟩
  · push Not at hkel
    have hk_lt : k < kStar := lt_of_le_of_ne hk (fun h => hkStar (h ▸ hkel))
    let up := Finset.univ.filter (fun m : Fin L => k < m ∧ m ∉ st.elim)
    have hkStar_up : kStar ∈ up := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_lt, hkStar⟩
    have hup_ne : up.Nonempty := ⟨kStar, hkStar_up⟩
    let g := up.min' hup_ne
    have hg_up : g ∈ up := Finset.min'_mem up hup_ne
    have hg_nel : g ∉ st.elim := (Finset.mem_filter.mp hg_up).2.2
    have hg_le : g ≤ kStar := Finset.min'_le up kStar hkStar_up
    obtain ⟨h1, h2⟩ := hlow g hg_le hg_nel
    refine ⟨g, hg_le, hg_nel, ?_, h1, h2⟩
    simp [hkel, up, dif_pos hup_ne, g]

lemma forcRank_low_edge (tb : List (Fin L × Obs n) → Fin L → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin L × Obs n) → Fin L → Equiv.Perm (Fin n))
    (h : List (Fin L × Obs n)) (st : State n L) (kStar : Fin L)
    (hlow : InvLow kStar st) (hkStar : kStar ∉ st.elim)
    (k : Fin L) (hk : k ≤ kStar) (j i u : Fin n)
    (hrank : forcRank tb fb h st k j = i) (he : (i, u) ∈ st.graph kStar) :
    (forcRank tb fb h st k).symm u < j := by
  obtain ⟨g, _, _, hused, hacyc, hsub⟩ := usedGraph_low kStar st hlow hkStar k hk
  obtain ⟨l, hpeel, hnd, hmem_iff, hlen, hplist⟩ :=
    peel_spec_of_not_hasCycle (tb h k) (htb h k) (st.cnt k) (st.graph g) hacyc n Finset.univ (by simp)
  have hall : ∀ x, x ∈ l := fun x => (hmem_iff x).mpr (Finset.mem_univ x)
  have hcond : l.Nodup ∧ (∀ x, x ∈ l) ∧ l.length = n := ⟨hnd, hall, hlen⟩
  have hfeq : forcRank tb fb h st k = listPerm l hnd hall hlen := by
    unfold forcRank
    rw [hused]
    dsimp only
    unfold graphRankSelect
    rw [if_neg hacyc, hpeel]
    dsimp only
    rw [dif_pos hcond]
  have hj_eq : (forcRank tb fb h st k).symm i = j :=
    (Equiv.symm_apply_eq _).mpr hrank.symm
  rw [← hj_eq, hfeq]
  exact symm_lt_of_edge (st.cnt k) (st.graph g) l hnd hall hlen hplist i u (hsub he)

noncomputable def rho (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) : ℝ :=
  if h : m < n then reach inst π ⟨m, h⟩ else 0

lemma reach_succ (inst : Instance n) (π : Equiv.Perm (Fin n)) (m : ℕ) (h : m + 1 < n) :
    reach inst π ⟨m + 1, h⟩ = reach inst π ⟨m, by omega⟩ *
      ((1 - inst.q ⟨m, by omega⟩) * (1 - inst.μ (π ⟨m, by omega⟩))) := by
  unfold reach
  have hI : Finset.Iio (⟨m + 1, h⟩ : Fin n) = insert ⟨m, by omega⟩ (Finset.Iio ⟨m, by omega⟩) := by
    ext r; simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def, Fin.ext_iff]; omega
  rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]
  ring

lemma realW_pair (inst : Instance n) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    realW inst π (j, true) + realW inst π (j, false) = rho inst π j - rho inst π (j + 1) := by
  simp only [realW, rho, dif_pos j.isLt]
  by_cases h : (j : ℕ) + 1 < n
  · rw [dif_pos h, if_pos h, reach_succ inst π j h]
    ring
  · rw [dif_neg h, if_neg h]; ring

open Classical in
lemma realW_sum_ge (inst : Instance n) (π : Equiv.Perm (Fin n)) (p : Fin n) :
    (∑ o : Obs n, realW inst π o * (if p ≤ o.1 then 1 else 0)) = reach inst π p := by
  rw [Fintype.sum_prod_type]
  have hbool : ∀ r : Fin n,
      (∑ b : Bool, realW inst π (r, b) * (if p ≤ r then (1 : ℝ) else 0)) =
      if (p : ℕ) ≤ (r : ℕ) then rho inst π r - rho inst π (r + 1) else 0 := by
    intro r
    rw [Fintype.sum_bool, ← add_mul, realW_pair]
    by_cases hpr : p ≤ r
    · have hpr' : (p : ℕ) ≤ (r : ℕ) := Fin.le_def.mp hpr
      simp [hpr, hpr']
    · have hpr' : ¬ (p : ℕ) ≤ (r : ℕ) := fun h => hpr (Fin.le_def.mpr h)
      simp [hpr, hpr']
  simp_rw [hbool]
  rw [Fin.sum_univ_eq_sum_range
    (fun m => if (p : ℕ) ≤ m then rho inst π m - rho inst π (m + 1) else 0) n]
  have htele : ∀ d : ℕ,
      (∑ m ∈ Finset.range ((p : ℕ) + d),
        if (p : ℕ) ≤ m then rho inst π m - rho inst π (m + 1) else 0) =
      rho inst π (p : ℕ) - rho inst π ((p : ℕ) + d) := by
    intro d
    induction d with
    | zero =>
      simp only [add_zero]
      rw [Finset.sum_eq_zero]
      · ring
      · intro m hm
        have : ¬ (p : ℕ) ≤ m := by simp at hm; omega
        simp [this]
    | succ d ih =>
      rw [ ← add_assoc, Finset.sum_range_succ, ih, if_pos (by omega)]
      ring
  have h1 := htele (n - (p : ℕ))
  have hp_lt : (p : ℕ) < n := p.isLt
  rw [show (p : ℕ) + (n - (p : ℕ)) = n by omega] at h1
  rw [h1]
  simp [rho]

open Classical in
lemma prod_one_sub_le_of_subset {α : Type*} (f : α → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) {A B : Finset α} (hAB : A ⊆ B) :
    (∏ x ∈ B, (1 - f x)) ≤ ∏ x ∈ A, (1 - f x) := by
  rw [← Finset.sdiff_union_of_subset hAB, Finset.prod_union Finset.sdiff_disjoint]
  have h1 : ∏ x ∈ B \ A, (1 - f x) ≤ 1 :=
    Finset.prod_le_one (fun x _ => by linarith [hf1 x]) (fun x _ => by linarith [hf0 x])
  have h2 : 0 ≤ ∏ x ∈ A, (1 - f x) :=
    Finset.prod_nonneg (fun x _ => by linarith [hf1 x])
  nlinarith

lemma prod_Iio_perm (inst : Instance n) (π : Equiv.Perm (Fin n)) (p : Fin n) :
    (∏ r ∈ Finset.Iio p, (1 - inst.μ (π r))) =
      ∏ u ∈ (Finset.Iio p).image π, (1 - inst.μ u) := by
  rw [Finset.prod_image (fun x _ y _ h => π.injective h)]

lemma reach_le_of_outEdges (inst : Instance n) (π : Equiv.Perm (Fin n))
    (j : Fin n) (O : Finset (Fin n)) (hO : ∀ u ∈ O, π.symm u < j) :
    O.card ≤ (j : ℕ) ∧
    reach inst π j ≤ (∏ r ∈ Finset.Iio j, (1 - inst.q r)) * ∏ u ∈ O, (1 - inst.μ u) := by
  have hsub : O ⊆ (Finset.Iio j).image π := by
    intro u hu
    rw [Finset.mem_image]
    exact ⟨π.symm u, Finset.mem_Iio.mpr (hO u hu), π.apply_symm_apply u⟩
  have hcard : O.card ≤ (j : ℕ) := by
    calc O.card ≤ ((Finset.Iio j).image π).card := Finset.card_le_card hsub
      _ = (Finset.Iio j).card := Finset.card_image_of_injective _ π.injective
      _ = (j : ℕ) := Fin.card_Iio j
  refine ⟨hcard, ?_⟩
  unfold reach
  rw [prod_Iio_perm]
  apply mul_le_mul_of_nonneg_left
  · exact prod_one_sub_le_of_subset inst.μ (fun x => (inst.μ_mem x).1)
      (fun x => (inst.μ_mem x).2) hsub
  · exact Finset.prod_nonneg (fun r _ => by linarith [(inst.q_mem r).2])

open Classical in
lemma exists_first_non_outEdge (inst : Instance n) (πStar : Equiv.Perm (Fin n))
    (j : Fin n) (O : Finset (Fin n)) (hOcard : O.card ≤ (j : ℕ)) :
    ∃ pStar : Fin n, pStar ≤ j ∧ πStar pStar ∉ O ∧
      (∏ r ∈ Finset.Iio j, (1 - inst.q r)) * (∏ u ∈ O, (1 - inst.μ u)) ≤
        reach inst πStar pStar := by
  let Pout := (Finset.Iic j).filter (fun p : Fin n => πStar p ∉ O)
  have hPout_ne : Pout.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hsub : (Finset.Iic j).image πStar ⊆ O := by
      intro u hu
      obtain ⟨p, hp_Iic, rfl⟩ := Finset.mem_image.mp hu
      by_contra hnot
      have hp_Pout : p ∈ Pout := Finset.mem_filter.mpr ⟨hp_Iic, hnot⟩
      rw [hemp] at hp_Pout
      exact Finset.notMem_empty p hp_Pout
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ πStar.injective, Fin.card_Iic] at hcard
    omega
  let pStar := Pout.min' hPout_ne
  have hpStar_mem : pStar ∈ Pout := Finset.min'_mem Pout hPout_ne
  have hpStar_le : pStar ≤ j := Finset.mem_Iic.mp (Finset.mem_filter.mp hpStar_mem).1
  have hpStar_not_O : πStar pStar ∉ O := (Finset.mem_filter.mp hpStar_mem).2
  have hIio_sub : Finset.Iio pStar ⊆ Finset.Iio j :=
    fun r hr => Finset.mem_Iio.mpr (lt_of_lt_of_le (Finset.mem_Iio.mp hr) hpStar_le)
  have himg_sub : (Finset.Iio pStar).image πStar ⊆ O := by
    intro u hu
    obtain ⟨r, hr_lt, rfl⟩ := Finset.mem_image.mp hu
    have hr_lt' : r < pStar := Finset.mem_Iio.mp hr_lt
    have hr_Iic : r ∈ Finset.Iic j := Finset.mem_Iic.mpr (le_trans hr_lt'.le hpStar_le)
    by_contra hnot
    have hr_Pout : r ∈ Pout := Finset.mem_filter.mpr ⟨hr_Iic, hnot⟩
    exact not_lt_of_ge (Finset.min'_le Pout r hr_Pout) hr_lt'
  have hq_le : (∏ r ∈ Finset.Iio j, (1 - inst.q r)) ≤ ∏ r ∈ Finset.Iio pStar, (1 - inst.q r) :=
    prod_one_sub_le_of_subset inst.q (fun x => (inst.q_mem x).1) (fun x => (inst.q_mem x).2) hIio_sub
  have hμ_le : (∏ u ∈ O, (1 - inst.μ u)) ≤ ∏ r ∈ Finset.Iio pStar, (1 - inst.μ (πStar r)) := by
    rw [prod_Iio_perm]
    exact prod_one_sub_le_of_subset inst.μ (fun x => (inst.μ_mem x).1)
      (fun x => (inst.μ_mem x).2) himg_sub
  refine ⟨pStar, hpStar_le, hpStar_not_O, ?_⟩
  unfold reach
  exact mul_le_mul hq_le hμ_le
    (Finset.prod_nonneg (fun u _ => by linarith [(inst.μ_mem u).2]))
    (Finset.prod_nonneg (fun r _ => by linarith [(inst.q_mem r).2]))

lemma etaHat_ge_cnt (st : State n L) (k : Fin L) (i : Fin n) :
    (st.cnt k i : ℝ) ≤ etaHat st k i := by
  unfold etaHat
  have hsum : 0 ≤ (∑ g ∈ Finset.univ.filter (fun g : Fin L => g < k), (st.cnt g i : ℝ)) /
      2 ^ ((k : ℕ) + 1) := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    · positivity
  linarith

lemma gamma_le_four_gamma_of_half_gap {T : ℕ} (inst : Instance n)
    (hA : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T))
    (j i u v : Fin n) (hgap_pos : 0 < gap inst j i)
    (hgap_half : gap inst j i / 2 ≤ gap inst u v) :
    gamma T inst u v ≤ 4 * gamma T inst j i := by
  unfold gamma
  have huv_pos : 0 < gap inst u v := by linarith
  have hsq : (gap inst j i / 2) ^ 2 ≤ gap inst u v ^ 2 := by nlinarith
  have h1 : 64 * Real.log (4 * (n : ℝ) * T / delta n T) / gap inst u v ^ 2 ≤
      64 * Real.log (4 * (n : ℝ) * T / delta n T) / (gap inst j i / 2) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
  calc 64 * Real.log (4 * (n : ℝ) * T / delta n T) / gap inst u v ^ 2
      ≤ 64 * Real.log (4 * (n : ℝ) * T / delta n T) / (gap inst j i / 2) ^ 2 := h1
    _ = 4 * (64 * Real.log (4 * (n : ℝ) * T / delta n T) / gap inst j i ^ 2) := by ring

lemma cnt_sigma_lt_four_gamma (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T))
    (t : Fin T) (ht1 : 1 ≤ (t : ℕ))
    (hgood_t : GoodSt n T inst F (stateAt tb fb τ t))
    (hinv_prev : Inv F (stateAt tb fb τ ((t : ℕ) - 1)))
    (hinv_t : Inv F (stateAt tb fb τ t))
    (kStar : Fin (numLevels T)) (hkStar : F ≤ 2 ^ ((kStar : ℕ) + 1))
    (j i pStar : Fin n) (hji : j < i) (hpStar : pStar ≤ j)
    (hηi : 4 * gamma T inst j i ≤ etaHat (stateAt tb fb τ t) kStar i)
    (hno_i_sig : (i, forcRank tb fb (algHist τ t) (stateAt tb fb τ t) kStar pStar) ∉
      (stateAt tb fb τ t).graph kStar) :
    ((stateAt tb fb τ t).cnt kStar
      (forcRank tb fb (algHist τ t) (stateAt tb fb τ t) kStar pStar) : ℝ) <
      4 * gamma T inst j i := by
  set st := stateAt tb fb τ t
  set h := algHist τ t
  set σ := forcRank tb fb h st kStar pStar
  obtain ⟨ha, _, _⟩ := log_facts n T hn hT
  have hA0 : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T) := by linarith
  have hgap_ji : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  obtain ⟨s, hs⟩ : ∃ s, (t : ℕ) = s + 1 := ⟨(t : ℕ) - 1, by omega⟩
  obtain ⟨π_prev, hπ_prev⟩ := stateAt_succ tb fb τ s (by omega)
  have hk_prev : kStar ∉ (stateAt tb fb τ s).elim := by
    have hs_eq : s = (t : ℕ) - 1 := by omega
    rw [hs_eq]
    exact (hinv_prev kStar hkStar).1
  have hst_upd : ∀ a b : Fin n, edgeCond n T st kStar a b → (a, b) ∈ st.graph kStar := by
    intro a b hec
    have hst_eq : st = (stateAt tb fb τ s).update n T π_prev (τ ⟨s, by omega⟩).1 (τ ⟨s, by omega⟩).2.2 := by
      change stateAt tb fb τ (t : ℕ) = _
      rw [hs, hπ_prev]
    rw [hst_eq] at hec ⊢
    exact (mem_graph_update T _ π_prev _ _ kStar (a, b)).mpr
      (Or.inr ⟨hk_prev, kStar, le_rfl, hk_prev, hec⟩)
  by_contra hnot_lt
  have hcnt_ge : 4 * gamma T inst j i ≤ (st.cnt kStar σ : ℝ) := le_of_not_gt hnot_lt
  have hησ : 4 * gamma T inst j i ≤ etaHat st kStar σ :=
    le_trans hcnt_ge (etaHat_ge_cnt st kStar σ)
  by_cases hgap_sig : gap inst j i / 2 ≤ gap inst σ i
  · have hμ_lt : inst.μ i < inst.μ σ := by
      unfold gap at hgap_ji hgap_sig; linarith
    have hσi : σ < i := lt_of_not_ge (fun hge => not_lt.mpr (hμ.antitone hge) hμ_lt)
    have hγ_le := gamma_le_four_gamma_of_half_gap inst hA0 j i σ i hgap_ji hgap_sig
    have hea := edge_add n T F hn hT inst hμ st kStar hkStar hgood_t σ i hσi
      (le_trans hγ_le hηi) (le_trans hγ_le hησ)
    exact hno_i_sig (hst_upd i σ hea)
  · have hgap_sig' : gap inst σ i < gap inst j i / 2 := lt_of_not_ge hgap_sig
    have hk_inv := hinv_t kStar hkStar
    have hk_elim : kStar ∉ st.elim := hk_inv.1
    have hk_edges : ∀ e ∈ st.graph kStar, e.2 < e.1 := hk_inv.2
    have hk_acyc : ¬ HasCycle (st.graph kStar) := not_hasCycle _ hk_edges
    obtain ⟨l, hpeel, hnd, hmem_iff, hlen, hplist⟩ :=
      peel_spec_of_not_hasCycle (tb h kStar) (htb h kStar) (st.cnt kStar) (st.graph kStar)
        hk_acyc n Finset.univ (by simp)
    have hall : ∀ x, x ∈ l := fun x => (hmem_iff x).mpr (Finset.mem_univ x)
    have hcond : l.Nodup ∧ (∀ x, x ∈ l) ∧ l.length = n := ⟨hnd, hall, hlen⟩
    have hrank_eq : forcRank tb fb h st kStar = listPerm l hnd hall hlen := by
      unfold forcRank usedGraph
      rw [if_pos hk_elim]
      dsimp only
      unfold graphRankSelect
      rw [if_neg hk_acyc, hpeel]
      dsimp only
      rw [dif_pos hcond]
    have hget_sig : l[(pStar : ℕ)]'(by omega) = σ := by
      change l[(pStar : ℕ)]'(by omega) = forcRank tb fb h st kStar pStar
      rw [hrank_eq, listPerm_apply]
    have hdrop_eq : l.drop (pStar : ℕ) = σ :: l.drop ((pStar : ℕ) + 1) := by
      rw [List.drop_eq_getElem_cons (by omega), hget_sig]
    have hplist_drop : IsPeelList (st.cnt kStar) (st.graph kStar) (σ :: l.drop ((pStar : ℕ) + 1)) := by
      have hd := hplist.drop (pStar : ℕ)
      rwa [hdrop_eq] at hd
    have hno_edge : ∀ y ∈ l.drop (pStar : ℕ), (σ, y) ∉ st.graph kStar := by
      cases hplist_drop with
      | cons _ _ hno _ _ =>
        intro y hy
        rw [hdrop_eq] at hy
        exact hno y hy
    have hbest : ∀ y ∈ l.drop (pStar : ℕ),
        (∀ z ∈ l.drop (pStar : ℕ), (y, z) ∉ st.graph kStar) → st.cnt kStar σ ≤ st.cnt kStar y := by
      cases hplist_drop with
      | cons _ _ _ hb _ =>
        intro y hy hy_no
        rw [hdrop_eq] at hy
        apply hb y hy
        intro z hz
        rw [← hdrop_eq] at hz
        exact hy_no z hz
    let Sp : Finset (Fin n) := (l.drop (pStar : ℕ)).toFinset
    have hSp_card : Sp.card = n - (pStar : ℕ) := by
      change (l.drop (pStar : ℕ)).toFinset.card = _
      rw [List.toFinset_card_of_nodup hnd.drop, List.length_drop, hlen]
    have hIoi_card : (Finset.Ioi j).card = n - 1 - (j : ℕ) := Fin.card_Ioi j
    have hnot_sub : ¬ (Sp ⊆ Finset.Ioi j) := by
      intro hsub
      have hle := Finset.card_le_card hsub
      rw [hSp_card, hIoi_card] at hle
      have hj_lt : (j : ℕ) < n := j.isLt
      have hpj : (pStar : ℕ) ≤ (j : ℕ) := Fin.le_def.mp hpStar
      omega
    obtain ⟨m0, hm0_Sp, hm0_not⟩ := Finset.not_subset.mp hnot_sub
    have hm0_le : m0 ≤ j := not_lt.mp (Finset.mem_Ioi.not.mp hm0_not)
    have hSp_ne : Sp.Nonempty := ⟨m0, hm0_Sp⟩
    let u : Fin n := Sp.min' hSp_ne
    have hu_Sp : u ∈ Sp := Finset.min'_mem Sp hSp_ne
    have hu_drop : u ∈ l.drop (pStar : ℕ) := List.mem_toFinset.mp hu_Sp
    have hu_le_j : u ≤ j := le_trans (Finset.min'_le Sp m0 hm0_Sp) hm0_le
    have hu_no_edge : ∀ z ∈ l.drop (pStar : ℕ), (u, z) ∉ st.graph kStar := by
      intro z hz hmem
      have hz_Sp : z ∈ Sp := List.mem_toFinset.mpr hz
      have hu_le_z : u ≤ z := Finset.min'_le Sp z hz_Sp
      have hz_lt_u : z < u := hk_edges (u, z) hmem
      exact not_lt_of_ge hu_le_z hz_lt_u
    have hsig_u_not_edge : (σ, u) ∉ st.graph kStar := hno_edge u hu_drop
    have hcnt_le : st.cnt kStar σ ≤ st.cnt kStar u := hbest u hu_drop hu_no_edge
    have hcnt_le' : (st.cnt kStar σ : ℝ) ≤ (st.cnt kStar u : ℝ) := by exact_mod_cast hcnt_le
    have hηu : 4 * gamma T inst j i ≤ etaHat st kStar u :=
      le_trans hcnt_ge (le_trans hcnt_le' (etaHat_ge_cnt st kStar u))
    have hμ_uj : inst.μ j ≤ inst.μ u := hμ.antitone hu_le_j
    have hgap_u_sig : gap inst j i / 2 ≤ gap inst u σ := by
      unfold gap at hgap_ji hgap_sig' ⊢
      linarith
    have hμ_sig_u : inst.μ σ < inst.μ u := by
      unfold gap at hgap_ji hgap_u_sig; linarith
    have hu_lt_sig : u < σ := lt_of_not_ge (fun hge => not_lt.mpr (hμ.antitone hge) hμ_sig_u)
    have hγ_le := gamma_le_four_gamma_of_half_gap inst hA0 j i u σ hgap_ji hgap_u_sig
    have hea := edge_add n T F hn hT inst hμ st kStar hkStar hgood_t u σ hu_lt_sig
      (le_trans hγ_le hησ) (le_trans hγ_le hηu)
    exact hsig_u_not_edge (hst_upd σ u hea)

lemma cnt_succ_ge {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) (k : Fin (numLevels T)) (i : Fin n) :
    (stateAt tb fb τ t).cnt k i ≤ (stateAt tb fb τ ((t : ℕ) + 1)).cnt k i := by
  rw [stateAt_succ_eq]
  unfold State.update
  dsimp only
  split_ifs <;> omega

lemma cnt_succ_of_feedback {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) (k : Fin (numLevels T)) (j i : Fin n)
    (htk : (τ t).1 = k) (hfb : feedbackEvent (forc n T tb fb) τ t j i) :
    (stateAt tb fb τ ((t : ℕ) + 1)).cnt k i = (stateAt tb fb τ t).cnt k i + 1 := by
  rw [stateAt_succ_eq]
  unfold State.update
  dsimp only
  have hsymm : (ranking (forc n T tb fb) τ t).symm i = j :=
    Equiv.symm_apply_eq (ranking (forc n T tb fb) τ t) |>.mpr hfb.1.symm
  have hcond : k = (τ t).1 ∧ (ranking (forc n T tb fb) τ t).symm i ≤ (τ t).2.2.1 := by
    refine ⟨htk.symm, ?_⟩
    rw [hsymm]
    exact hfb.2.2
  rw [if_pos hcond]

lemma cnt_succ_of_ne {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) (g : Fin (numLevels T)) (i : Fin n)
    (hne : g ≠ (τ t).1) :
    (stateAt tb fb τ ((t : ℕ) + 1)).cnt g i = (stateAt tb fb τ t).cnt g i := by
  rw [stateAt_succ_eq]
  unfold State.update
  dsimp only
  simp [hne]

lemma sum_low_cnt_succ_of_feedback {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : Fin T) (kStar : Fin (numLevels T)) (j i : Fin n)
    (htk : (τ t).1 < kStar) (hfb : feedbackEvent (forc n T tb fb) τ t j i) :
    (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < kStar),
      (stateAt tb fb τ ((t : ℕ) + 1)).cnt g i) =
    (∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < kStar),
      (stateAt tb fb τ t).cnt g i) + 1 := by
  let S := Finset.univ.filter (fun g : Fin (numLevels T) => g < kStar)
  have hmem : (τ t).1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, htk⟩
  rw [← Finset.sum_erase_add S _ hmem,
      ← Finset.sum_erase_add S (fun g => (stateAt tb fb τ t).cnt g i) hmem]
  have h1 : (stateAt tb fb τ ((t : ℕ) + 1)).cnt (τ t).1 i =
      (stateAt tb fb τ t).cnt (τ t).1 i + 1 :=
    cnt_succ_of_feedback tb fb τ t (τ t).1 j i rfl hfb
  have h2 : (∑ g ∈ S.erase (τ t).1, (stateAt tb fb τ ((t : ℕ) + 1)).cnt g i) =
      ∑ g ∈ S.erase (τ t).1, (stateAt tb fb τ t).cnt g i := by
    apply Finset.sum_congr rfl
    intro g hg
    exact cnt_succ_of_ne tb fb τ t g i (Finset.ne_of_mem_erase hg)
  rw [h1, h2]
  omega

lemma sum_low_cnt_le_etaHat (st : State n L) (kStar : Fin L) (i : Fin n) :
    ((∑ g ∈ Finset.univ.filter (fun g : Fin L => g < kStar), st.cnt g i : ℕ) : ℝ) ≤
      2 ^ ((kStar : ℕ) + 1) * etaHat st kStar i := by
  unfold etaHat
  rw [Nat.cast_sum]
  have hpow : (0 : ℝ) < 2 ^ ((kStar : ℕ) + 1) := by positivity
  have hcnt : (0 : ℝ) ≤ st.cnt kStar i := Nat.cast_nonneg _
  have h1 : (∑ g ∈ Finset.univ.filter (fun g : Fin L => g < kStar), (st.cnt g i : ℝ)) =
      2 ^ ((kStar : ℕ) + 1) *
        ((∑ g ∈ Finset.univ.filter (fun g : Fin L => g < kStar), (st.cnt g i : ℝ)) /
          2 ^ ((kStar : ℕ) + 1)) := by
    field_simp
  nlinarith

open Classical in
lemma filter_lt_succ {T : ℕ} (m : ℕ) (hm : m < T) :
    Finset.univ.filter (fun t : Fin T => (t : ℕ) < m + 1) =
      insert (⟨m, hm⟩ : Fin T) (Finset.univ.filter (fun t : Fin T => (t : ℕ) < m)) := by
  ext t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

lemma sum_le_of_step_bound {T : ℕ} (c : ℕ → ℕ) (P : Fin T → Prop) [DecidablePred P] (B : ℝ)
    (hB : 0 ≤ B) (hc0 : c 0 = 0)
    (hc_mono : ∀ t : Fin T, c t ≤ c ((t : ℕ) + 1))
    (hc_step : ∀ t : Fin T, P t → c ((t : ℕ) + 1) = c t + 1 ∧ (c t : ℝ) < B) :
    (∑ t : Fin T, if P t then (1 : ℝ) else 0) ≤ B + 1 := by
  have hmain : ∀ m : ℕ, m ≤ T →
      (∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < m), if P t then (1 : ℝ) else 0) ≤ (c m : ℝ) ∧
      (∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < m), if P t then (1 : ℝ) else 0) ≤ B + 1 := by
    intro m
    induction m with
    | zero =>
      intro _
      have hempty : Finset.univ.filter (fun t : Fin T => (t : ℕ) < 0) = ∅ := by
        ext t; simp
      rw [hempty, Finset.sum_empty, hc0, Nat.cast_zero]
      exact ⟨le_rfl, by linarith⟩
    | succ m ih =>
      intro hm
      have hm_lt : m < T := by omega
      obtain ⟨ih1, _ih2⟩ := ih (by omega)
      let t0 : Fin T := ⟨m, hm_lt⟩
      have hnot_mem : t0 ∉ Finset.univ.filter (fun t : Fin T => (t : ℕ) < m) := by
        simp [t0]
      rw [filter_lt_succ m hm_lt, Finset.sum_insert hnot_mem]
      by_cases hP : P t0
      · obtain ⟨hc_eq, hc_lt⟩ := hc_step t0 hP
        rw [if_pos hP]
        have hc_eq' : (c (m + 1) : ℝ) = (c m : ℝ) + 1 := by
          exact_mod_cast hc_eq
        refine ⟨by linarith, by linarith⟩
      · rw [if_neg hP, zero_add]
        have hc_le : (c m : ℝ) ≤ (c (m + 1) : ℝ) := by
          exact_mod_cast hc_mono t0
        refine ⟨by linarith, (ih (by omega)).2⟩
  have hT_filter : Finset.univ.filter (fun t : Fin T => (t : ℕ) < T) = Finset.univ := by
    ext t; simp
  have hres := (hmain T le_rfl).2
  rwa [hT_filter] at hres

open Classical in
lemma termA_pathwise (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (hkStar_ub : 2 ^ ((kStar : ℕ) + 1) ≤ 2 * F)
    (j i : Fin n) (hji : j < i) (τ : Fin T → Step n (numLevels T)) :
    (∑ t : Fin T,
      if (τ t).1 < kStar ∧ feedbackEvent (forc n T tb fb) τ t j i ∧
         etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i
      then (1 : ℝ) else 0) ≤ 8 * (F : ℝ) * gamma T inst j i + 1 := by
  obtain ⟨ha, _, _⟩ := log_facts n T hn hT
  have hgap : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hγ_pos : 0 < gamma T inst j i := by unfold gamma; positivity
  have hB : 0 ≤ 8 * (F : ℝ) * gamma T inst j i := by positivity
  refine sum_le_of_step_bound
    (fun m => ∑ g ∈ Finset.univ.filter (fun g : Fin (numLevels T) => g < kStar),
      (stateAt tb fb τ m).cnt g i)
    (fun t => (τ t).1 < kStar ∧ feedbackEvent (forc n T tb fb) τ t j i ∧
      etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i)
    (8 * (F : ℝ) * gamma T inst j i) hB ?_ ?_ ?_
  · rw [stateAt_zero]; simp [State.init]
  · intro t
    exact Finset.sum_le_sum (fun g _ => cnt_succ_ge tb fb τ t g i)
  · intro t ⟨htk, hfb, hη_lt⟩
    refine ⟨sum_low_cnt_succ_of_feedback tb fb τ t kStar j i htk hfb, ?_⟩
    have h1 := sum_low_cnt_le_etaHat (stateAt tb fb τ t) kStar i
    have h2 : (2 : ℝ) ^ ((kStar : ℕ) + 1) ≤ 2 * (F : ℝ) := by exact_mod_cast hkStar_ub
    have hη_nonneg : 0 ≤ etaHat (stateAt tb fb τ t) kStar i :=
      le_trans (Nat.cast_nonneg _) (etaHat_ge_cnt (stateAt tb fb τ t) kStar i)
    have hF_pos : (0 : ℝ) < 2 ^ ((kStar : ℕ) + 1) := by positivity
    nlinarith

lemma S_eq (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) =
    ∑ i ∈ Finset.range (L - 1), (1 / 4 : ℝ) * (1 / 2 : ℝ) ^ i := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [show 1 + i + 1 = i + 2 by ring, pow_add]
  norm_num
  ring

lemma S_le (L : ℕ) : ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1) ≤ 1 / 2 := by
  rw [S_eq, ← Finset.mul_sum]
  have := sum_geometric_two_le (L - 1)
  linarith

lemma levelW_nonneg (L : ℕ) (k : Fin L) : 0 ≤ levelW L k := by
  unfold levelW
  split_ifs
  · linarith [S_le L]
  · positivity

lemma levelW_sum (L : ℕ) (hL : 1 ≤ L) : ∑ k : Fin L, levelW L k = 1 := by
  unfold levelW
  rw [Fin.sum_univ_eq_sum_range (fun m => if m = 0 then 1 - ∑ m ∈ Finset.Ico 1 L, (1 / 2 : ℝ) ^ (m + 1)
    else (1 / 2 : ℝ) ^ (m + 1)) L]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, if_false, if_true]
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  have : ∀ i ∈ Finset.range L', (1 / 2 : ℝ) ^ (1 + i + 1) = (1 / 2 : ℝ) ^ (i + 1 + 1) := by
    intro i _; rw [show 1 + i + 1 = i + 1 + 1 by ring]
  rw [Finset.sum_congr rfl this]
  ring

lemma realW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (o : Obs n) :
    0 ≤ realW inst π o := by
  rcases o with ⟨j, b⟩
  have h1 : 0 ≤ reach inst π j := by
    unfold reach
    apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro r _
    · linarith [(inst.q_mem r).2]
    · linarith [(inst.μ_mem (π r)).2]
  have h2 := (inst.μ_mem (π j)).1
  have h3 := (inst.μ_mem (π j)).2
  have h4 := (inst.q_mem j).1
  cases b
  · simp only [realW]
    apply mul_nonneg (mul_nonneg h1 (by linarith))
    split_ifs <;> linarith
  · simp only [realW]; exact mul_nonneg h1 h2

lemma obsW_nonneg (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (o : Obs n) :
    0 ≤ obsW inst π a o := by
  cases a with
  | none => exact realW_nonneg inst π o
  | some a => simp only [obsW]; split_ifs <;> norm_num

lemma stepW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) (s : Fin T) :
    0 ≤ stepW inst P A τ s := by
  unfold stepW
  exact mul_nonneg (mul_nonneg (hw_nonneg _ _) ENNReal.toReal_nonneg) (obsW_nonneg _ _ _ _)

lemma trajW_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (τ : Fin T → Step n L) :
    0 ≤ trajW inst P A T τ :=
  Finset.prod_nonneg (fun s _ => stepW_nonneg inst P A hw_nonneg τ s)

lemma reach_zero (inst : Instance n) (π : Equiv.Perm (Fin n)) (h : 0 < n) :
    reach inst π ⟨0, h⟩ = 1 := by
  unfold reach
  have hI : Finset.Iio (⟨0, h⟩ : Fin n) = ∅ := by
    ext r; simp [Fin.lt_def]
  simp [hI]

lemma realW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (hn : 1 ≤ n) :
    ∑ o, realW inst π o = 1 := by
  have h0 : 0 < n := by omega
  have := realW_sum_ge inst π ⟨0, h0⟩
  have hle : ∀ o : Obs n, (⟨0, h0⟩ : Fin n) ≤ o.1 := fun o => Fin.le_def.mpr (Nat.zero_le _)
  simp only [hle, if_true, mul_one] at this
  rw [this, reach_zero inst π h0]

lemma obsW_sum (inst : Instance n) (π : Equiv.Perm (Fin n)) (a : Action n) (hn : 1 ≤ n) :
    ∑ o, obsW inst π a o = 1 := by
  cases a with
  | none => exact realW_sum inst π hn
  | some a => simp [obsW]

lemma pmf_sum (p : PMF (Action n)) : ∑ a, (p a).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top p a)]
  rw [← tsum_fintype (L := SummationFilter.unconditional _), PMF.tsum_coe]; simp

def DepBelow (m : ℕ) {β : Type*} (f : (Fin T → Step n L) → β) : Prop :=
  ∀ τ τ' : Fin T → Step n L, (∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) → f τ = f τ'

lemma DepBelow.mono {m m' : ℕ} {β : Type*} {f : (Fin T → Step n L) → β} (h : DepBelow m f)
    (hm : m ≤ m') : DepBelow m' f :=
  fun τ τ' hτ => h τ τ' (fun i hi => hτ i (lt_of_lt_of_le hi hm))

lemma algHist_dep (s : ℕ) : DepBelow (T := T) (n := n) (L := L) s (fun τ => algHist τ s) := by
  intro τ τ' h
  beta_reduce
  unfold algHist
  congr 1
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp at h1; simp; omega

lemma algHist_eq (s : ℕ) (τ τ' : Fin T → Step n L)
    (h : ∀ i : Fin T, (i : ℕ) < s → τ i = τ' i) :
    algHist τ s = algHist τ' s := algHist_dep s τ τ' h

lemma stateAt_eq (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (s : ℕ) (τ τ' : Fin T → Step n (numLevels T))
    (h : ∀ i : Fin T, (i : ℕ) < s → τ i = τ' i) :
    stateAt tb fb τ s = stateAt tb fb τ' s := by
  unfold stateAt
  rw [algHist_eq s τ τ' h]

lemma ranking_dep (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => ranking A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold ranking
  have e := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  beta_reduce at e
  rw [e, h s (by omega)]

lemma pubHist_dep (A : Alg n L) (s : ℕ) : DepBelow (T := T) s (fun τ => pubHist A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold pubHist
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    simp at h1
    have e := ranking_dep A ⟨i, by omega⟩ τ τ' (fun j hj => h j (by simp at hj; omega))
    beta_reduce at e
    rw [e, h ⟨i, by omega⟩ (by simp; omega)]

lemma stepW_dep (inst : Instance n) (P : Adversary n) (A : Alg n L) (s : Fin T) :
    DepBelow (s + 1) (fun τ => stepW inst P A τ s) := by
  intro τ τ' h
  beta_reduce
  unfold stepW
  have e1 := algHist_dep (n := n) (L := L) s τ τ' (fun i hi => h i (by omega))
  have e2 := pubHist_dep A s τ τ' (fun i hi => h i (by omega))
  have e3 := ranking_dep A s τ τ' h
  beta_reduce at e1 e2 e3
  rw [e1, e2, e3, h s (by omega)]

lemma update_agree (τ : Fin T → Step n L) (m : Fin T) (x : Step n L) :
    ∀ i : Fin T, (i : ℕ) < m → Function.update τ m x i = τ i := by
  intro i hi
  exact Function.update_of_ne (by intro h; rw [h] at hi; exact lt_irrefl _ hi) _ _

noncomputable def Wm (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (τ : Fin T → Step n L) : ℝ :=
  ∏ s : Fin T, if (s : ℕ) < m then stepW inst P A τ s else (Fintype.card (Step n L) : ℝ)⁻¹

noncomputable def Em (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : ℕ)
    (g : (Fin T → Step n L) → ℝ) : ℝ :=
  ∑ τ, Wm inst P A m τ * g τ

lemma Wm_nonneg (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (m : ℕ) (τ : Fin T → Step n L) :
    0 ≤ Wm inst P A m τ := by
  unfold Wm
  apply Finset.prod_nonneg
  intro s _
  split_ifs
  · exact stepW_nonneg inst P A hw_nonneg τ s
  · positivity

lemma sum_update_eq {α : Type*} [Fintype α] [DecidableEq α] (F : (Fin T → α) → ℝ) (m : Fin T) :
    ∑ τ, ∑ x, F (Function.update τ m x) = (Fintype.card α : ℝ) * ∑ τ, F τ := by
  let Φ : (Fin T → α) × α → (Fin T → α) × α := fun p => (Function.update p.1 m p.2, p.1 m)
  have hΦ : Function.Involutive Φ := by
    intro p; simp [Φ]
  calc ∑ τ, ∑ x, F (Function.update τ m x) = ∑ p : (Fin T → α) × α, F (Φ p).1 := by
        rw [Fintype.sum_prod_type]
    _ = ∑ p : (Fin T → α) × α, F p.1 :=
        Fintype.sum_equiv (hΦ.toPerm Φ) _ _ (fun p => rfl)
    _ = _ := by
        rw [Fintype.sum_prod_type]
        simp [Finset.sum_const, Finset.mul_sum]

lemma Wm_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Wm inst P A (m + 1) (Function.update τ m x) =
      (Fintype.card (Step n L) : ℝ) * Wm inst P A m τ * stepW inst P A (Function.update τ m x) m := by
  unfold Wm
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ m),
    ← Finset.mul_prod_erase Finset.univ (fun s : Fin T => if (s : ℕ) < m then stepW inst P A τ s
      else (Fintype.card (Step n L) : ℝ)⁻¹) (Finset.mem_univ m)]
  simp only [lt_add_iff_pos_right, lt_irrefl, if_false, Nat.lt_succ_self, if_true]
  have hrest : ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < (m : ℕ) + 1 then
      stepW inst P A (Function.update τ m x) s else (Fintype.card (Step n L) : ℝ)⁻¹) =
      ∏ s ∈ Finset.univ.erase m, (if (s : ℕ) < m then stepW inst P A τ s
        else (Fintype.card (Step n L) : ℝ)⁻¹) := by
    apply Finset.prod_congr rfl
    intro s hs
    have hsm : s ≠ m := Finset.ne_of_mem_erase hs
    have hsm' : (s : ℕ) ≠ m := fun h => hsm (Fin.ext h)
    by_cases hlt : (s : ℕ) < m
    · rw [if_pos (by omega), if_pos hlt]
      have e := stepW_dep inst P A s _ _ (fun i hi => update_agree τ m x i (by omega))
      beta_reduce at e
      exact e
    · rw [if_neg (by omega), if_neg hlt]
  rw [hrest]
  field_simp

lemma Em_step (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (g : (Fin T → Step n L) → ℝ) (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (m + 1) g = Em inst P A m (fun τ => ∑ x, stepW inst P A (Function.update τ m x) m *
      g (Function.update τ m x)) := by
  unfold Em
  have := sum_update_eq (fun τ => Wm inst P A (m + 1) τ * g τ) m
  have e : ∑ τ, Wm inst P A (m + 1) τ * g τ =
      (Fintype.card (Step n L) : ℝ)⁻¹ * ∑ τ, ∑ x, Wm inst P A (m + 1) (Function.update τ m x) *
        g (Function.update τ m x) := by
    rw [this]; field_simp
  rw [e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Wm_update inst P A m τ x hN]
  field_simp

lemma stepW_update (inst : Instance n) (P : Adversary n) (A : Alg n L) (m : Fin T)
    (τ : Fin T → Step n L) (x : Step n L) :
    stepW inst P A (Function.update τ m x) m = A.w (algHist τ m) x.1 *
      (P (pubHist A τ m) x.2.1).toReal * obsW inst (A.rank (algHist τ m) x.1) x.2.1 x.2.2 := by
  unfold stepW ranking
  have e1 := algHist_dep (n := n) (L := L) m _ τ (update_agree τ m x)
  have e2 := pubHist_dep A m _ τ (update_agree τ m x)
  beta_reduce at e1 e2
  rw [Function.update_self, e1, e2]

lemma stepW_sum (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (m : Fin T) (τ : Fin T → Step n L) :
    ∑ x, stepW inst P A (Function.update τ m x) m = 1 := by
  simp only [stepW_update]
  rw [Fintype.sum_prod_type]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans (hw_sum (algHist τ m))
  rw [Fintype.sum_prod_type]
  simp only [mul_assoc, ← Finset.mul_sum, obsW_sum inst _ _ hn, mul_one]
  rw [pmf_sum, mul_one]

lemma Em_drop (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : Fin T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    Em inst P A (m + 1) g = Em inst P A m g := by
  rw [Em_step inst P A m g hN]
  congr 1
  funext τ
  have : ∀ x, g (Function.update τ m x) = g τ := fun x => hg _ _ (update_agree τ m x)
  simp only [this, ← Finset.sum_mul, stepW_sum inst P A hw_sum hn m τ, one_mul]

lemma expect_eq_Em (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hN : (0 : ℝ) < Fintype.card (Step n L))
    (m : ℕ) (hm : m ≤ T) (g : (Fin T → Step n L) → ℝ) (hg : DepBelow m g) :
    expect inst P A T g = Em inst P A m g := by
  have hT : expect inst P A T g = Em inst P A T g := by
    unfold expect Em trajW Wm
    apply Finset.sum_congr rfl
    intro τ _
    congr 1
    apply Finset.prod_congr rfl
    intro s _
    rw [if_pos s.isLt]
  rw [hT]
  have key : ∀ d, m + d ≤ T → Em inst P A (m + d) g = Em inst P A m g := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      have := Em_drop inst P A hw_sum hn hN ⟨m + d, by omega⟩ g (hg.mono (by simp))
      simp only at this
      rw [← add_assoc, this, ih (by omega)]
  have := key (T - m) (by omega)
  rwa [show m + (T - m) = T by omega] at this

lemma Em_zero_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hN : (0 : ℝ) < Fintype.card (Step n L)) :
    Em inst P A (T := T) 0 (fun _ => 1) = 1 := by
  unfold Em Wm
  simp only [Nat.not_lt_zero, if_false, mul_one, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  rw [← mul_pow, mul_inv_cancel₀ hN.ne', one_pow]

lemma expect_one (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_sum : ∀ h, ∑ k, A.w h k = 1) (hn : 1 ≤ n) (hL : 1 ≤ L) :
    expect inst P A T (fun _ => 1) = 1 := by
  have hN : (0 : ℝ) < Fintype.card (Step n L) := by
    have : Nonempty (Step n L) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  rw [expect_eq_Em inst P A hw_sum hn hN 0 (Nat.zero_le _) _ (fun _ _ _ => rfl),
    Em_zero_one inst P A hN]

lemma expect_le_const (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (hw_sum : ∀ h, ∑ k, A.w h k = 1)
    (hn : 1 ≤ n) (hL : 1 ≤ L) (g : (Fin T → Step n L) → ℝ) (B : ℝ)
    (hg : ∀ τ, g τ ≤ B) :
    expect inst P A T g ≤ B := by
  calc expect inst P A T g
      ≤ expect inst P A T (fun _ => B) := by
        unfold expect
        apply Finset.sum_le_sum
        intro τ _
        exact mul_le_mul_of_nonneg_left (hg τ) (trajW_nonneg inst P A hw_nonneg τ)
    _ = B * expect inst P A T (fun _ => 1) := by
        unfold expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro τ _; ring
    _ = B := by rw [expect_one inst P A hw_sum hn hL, mul_one]

lemma expect_mono (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (hw_nonneg : ∀ h k, 0 ≤ A.w h k) (g₁ g₂ : (Fin T → Step n L) → ℝ)
    (hle : ∀ τ, g₁ τ ≤ g₂ τ) :
    expect inst P A T g₁ ≤ expect inst P A T g₂ := by
  unfold expect
  apply Finset.sum_le_sum
  intro τ _
  exact mul_le_mul_of_nonneg_left (hle τ) (trajW_nonneg inst P A hw_nonneg τ)

lemma expect_add (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (g₁ g₂ : (Fin T → Step n L) → ℝ) :
    expect inst P A T (fun τ => g₁ τ + g₂ τ) = expect inst P A T g₁ + expect inst P A T g₂ := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro τ _; ring

lemma expect_sum {ι : Type*} (s : Finset ι) (inst : Instance n) (P : Adversary n) (A : Alg n L)
    (g : ι → (Fin T → Step n L) → ℝ) :
    expect inst P A T (fun τ => ∑ i ∈ s, g i τ) = ∑ i ∈ s, expect inst P A T (g i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

def goodPrefix (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (m : ℕ) (τ : Fin T → Step n (numLevels T)) : Prop :=
  ∀ s : ℕ, 1 ≤ s → s ≤ m → GoodSt n T inst F (stateAt tb fb τ s)

lemma goodPrefix_dep (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (m : ℕ) (τ τ' : Fin T → Step n (numLevels T))
    (h : ∀ i : Fin T, (i : ℕ) < m → τ i = τ' i) :
    goodPrefix inst F tb fb m τ ↔ goodPrefix inst F tb fb m τ' := by
  unfold goodPrefix
  refine ⟨fun h1 s hs1 hsm => ?_, fun h1 s hs1 hsm => ?_⟩
  · rw [← stateAt_eq tb fb s τ τ' (fun i hi => h i (by omega))]
    exact h1 s hs1 hsm
  · rw [stateAt_eq tb fb s τ τ' (fun i hi => h i (by omega))]
    exact h1 s hs1 hsm

lemma inv_of_goodPrefix (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (m : ℕ) (hm : m ≤ T) (τ : Fin T → Step n (numLevels T))
    (hgp : goodPrefix inst F tb fb m τ) :
    ∀ s ≤ m, Inv F (stateAt tb fb τ s) := by
  obtain ⟨ha, hb, _⟩ := log_facts n T hn hT
  have hA : 0 ≤ Real.log (4 * n * T / delta n T) := by linarith
  have hB : 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by linarith
  intro s
  induction s with
  | zero => intro _; rw [stateAt_zero]; intro g _; simp [State.init]
  | succ s ih =>
    intro hsm
    obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ s (by omega)
    have hg := hgp (s + 1) (by omega) hsm
    rw [hπ] at hg ⊢
    exact inv_update T F inst hμ _ π _ _ hA hB (ih (by omega)) hg

lemma invLow_all (T : ℕ) (kStar : Fin (numLevels T))
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) :
    ∀ s ≤ T, InvLow kStar (stateAt tb fb τ s) := by
  intro s
  induction s with
  | zero => intro _; rw [stateAt_zero]; exact invLow_init kStar
  | succ s ih =>
    intro hsT
    obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ s (by omega)
    rw [hπ]
    exact invLow_update T kStar _ π _ _ (ih (by omega))

def activeB (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T)
    (τ : Fin T → Step n (numLevels T)) : Prop :=
  goodPrefix inst F tb fb t τ ∧
  4 * gamma T inst j i ≤ etaHat (stateAt tb fb τ t) kStar i ∧
  ∃ k : Fin (numLevels T), k < kStar ∧
    forcRank tb fb (algHist τ t) (stateAt tb fb τ t) k j = i

lemma activeB_dep (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T)
    (τ τ' : Fin T → Step n (numLevels T))
    (h : ∀ s : Fin T, (s : ℕ) < t → τ s = τ' s) :
    activeB inst F tb fb kStar j i t τ ↔ activeB inst F tb fb kStar j i t τ' := by
  unfold activeB
  rw [goodPrefix_dep inst F tb fb t τ τ' h,
      stateAt_eq tb fb t τ τ' h,
      algHist_eq t τ τ' h]

open Classical in
noncomputable def termBStep (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T)
    (τ : Fin T → Step n (numLevels T)) : ℝ :=
  if activeB inst F tb fb kStar j i t τ ∧
     (τ t).1 < kStar ∧ feedbackEvent (forc n T tb fb) τ t j i
  then 1 else 0

open Classical in
noncomputable def highIncStep (inst : Instance n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T)
    (τ : Fin T → Step n (numLevels T)) : ℝ :=
  ∑ σ : Fin n,
    if (stateAt tb fb τ ((t : ℕ) + 1)).cnt kStar σ = (stateAt tb fb τ t).cnt kStar σ + 1 ∧
       ((stateAt tb fb τ t).cnt kStar σ : ℝ) < 4 * gamma T inst j i
    then 1 else 0

lemma termBStep_dep (inst : Instance n) (F : ℕ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T) :
    DepBelow ((t : ℕ) + 1) (termBStep inst F tb fb kStar j i t) := by
  intro τ τ' h
  unfold termBStep feedbackEvent
  have h1 := activeB_dep inst F tb fb kStar j i t τ τ' (fun s hs => h s (by omega))
  have h2 := ranking_dep (forc n T tb fb) t τ τ' h
  have h3 := h t (by omega)
  beta_reduce at h2
  rw [h1, h2, h3]

lemma highIncStep_dep (inst : Instance n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (t : Fin T) :
    DepBelow ((t : ℕ) + 1) (highIncStep inst tb fb kStar j i t) := by
  intro τ τ' h
  unfold highIncStep
  have h1 := stateAt_eq tb fb t τ τ' (fun s hs => h s (by omega))
  have h2 := stateAt_eq tb fb ((t : ℕ) + 1) τ τ' h
  rw [h1, h2]

open Classical in
lemma step_expect_termB_le (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ) (P : Adversary n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (hkStar_pos : 1 ≤ (kStar : ℕ))
    (hkStar : F ≤ 2 ^ ((kStar : ℕ) + 1)) (hkStar_ub : 2 ^ ((kStar : ℕ) + 1) ≤ 2 * F)
    (j i : Fin n) (hji : j < i) (t : Fin T) (τ : Fin T → Step n (numLevels T)) :
    (∑ x : Step n (numLevels T),
      stepW inst P (forc n T tb fb) (Function.update τ t x) t *
        termBStep inst F tb fb kStar j i t (Function.update τ t x)) ≤
    2 * (F : ℝ) * ∑ x : Step n (numLevels T),
      stepW inst P (forc n T tb fb) (Function.update τ t x) t *
        highIncStep inst tb fb kStar j i t (Function.update τ t x) := by
  set A := forc n T tb fb
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => levelW_sum _ hL
  by_cases hact : activeB inst F tb fb kStar j i t τ
  · set st := stateAt tb fb τ t
    set h := algHist τ t
    have hgp := hact.1
    have hηi := hact.2.1
    obtain ⟨k0, hk0_lt, hk0_rank⟩ := hact.2.2
    obtain ⟨ha, _, _⟩ := log_facts n T hn hT
    have hgap_ji : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
    have hγ_pos : 0 < gamma T inst j i := by unfold gamma; positivity
    have ht1 : 1 ≤ (t : ℕ) := by
      rcases Nat.eq_zero_or_pos (t : ℕ) with ht0 | ht_pos
      · exfalso
        have hst0 : st = State.init := by
          change stateAt tb fb τ (t : ℕ) = State.init
          rw [ht0, stateAt_zero]
        have hη0 : etaHat st kStar i = 0 := by
          rw [hst0]; unfold etaHat; simp [State.init]
        linarith
      · exact ht_pos
    have hinv_all := inv_of_goodPrefix n T F hn hT inst hμ tb fb t t.isLt.le τ hgp
    have hinv_t : Inv F st := hinv_all t le_rfl
    have hinv_prev : Inv F (stateAt tb fb τ ((t : ℕ) - 1)) := hinv_all ((t : ℕ) - 1) (by omega)
    have hlow_t : InvLow kStar st := invLow_all T kStar tb fb τ t t.isLt.le
    have hkStar_nel : kStar ∉ st.elim := (hinv_t kStar hkStar).1
    let O : Finset (Fin n) := Finset.univ.filter (fun u : Fin n => (i, u) ∈ st.graph kStar)
    have hO_k0 : ∀ u ∈ O, (forcRank tb fb h st k0).symm u < j := by
      intro u hu
      exact forcRank_low_edge tb htb fb h st kStar hlow_t hkStar_nel k0 hk0_lt.le j i u
        hk0_rank (Finset.mem_filter.mp hu).2
    have hOcard : O.card ≤ (j : ℕ) := (reach_le_of_outEdges inst _ j O hO_k0).1
    set πStar := forcRank tb fb h st kStar
    obtain ⟨pStar, hpStar_le, hpStar_not_O, hreach_star⟩ :=
      exists_first_non_outEdge inst πStar j O hOcard
    set σ := πStar pStar
    have hno_i_sig : (i, σ) ∉ st.graph kStar := by
      intro hmem
      exact hpStar_not_O (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
    have hcnt_sig_lt : (st.cnt kStar σ : ℝ) < 4 * gamma T inst j i :=
      cnt_sigma_lt_four_gamma n T F hn hT inst hμ tb htb fb τ t ht1
        (hgp t ht1 le_rfl) hinv_prev hinv_t kStar hkStar j i pStar hji hpStar_le hηi hno_i_sig
    set R0 := (∏ r ∈ Finset.Iio j, (1 - inst.q r)) * ∏ u ∈ O, (1 - inst.μ u)
    have hreach_low : ∀ k : Fin (numLevels T), k < kStar →
        forcRank tb fb h st k j = i → reach inst (forcRank tb fb h st k) j ≤ R0 := by
      intro k hk_lt hrank_k
      refine (reach_le_of_outEdges inst _ j O ?_).2
      intro u hu
      exact forcRank_low_edge tb htb fb h st kStar hlow_t hkStar_nel k hk_lt.le j i u
        hrank_k (Finset.mem_filter.mp hu).2
    set p_real := (P (pubHist A τ t) none).toReal
    have hp_real_nn : 0 ≤ p_real := ENNReal.toReal_nonneg
    have hR0_nn : 0 ≤ R0 := by
      dsimp only [R0]
      apply mul_nonneg <;> apply Finset.prod_nonneg <;> intro x _
      · linarith [(inst.q_mem x).2]
      · linarith [(inst.μ_mem x).2]
    have hlhs : (∑ x : Step n (numLevels T),
        stepW inst P A (Function.update τ t x) t *
          termBStep inst F tb fb kStar j i t (Function.update τ t x)) ≤
        p_real * R0 := by
      rw [Fintype.sum_prod_type]
      calc (∑ k : Fin (numLevels T), ∑ y : Action n × Obs n,
              stepW inst P A (Function.update τ t (k, y)) t *
                termBStep inst F tb fb kStar j i t (Function.update τ t (k, y)))
          ≤ ∑ k : Fin (numLevels T), levelW (numLevels T) k * (p_real * R0) := by
            apply Finset.sum_le_sum
            intro k _
            rw [Fintype.sum_prod_type]
            have hact_none : ∀ a : Action n, a ≠ none →
                (∑ o : Obs n, stepW inst P A (Function.update τ t (k, a, o)) t *
                  termBStep inst F tb fb kStar j i t (Function.update τ t (k, a, o))) = 0 := by
              intro a ha_ne
              apply Finset.sum_eq_zero
              intro o _
              have hfb_false : ¬ feedbackEvent (forc n T tb fb) (Function.update τ t (k, a, o)) t j i := by
                intro hfb
                have := hfb.2.1
                simp [ha_ne] at this
              unfold termBStep
              rw [if_neg (by tauto), mul_zero]
            rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ (none : Action n)),
                Finset.sum_eq_zero (fun a ha => hact_none a (Finset.ne_of_mem_erase ha)), zero_add]
            have hterm_none : ∀ o : Obs n,
                stepW inst P A (Function.update τ t (k, none, o)) t *
                  termBStep inst F tb fb kStar j i t (Function.update τ t (k, none, o)) =
                levelW (numLevels T) k * p_real *
                  (realW inst (forcRank tb fb h st k) o *
                    if k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1 then 1 else 0) := by
              intro o
              rw [stepW_update]
              have hsw : A.w (algHist τ t) k * (P (pubHist A τ t) none).toReal *
                  obsW inst (A.rank (algHist τ t) k) none o =
                  levelW (numLevels T) k * p_real * realW inst (forcRank tb fb h st k) o := rfl
              rw [hsw]
              unfold termBStep
              have e_act := activeB_dep inst F tb fb kStar j i t (Function.update τ t (k, none, o)) τ (update_agree τ t (k, none, o))
              have e_hist := algHist_eq t (Function.update τ t (k, none, o)) τ (update_agree τ t (k, none, o))
              have hcond_iff : (activeB inst F tb fb kStar j i t (Function.update τ t (k, none, o)) ∧
                  (Function.update τ t (k, none, o) t).1 < kStar ∧
                  feedbackEvent (forc n T tb fb) (Function.update τ t (k, none, o)) t j i) ↔
                  (k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1) := by
                unfold feedbackEvent ranking
                rw [e_act, e_hist]
                simp [hact, forc, stateAt, h, st]
              by_cases hc : k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1
              · rw [if_pos (hcond_iff.mpr hc), if_pos hc]; ring
              · rw [if_neg (mt hcond_iff.mp hc), if_neg hc]; ring
            simp_rw [hterm_none, ← Finset.mul_sum]
            have hw_nn : 0 ≤ levelW (numLevels T) k := levelW_nonneg _ k
            by_cases hk_cond : k < kStar ∧ forcRank tb fb h st k j = i
            · have hsum_o : (∑ o : Obs n, realW inst (forcRank tb fb h st k) o *
                  (if k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1 then (1 : ℝ) else 0)) =
                  reach inst (forcRank tb fb h st k) j := by
                rw [← realW_sum_ge inst (forcRank tb fb h st k) j]
                apply Finset.sum_congr rfl
                intro o _
                by_cases h3 : j ≤ o.1 <;> simp [hk_cond.1, hk_cond.2, h3]
              rw [hsum_o]
              have hrl := hreach_low k hk_cond.1 hk_cond.2
              calc levelW (numLevels T) k * p_real * reach inst (forcRank tb fb h st k) j
                  ≤ levelW (numLevels T) k * p_real * R0 :=
                    mul_le_mul_of_nonneg_left hrl (mul_nonneg hw_nn hp_real_nn)
                _ = levelW (numLevels T) k * (p_real * R0) := by ring
            · have hsum_zero : (∑ o : Obs n, realW inst (forcRank tb fb h st k) o *
                  (if k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1 then (1 : ℝ) else 0)) = 0 := by
                apply Finset.sum_eq_zero
                intro o _
                have : ¬ (k < kStar ∧ forcRank tb fb h st k j = i ∧ j ≤ o.1) := by tauto
                simp [this]
              rw [hsum_zero, mul_zero]
              exact mul_nonneg hw_nn (mul_nonneg hp_real_nn hR0_nn)
        _ = (∑ k : Fin (numLevels T), levelW (numLevels T) k) * (p_real * R0) := by
            rw [← Finset.sum_mul]
        _ = p_real * R0 := by rw [levelW_sum _ hL, one_mul]
    have hrhs : levelW (numLevels T) kStar * (p_real * reach inst πStar pStar) ≤
        ∑ x : Step n (numLevels T),
          stepW inst P A (Function.update τ t x) t *
            highIncStep inst tb fb kStar j i t (Function.update τ t x) := by
      have hterm_nn : ∀ x : Step n (numLevels T),
          0 ≤ stepW inst P A (Function.update τ t x) t *
            highIncStep inst tb fb kStar j i t (Function.update τ t x) := by
        intro x
        apply mul_nonneg (stepW_nonneg inst P A hw_nonneg _ t)
        unfold highIncStep
        apply Finset.sum_nonneg
        intro s _; split_ifs <;> norm_num
      rw [Fintype.sum_prod_type]
      refine le_trans ?_ (Finset.single_le_sum
        (fun k _ => Finset.sum_nonneg (fun y _ => hterm_nn (k, y))) (Finset.mem_univ kStar))
      rw [Fintype.sum_prod_type]
      refine le_trans ?_ (Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg (fun o _ => hterm_nn (kStar, a, o))) (Finset.mem_univ (none : Action n)))
      rw [← realW_sum_ge inst πStar pStar, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro o _
      rw [stepW_update]
      have e_hist := algHist_eq t (Function.update τ t (kStar, none, o)) τ (update_agree τ t (kStar, none, o))
      have hsw : A.w (algHist τ t) kStar * (P (pubHist A τ t) none).toReal *
          obsW inst (A.rank (algHist τ t) kStar) none o =
          levelW (numLevels T) kStar * p_real * realW inst πStar o := rfl
      rw [hsw]
      have hw_nn : 0 ≤ levelW (numLevels T) kStar * p_real * realW inst πStar o :=
        mul_nonneg (mul_nonneg (levelW_nonneg _ kStar) hp_real_nn) (realW_nonneg inst πStar o)
      by_cases hp_le : pStar ≤ o.1
      · rw [if_pos hp_le]
        have hinc : 1 ≤ highIncStep inst tb fb kStar j i t (Function.update τ t (kStar, none, o)) := by
          unfold highIncStep
          refine le_trans ?_ (Finset.single_le_sum
            (fun s _ => by split_ifs <;> norm_num) (Finset.mem_univ σ))
          have hst_eq := stateAt_eq tb fb t (Function.update τ t (kStar, none, o)) τ
            (update_agree τ t (kStar, none, o))
          have hfb_star : feedbackEvent A (Function.update τ t (kStar, none, o)) t pStar σ := by
            unfold feedbackEvent ranking
            rw [e_hist]
            simp [A, forc, stateAt, h, st, πStar, σ, hp_le]
          have hcnt_succ := cnt_succ_of_feedback tb fb (Function.update τ t (kStar, none, o))
            t kStar pStar σ (by simp) hfb_star
          rw [hst_eq] at hcnt_succ ⊢
          rw [if_pos ⟨hcnt_succ, hcnt_sig_lt⟩]
        calc levelW (numLevels T) kStar * (p_real * (realW inst πStar o * 1))
            = (levelW (numLevels T) kStar * p_real * realW inst πStar o) * 1 := by ring
          _ ≤ (levelW (numLevels T) kStar * p_real * realW inst πStar o) *
              highIncStep inst tb fb kStar j i t (Function.update τ t (kStar, none, o)) :=
            mul_le_mul_of_nonneg_left hinc hw_nn
      · rw [if_neg hp_le, mul_zero, mul_zero, mul_zero]
        refine mul_nonneg hw_nn ?_
        unfold highIncStep
        apply Finset.sum_nonneg
        intro s _; split_ifs <;> norm_num
    have hlev_eq : levelW (numLevels T) kStar = (1 / 2 : ℝ) ^ ((kStar : ℕ) + 1) := by
      unfold levelW
      rw [if_neg (by omega)]
    have h2F : 1 ≤ 2 * (F : ℝ) * levelW (numLevels T) kStar := by
      rw [hlev_eq, one_div, inv_pow]
      have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ ((kStar : ℕ) + 1) := by positivity
      have hpow_le : (2 : ℝ) ^ ((kStar : ℕ) + 1) ≤ 2 * (F : ℝ) := by exact_mod_cast hkStar_ub
      rw [ ← div_eq_mul_inv, one_le_div hpow_pos]
      exact hpow_le
    have hF_nn : 0 ≤ 2 * (F : ℝ) := by positivity
    have hmid : p_real * R0 ≤ 2 * (F : ℝ) *
        (levelW (numLevels T) kStar * (p_real * reach inst πStar pStar)) := by
      have h1 : p_real * R0 ≤ p_real * reach inst πStar pStar :=
        mul_le_mul_of_nonneg_left hreach_star hp_real_nn
      have h2 : 0 ≤ p_real * reach inst πStar pStar := le_trans (mul_nonneg hp_real_nn hR0_nn) h1
      calc p_real * R0 ≤ 1 * (p_real * reach inst πStar pStar) := by linarith
        _ ≤ (2 * (F : ℝ) * levelW (numLevels T) kStar) * (p_real * reach inst πStar pStar) :=
          mul_le_mul_of_nonneg_right h2F h2
        _ = 2 * (F : ℝ) * (levelW (numLevels T) kStar * (p_real * reach inst πStar pStar)) := by ring
    exact le_trans hlhs (le_trans hmid (mul_le_mul_of_nonneg_left hrhs hF_nn))
  · have hlhs0 : (∑ x : Step n (numLevels T),
        stepW inst P A (Function.update τ t x) t *
          termBStep inst F tb fb kStar j i t (Function.update τ t x)) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hnot : ¬ activeB inst F tb fb kStar j i t (Function.update τ t x) := by
        rw [activeB_dep inst F tb fb kStar j i t _ τ (update_agree τ t x)]
        exact hact
      unfold termBStep
      simp [hnot]
    rw [hlhs0]
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    apply mul_nonneg (stepW_nonneg inst P A hw_nonneg _ t)
    unfold highIncStep
    apply Finset.sum_nonneg
    intro s _; split_ifs <;> norm_num

lemma expect_termBStep_le (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ) (P : Adversary n)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (hkStar_pos : 1 ≤ (kStar : ℕ))
    (hkStar : F ≤ 2 ^ ((kStar : ℕ) + 1)) (hkStar_ub : 2 ^ ((kStar : ℕ) + 1) ≤ 2 * F)
    (j i : Fin n) (hji : j < i) (t : Fin T) :
    expect inst P (forc n T tb fb) T (termBStep inst F tb fb kStar j i t) ≤
      2 * (F : ℝ) * expect inst P (forc n T tb fb) T (highIncStep inst tb fb kStar j i t) := by
  set A := forc n T tb fb
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hN : (0 : ℝ) < Fintype.card (Step n (numLevels T)) := by
    have : Nonempty (Step n (numLevels T)) := ⟨(⟨0, hL⟩, none, (⟨0, hn⟩, true))⟩
    exact_mod_cast Fintype.card_pos
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => levelW_sum _ hL
  rw [expect_eq_Em inst P A hw_sum hn hN ((t : ℕ) + 1) (by omega) _
        (termBStep_dep inst F tb fb kStar j i t),
      expect_eq_Em inst P A hw_sum hn hN ((t : ℕ) + 1) (by omega) _
        (highIncStep_dep inst tb fb kStar j i t),
      Em_step inst P A t _ hN,
      Em_step inst P A t _ hN]
  unfold Em
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro τ _
  have hW : 0 ≤ Wm inst P A t τ := Wm_nonneg inst P A hw_nonneg t τ
  have hstep := step_expect_termB_le n T F hn hT inst hμ P tb htb fb
    kStar hkStar_pos hkStar hkStar_ub j i hji t τ
  calc Wm inst P A t τ * ∑ x, stepW inst P A (Function.update τ t x) t *
          termBStep inst F tb fb kStar j i t (Function.update τ t x)
      ≤ Wm inst P A t τ * (2 * (F : ℝ) * ∑ x, stepW inst P A (Function.update τ t x) t *
          highIncStep inst tb fb kStar j i t (Function.update τ t x)) :=
        mul_le_mul_of_nonneg_left hstep hW
    _ = 2 * (F : ℝ) * (Wm inst P A t τ * ∑ x, stepW inst P A (Function.update τ t x) t *
          highIncStep inst tb fb kStar j i t (Function.update τ t x)) := by ring

lemma sum_highIncStep_pathwise (n T : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (kStar : Fin (numLevels T)) (j i : Fin n) (hji : j < i)
    (τ : Fin T → Step n (numLevels T)) :
    (∑ t : Fin T, highIncStep inst tb fb kStar j i t τ) ≤
      (n : ℝ) * (4 * gamma T inst j i + 1) := by
  unfold highIncStep
  rw [Finset.sum_comm]
  obtain ⟨ha, _, _⟩ := log_facts n T hn hT
  have hgap : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hγ_pos : 0 < gamma T inst j i := by unfold gamma; positivity
  have hB : 0 ≤ 4 * gamma T inst j i := by positivity
  calc (∑ σ : Fin n, ∑ t : Fin T,
          if (stateAt tb fb τ ((t : ℕ) + 1)).cnt kStar σ = (stateAt tb fb τ t).cnt kStar σ + 1 ∧
             ((stateAt tb fb τ t).cnt kStar σ : ℝ) < 4 * gamma T inst j i
          then (1 : ℝ) else 0)
      ≤ ∑ _σ : Fin n, (4 * gamma T inst j i + 1) := by
        apply Finset.sum_le_sum
        intro σ _
        refine sum_le_of_step_bound
          (fun m => (stateAt tb fb τ m).cnt kStar σ)
          (fun t => (stateAt tb fb τ ((t : ℕ) + 1)).cnt kStar σ = (stateAt tb fb τ t).cnt kStar σ + 1 ∧
            ((stateAt tb fb τ t).cnt kStar σ : ℝ) < 4 * gamma T inst j i)
          (4 * gamma T inst j i) hB ?_ ?_ ?_
        · rw [stateAt_zero]; rfl
        · intro t; exact cnt_succ_ge tb fb τ t kStar σ
        · intro t hP; exact hP
    _ = (n : ℝ) * (4 * gamma T inst j i + 1) := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring

lemma gamma_add_one_le (n T : ℕ) (hn : 2 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ) (j i : Fin n) (hji : j < i) :
    gamma T inst j i + 1 ≤ 321 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hgap_pos : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hgap_le : gap inst j i ≤ 1 := by
    unfold gap; linarith [(inst.μ_mem j).2, (inst.μ_mem i).1]
  have hgap2_pos : 0 < gap inst j i ^ 2 := by positivity
  have hgap2_le : gap inst j i ^ 2 ≤ 1 := by nlinarith
  have hexp_half : Real.exp (1 / 2) ≤ 2 := by
    have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
    have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hexp1 : Real.exp 1 ≤ (n : ℝ) * T := by
    have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (1 / 2 : ℝ)]
  have hlog_nT : 1 ≤ Real.log ((n : ℝ) * T) := by
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log ((n : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) hexp1
  have hone_le : 1 ≤ Real.log ((n : ℝ) * T) / gap inst j i ^ 2 := by
    rw [one_le_div hgap2_pos]
    linarith
  have e1 : 4 * (n : ℝ) * T / delta n T = 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by
    unfold delta; field_simp
  have hpow5 : 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2 ≤ ((n : ℝ) * T) ^ 5 := by
    have h4 : (4 : ℝ) ≤ (n : ℝ) * (T : ℝ) ^ 3 := by
      have : (8 : ℝ) ≤ (T : ℝ) ^ 3 := by nlinarith
      nlinarith
    have hnn : 0 ≤ (n : ℝ) ^ 4 * (T : ℝ) ^ 2 := by positivity
    calc 4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2
        = 4 * ((n : ℝ) ^ 4 * (T : ℝ) ^ 2) := by ring
      _ ≤ ((n : ℝ) * (T : ℝ) ^ 3) * ((n : ℝ) ^ 4 * (T : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = ((n : ℝ) * T) ^ 5 := by ring
  have hlog5 : Real.log (4 * (n : ℝ) * T / delta n T) ≤ 5 * Real.log ((n : ℝ) * T) := by
    rw [e1]
    calc Real.log (4 * (n : ℝ) ^ 4 * (T : ℝ) ^ 2)
        ≤ Real.log (((n : ℝ) * T) ^ 5) := Real.log_le_log (by positivity) hpow5
      _ = 5 * Real.log ((n : ℝ) * T) := by rw [Real.log_pow]; ring
  have hγ_le : gamma T inst j i ≤ 320 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) := by
    unfold gamma
    rw [show 320 * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2) =
      (64 * (5 * Real.log ((n : ℝ) * T))) / gap inst j i ^ 2 by ring]
    exact div_le_div_of_nonneg_right (by linarith) hgap2_pos.le
  linarith

end SolLemma16LowLevels

open Classical in
theorem solution :
    ∃ C : ℝ, ∀ (n T F : ℕ), 1 ≤ n → 2 ≤ T →
      ∀ (inst : Instance n), StrictAnti inst.μ →
      ∀ (P : Adversary n), WithinBudget F P →
      ∀ (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n),
        (∀ h k S, S.Nonempty → tb h k S ∈ S) →
      ∀ (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n)),
      ∀ (j i : Fin n), j < i →
        expect inst P (forc n T tb fb) T
          (fun τ => (if goodEvent inst F tb fb τ then 1 else 0) *
            ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
              feedbackEvent (forc n T tb fb) τ t j i then 1 else 0)) ≤
          C * ((n : ℝ) ^ 2 * F * (Real.log ((n : ℝ) * T) / gap inst j i ^ 2)) := by
  refine ⟨4815, fun n T F hn hT inst hμ P _hP tb htb fb j i hji => ?_⟩
  set A := forc n T tb fb
  have hn2 : 2 ≤ n := by
    have hj := j.isLt
    have hi := i.isLt
    have hji' : (j : ℕ) < (i : ℕ) := Fin.lt_def.mp hji
    omega
  have hL : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hw_nonneg : ∀ h k, 0 ≤ A.w h k := fun _ k => SolLemma16LowLevels.levelW_nonneg _ k
  have hw_sum : ∀ h, ∑ k, A.w h k = 1 := fun _ => SolLemma16LowLevels.levelW_sum _ hL
  set X := Real.log ((n : ℝ) * T) / gap inst j i ^ 2
  have hγ_bound := SolLemma16LowLevels.gamma_add_one_le n T hn2 hT inst hμ j i hji
  obtain ⟨ha, _, _⟩ := SolLemma16LowLevels.log_facts n T hn hT
  have hgap_pos : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hgap_le : gap inst j i ≤ 1 := by
    unfold gap; linarith [(inst.μ_mem j).2, (inst.μ_mem i).1]
  have hγ_ge_one : 1 ≤ gamma T inst j i := by
    unfold gamma
    rw [le_div_iff₀ (by positivity)]
    have : gap inst j i ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hX_ge_one : 1 ≤ X := by
    have : (2 : ℝ) ≤ gamma T inst j i + 1 := by linarith
    have : (2 : ℝ) ≤ 321 * X := le_trans this hγ_bound
    have hlog_ge : 1 ≤ Real.log ((n : ℝ) * T) := by
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hT' : (2 : ℝ) ≤ T := by exact_mod_cast hT
      have hexp_half : Real.exp (1 / 2) ≤ 2 := by
        have h1 := Real.add_one_le_exp (-(1 / 2 : ℝ))
        have h2 : Real.exp (-(1 / 2 : ℝ)) * Real.exp (1 / 2) = 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      have hexp1 : Real.exp 1 ≤ (n : ℝ) * T := by
        have h1 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        nlinarith [Real.exp_pos (1 / 2 : ℝ)]
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log ((n : ℝ) * T) := Real.log_le_log (Real.exp_pos 1) hexp1
    dsimp only [X]
    rw [one_le_div (by positivity)]
    have : gap inst j i ^ 2 ≤ 1 := by nlinarith
    linarith
  by_cases hF2 : F ≤ 2
  · have hzero : ∀ τ : Fin T → Step n (numLevels T),
        (if goodEvent inst F tb fb τ then (1 : ℝ) else 0) *
          ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
            feedbackEvent A τ t j i then (1 : ℝ) else 0) ≤ 0 := by
      intro τ
      have hsum0 : (∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
          feedbackEvent A τ t j i then (1 : ℝ) else 0)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        have hpow : 2 ≤ 2 ^ (((τ t).1 : ℕ) + 1) :=
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ (((τ t).1 : ℕ) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
        have hnot : ¬ (2 ^ (((τ t).1 : ℕ) + 1) < F) := by omega
        simp [hnot]
      rw [hsum0, mul_zero]
    have hexp0 := SolLemma16LowLevels.expect_le_const inst P A hw_nonneg hw_sum hn hL _ 0 hzero
    have hrhs_nn : 0 ≤ 4815 * ((n : ℝ) ^ 2 * F * X) := by positivity
    exact le_trans hexp0 hrhs_nn
  · by_cases hFL : 2 ^ (numLevels T) < F
    · have hTF : T ≤ F := by
        have h1 : T ≤ 2 ^ (numLevels T) := Nat.le_pow_clog (by norm_num) T
        omega
      have hpt_T : ∀ τ : Fin T → Step n (numLevels T),
          (if goodEvent inst F tb fb τ then (1 : ℝ) else 0) *
            ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
              feedbackEvent A τ t j i then (1 : ℝ) else 0) ≤ (F : ℝ) := by
        intro τ
        have hsum_T : (∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
            feedbackEvent A τ t j i then (1 : ℝ) else 0)) ≤ (T : ℝ) := by
          calc (∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
                  feedbackEvent A τ t j i then (1 : ℝ) else 0))
              ≤ ∑ _t : Fin T, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro t _; split_ifs <;> norm_num
            _ = (T : ℝ) := by simp
        have hTF' : (T : ℝ) ≤ (F : ℝ) := by exact_mod_cast hTF
        by_cases hG : goodEvent inst F tb fb τ
        · rw [if_pos hG, one_mul]; linarith
        · rw [if_neg hG, zero_mul]; positivity
      have hexpF := SolLemma16LowLevels.expect_le_const inst P A hw_nonneg hw_sum hn hL _ (F : ℝ) hpt_T
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hn2' : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      have hF_nn : (0 : ℝ) ≤ F := Nat.cast_nonneg F
      have hFX : (F : ℝ) ≤ (n : ℝ) ^ 2 * F * X := by
        calc (F : ℝ) = 1 * (F : ℝ) * 1 := by ring
          _ ≤ (n : ℝ) ^ 2 * (F : ℝ) * X := by
            nlinarith [mul_le_mul hn2' hX_ge_one (by norm_num) (by positivity)]
      linarith
    · have hF3 : 3 ≤ F := by omega
      have hFL_le : F ≤ 2 ^ (numLevels T) := not_lt.mp hFL
      let Shigh := Finset.univ.filter (fun k : Fin (numLevels T) => F ≤ 2 ^ ((k : ℕ) + 1))
      have hShigh_ne : Shigh.Nonempty := by
        let kmax : Fin (numLevels T) := ⟨numLevels T - 1, by omega⟩
        refine ⟨kmax, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        simp only [kmax, Nat.sub_add_cancel hL]
        exact hFL_le
      let kStar : Fin (numLevels T) := Shigh.min' hShigh_ne
      have hkStar_mem : kStar ∈ Shigh := Finset.min'_mem Shigh hShigh_ne
      have hkStar : F ≤ 2 ^ ((kStar : ℕ) + 1) := (Finset.mem_filter.mp hkStar_mem).2
      have hkStar_pos : 1 ≤ (kStar : ℕ) := by
        by_contra h0
        have hk0 : (kStar : ℕ) = 0 := by omega
        rw [hk0] at hkStar
        norm_num at hkStar
        omega
      have hkStar_ub : 2 ^ ((kStar : ℕ) + 1) ≤ 2 * F := by
        let kprev : Fin (numLevels T) := ⟨(kStar : ℕ) - 1, by omega⟩
        have hkprev_lt : kprev < kStar := by
          simp [kprev, Fin.lt_def]; omega
        have hkprev_not : kprev ∉ Shigh := fun h => not_lt_of_ge (Finset.min'_le Shigh kprev h) hkprev_lt
        have hlt_F : 2 ^ (kStar : ℕ) < F := by
          simp only [Shigh, Finset.mem_filter, Finset.mem_univ, true_and, not_le,
            kprev, Nat.sub_add_cancel hkStar_pos] at hkprev_not
          exact hkprev_not
        have hpow_succ : 2 ^ ((kStar : ℕ) + 1) = 2 * 2 ^ (kStar : ℕ) := by
          rw [pow_succ, mul_comm]
        omega
      have hlow_iff : ∀ k : Fin (numLevels T), 2 ^ ((k : ℕ) + 1) < F ↔ k < kStar := by
        intro k
        constructor
        · intro hlt
          by_contra hge
          have hle : (kStar : ℕ) ≤ (k : ℕ) := Fin.le_def.mp (not_lt.mp hge)
          have hpow : 2 ^ ((kStar : ℕ) + 1) ≤ 2 ^ ((k : ℕ) + 1) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        · intro hlt
          have hnot : k ∉ Shigh := fun h => not_lt_of_ge (Finset.min'_le Shigh k h) hlt
          simp only [Shigh, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hnot
          exact hnot
      have hpt_split : ∀ τ : Fin T → Step n (numLevels T),
          (if goodEvent inst F tb fb τ then (1 : ℝ) else 0) *
            ∑ t : Fin T, (if 2 ^ (((τ t).1 : ℕ) + 1) < F ∧
              feedbackEvent A τ t j i then (1 : ℝ) else 0) ≤
          (∑ t : Fin T,
            if (τ t).1 < kStar ∧ feedbackEvent A τ t j i ∧
               etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i
            then (1 : ℝ) else 0) +
          (∑ t : Fin T, SolLemma16LowLevels.termBStep inst F tb fb kStar j i t τ) := by
        intro τ
        by_cases hG : goodEvent inst F tb fb τ
        · rw [if_pos hG, one_mul, ← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro t _
          by_cases h1 : (τ t).1 < kStar ∧ feedbackEvent A τ t j i
          · have h1' : 2 ^ (((τ t).1 : ℕ) + 1) < F ∧ feedbackEvent A τ t j i :=
              ⟨(hlow_iff (τ t).1).mpr h1.1, h1.2⟩
            rw [if_pos h1']
            by_cases h2 : etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i
            · have hA_pos : (τ t).1 < kStar ∧ feedbackEvent A τ t j i ∧
                  etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i := ⟨h1.1, h1.2, h2⟩
              rw [if_pos hA_pos]
              have hB_nn : 0 ≤ SolLemma16LowLevels.termBStep inst F tb fb kStar j i t τ := by
                unfold SolLemma16LowLevels.termBStep; split_ifs <;> norm_num
              linarith
            · have hη_ge : 4 * gamma T inst j i ≤ etaHat (stateAt tb fb τ t) kStar i := le_of_not_gt h2
              have hgp : SolLemma16LowLevels.goodPrefix inst F tb fb t τ :=
                fun s hs1 hst => fun m hm x => hG.1 s hs1 (le_trans hst t.isLt.le) m hm x
              have hact : SolLemma16LowLevels.activeB inst F tb fb kStar j i t τ :=
                ⟨hgp, hη_ge, (τ t).1, h1.1, h1.2.1⟩
              have hB_one : SolLemma16LowLevels.termBStep inst F tb fb kStar j i t τ = 1 := by
                unfold SolLemma16LowLevels.termBStep
                rw [if_pos ⟨hact, h1.1, h1.2⟩]
              rw [hB_one]
              split_ifs <;> norm_num
          · have h1' : ¬ (2 ^ (((τ t).1 : ℕ) + 1) < F ∧ feedbackEvent A τ t j i) :=
              fun ⟨ha, hb⟩ => h1 ⟨(hlow_iff (τ t).1).mp ha, hb⟩
            rw [if_neg h1']
            apply add_nonneg
            · split_ifs <;> norm_num
            · unfold SolLemma16LowLevels.termBStep; split_ifs <;> norm_num
        · rw [if_neg hG, zero_mul]
          apply add_nonneg <;> apply Finset.sum_nonneg <;> intro t _
          · split_ifs <;> norm_num
          · unfold SolLemma16LowLevels.termBStep; split_ifs <;> norm_num
      have hexp_le := SolLemma16LowLevels.expect_mono inst P A hw_nonneg _ _ hpt_split
      rw [SolLemma16LowLevels.expect_add] at hexp_le
      have hexp_A : expect inst P A T (fun τ => ∑ t : Fin T,
          if (τ t).1 < kStar ∧ feedbackEvent A τ t j i ∧
             etaHat (stateAt tb fb τ t) kStar i < 4 * gamma T inst j i
          then (1 : ℝ) else 0) ≤ 8 * (F : ℝ) * gamma T inst j i + 1 :=
        SolLemma16LowLevels.expect_le_const inst P A hw_nonneg hw_sum hn hL _ _
          (SolLemma16LowLevels.termA_pathwise n T F hn hT inst hμ tb fb kStar hkStar_ub j i hji)
      have hexp_B : expect inst P A T (fun τ => ∑ t : Fin T,
          SolLemma16LowLevels.termBStep inst F tb fb kStar j i t τ) ≤
          2 * (F : ℝ) * ((n : ℝ) * (4 * gamma T inst j i + 1)) := by
        rw [SolLemma16LowLevels.expect_sum]
        calc (∑ t : Fin T, expect inst P A T (SolLemma16LowLevels.termBStep inst F tb fb kStar j i t))
            ≤ ∑ t : Fin T, 2 * (F : ℝ) *
                expect inst P A T (SolLemma16LowLevels.highIncStep inst tb fb kStar j i t) := by
              apply Finset.sum_le_sum
              intro t _
              exact SolLemma16LowLevels.expect_termBStep_le n T F hn hT inst hμ P tb htb fb
                kStar hkStar_pos hkStar hkStar_ub j i hji t
          _ = 2 * (F : ℝ) * expect inst P A T (fun τ => ∑ t : Fin T,
                SolLemma16LowLevels.highIncStep inst tb fb kStar j i t τ) := by
              rw [← Finset.mul_sum, SolLemma16LowLevels.expect_sum]
          _ ≤ 2 * (F : ℝ) * ((n : ℝ) * (4 * gamma T inst j i + 1)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              exact SolLemma16LowLevels.expect_le_const inst P A hw_nonneg hw_sum hn hL _ _
                (SolLemma16LowLevels.sum_highIncStep_pathwise n T hn hT inst hμ tb fb kStar j i hji)
      have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn2
      have hF' : (3 : ℝ) ≤ F := by exact_mod_cast hF3
      have htot_γ : (8 * (F : ℝ) * gamma T inst j i + 1) +
          2 * (F : ℝ) * ((n : ℝ) * (4 * gamma T inst j i + 1)) ≤
          15 * (n : ℝ) ^ 2 * F * (gamma T inst j i + 1) := by
        have h2n_sq : 2 * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have h1_le_n2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        have hFγ_nn : 0 ≤ (F : ℝ) * gamma T inst j i := by positivity
        have h1 : (F : ℝ) * gamma T inst j i ≤ (n : ℝ) ^ 2 * ((F : ℝ) * gamma T inst j i) := by
          calc (F : ℝ) * gamma T inst j i = 1 * ((F : ℝ) * gamma T inst j i) := by ring
            _ ≤ (n : ℝ) ^ 2 * ((F : ℝ) * gamma T inst j i) := mul_le_mul_of_nonneg_right h1_le_n2 hFγ_nn
        have h2 : 2 * (n : ℝ) * ((F : ℝ) * gamma T inst j i) ≤ (n : ℝ) ^ 2 * ((F : ℝ) * gamma T inst j i) :=
          mul_le_mul_of_nonneg_right h2n_sq hFγ_nn
        have h3 : (n : ℝ) * F ≤ (n : ℝ) ^ 2 * F := by nlinarith
        have h4 : (1 : ℝ) ≤ (n : ℝ) ^ 2 * F := by nlinarith
        have h5 : 0 ≤ (n : ℝ) ^ 2 * ((F : ℝ) * gamma T inst j i) := by positivity
        calc (8 * (F : ℝ) * gamma T inst j i + 1) + 2 * (F : ℝ) * ((n : ℝ) * (4 * gamma T inst j i + 1))
            = 8 * ((F : ℝ) * gamma T inst j i) + 4 * (2 * (n : ℝ) * ((F : ℝ) * gamma T inst j i)) +
              2 * ((n : ℝ) * F) + 1 := by ring
          _ ≤ 15 * ((n : ℝ) ^ 2 * ((F : ℝ) * gamma T inst j i)) + 15 * ((n : ℝ) ^ 2 * F) := by linarith
          _ = 15 * (n : ℝ) ^ 2 * F * (gamma T inst j i + 1) := by ring
      have htot_X : 15 * (n : ℝ) ^ 2 * F * (gamma T inst j i + 1) ≤
          4815 * ((n : ℝ) ^ 2 * F * X) := by
        have hnn : 0 ≤ 15 * (n : ℝ) ^ 2 * F := by positivity
        calc 15 * (n : ℝ) ^ 2 * F * (gamma T inst j i + 1)
            ≤ 15 * (n : ℝ) ^ 2 * F * (321 * X) := mul_le_mul_of_nonneg_left hγ_bound hnn
          _ = 4815 * ((n : ℝ) ^ 2 * F * X) := by ring
      linarith
