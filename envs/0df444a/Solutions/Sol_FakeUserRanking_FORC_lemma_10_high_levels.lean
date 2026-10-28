-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_10_high_levels
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T07:54:01.632359+00:00
-- url     : https://prove2.me/submissions/afb69af5-02e3-4c7b-8256-8805aa082f3f

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

set_option autoImplicit false

open FakeUserRanking.FORC

namespace SolLemma10HighLevels

variable {n L : ℕ}

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

lemma peel_spec {n : ℕ} (tb : Finset (Fin n) → Fin n)
    (htb : ∀ S : Finset (Fin n), S.Nonempty → tb S ∈ S)
    (η : Fin n → ℕ) (G : Finset (Fin n × Fin n)) (hG : ∀ e ∈ G, e.2 < e.1) :
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
    have hmin_cands : S.min' hSne ∈ cands := by
      simp only [cands, Finset.mem_filter]
      refine ⟨Finset.min'_mem S hSne, ?_⟩
      intro j hj hmem
      have hlt := hG (S.min' hSne, j) hmem
      have hle := Finset.min'_le S j hj
      exact not_lt_of_ge hle hlt
    have hcands_ne : cands.Nonempty := ⟨S.min' hSne, hmin_cands⟩
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

lemma etaHat_ge_cnt (st : State n L) (k : Fin L) (i : Fin n) :
    (st.cnt k i : ℝ) ≤ etaHat st k i := by
  unfold etaHat
  have hsum : 0 ≤ (∑ g ∈ Finset.univ.filter (fun g : Fin L => g < k), (st.cnt g i : ℝ)) /
      2 ^ ((k : ℕ) + 1) := by
    apply div_nonneg
    · exact Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
    · positivity
  linarith

lemma gamma_mono_left {T : ℕ} (inst : Instance n) (hμ : StrictAnti inst.μ)
    (hA : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T))
    (m j i : Fin n) (hmj : m ≤ j) (hji : j < i) :
    gamma T inst m i ≤ gamma T inst j i := by
  unfold gamma
  have hgap_ji : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hgap_le : gap inst j i ≤ gap inst m i := by
    unfold gap
    have := hμ.antitone hmj
    linarith
  have hsq : gap inst j i ^ 2 ≤ gap inst m i ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq

lemma cnt_lt_gamma_of_feedback (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T))
    (hgoodAt : ∀ t, 1 ≤ t → t ≤ T → GoodSt n T inst F (stateAt tb fb τ t))
    (hinvAll : ∀ t ≤ T, Inv F (stateAt tb fb τ t))
    (hA1 : 1 ≤ Real.log (4 * (n : ℝ) * T / delta n T))
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1))
    (t : Fin T) (htk : (τ t).1 = k) (hfb : feedbackEvent (forc n T tb fb) τ t j i) :
    ((stateAt tb fb τ t).cnt k i : ℝ) < gamma T inst j i := by
  set st := stateAt tb fb τ t
  set h := algHist τ t
  have hk_inv := hinvAll t t.isLt.le k hk
  have hk_elim : k ∉ st.elim := hk_inv.1
  have hk_edges : ∀ e ∈ st.graph k, e.2 < e.1 := hk_inv.2
  have hk_acyc : ¬ HasCycle (st.graph k) := not_hasCycle _ hk_edges
  obtain ⟨l, hpeel, hnd, hmem_iff, hlen, hplist⟩ :=
    peel_spec (tb h k) (htb h k) (st.cnt k) (st.graph k) hk_edges n Finset.univ (by simp)
  have hall : ∀ x, x ∈ l := fun x => (hmem_iff x).mpr (Finset.mem_univ x)
  have hcond : l.Nodup ∧ (∀ x, x ∈ l) ∧ l.length = n := ⟨hnd, hall, hlen⟩
  have hrank_eq : ranking (forc n T tb fb) τ t = listPerm l hnd hall hlen := by
    change forcRank tb fb h st (τ t).1 = _
    rw [htk]
    unfold forcRank usedGraph
    rw [if_pos hk_elim]
    dsimp only
    unfold graphRankSelect
    rw [if_neg hk_acyc, hpeel]
    dsimp only
    rw [dif_pos hcond]
  have hget_i : l[(j : ℕ)]'(by omega) = i := by
    have h1 : ranking (forc n T tb fb) τ t j = i := hfb.1
    rw [hrank_eq, listPerm_apply] at h1
    exact h1
  have hdrop_eq : l.drop (j : ℕ) = i :: l.drop ((j : ℕ) + 1) := by
    rw [List.drop_eq_getElem_cons (by omega), hget_i]
  have hplist_drop : IsPeelList (st.cnt k) (st.graph k) (i :: l.drop ((j : ℕ) + 1)) := by
    have hd := hplist.drop (j : ℕ)
    rwa [hdrop_eq] at hd
  have hno_edge : ∀ y ∈ l.drop (j : ℕ), (i, y) ∉ st.graph k := by
    cases hplist_drop with
    | cons _ _ hno _ _ =>
      intro y hy
      rw [hdrop_eq] at hy
      exact hno y hy
  have hbest : ∀ y ∈ l.drop (j : ℕ),
      (∀ z ∈ l.drop (j : ℕ), (y, z) ∉ st.graph k) → st.cnt k i ≤ st.cnt k y := by
    cases hplist_drop with
    | cons _ _ _ hb _ =>
      intro y hy hy_no
      rw [hdrop_eq] at hy
      apply hb y hy
      intro z hz
      rw [← hdrop_eq] at hz
      exact hy_no z hz
  let Sj : Finset (Fin n) := (l.drop (j : ℕ)).toFinset
  have hSj_card : Sj.card = n - (j : ℕ) := by
    change (l.drop (j : ℕ)).toFinset.card = _
    rw [List.toFinset_card_of_nodup hnd.drop, List.length_drop, hlen]
  have hIoi_card : (Finset.Ioi j).card = n - 1 - (j : ℕ) := Fin.card_Ioi j
  have hnot_sub : ¬ (Sj ⊆ Finset.Ioi j) := by
    intro hsub
    have hle := Finset.card_le_card hsub
    rw [hSj_card, hIoi_card] at hle
    have hj_lt : (j : ℕ) < n := j.isLt
    omega
  obtain ⟨m0, hm0_Sj, hm0_not⟩ := Finset.not_subset.mp hnot_sub
  have hm0_le : m0 ≤ j := not_lt.mp (Finset.mem_Ioi.not.mp hm0_not)
  have hSj_ne : Sj.Nonempty := ⟨m0, hm0_Sj⟩
  let m : Fin n := Sj.min' hSj_ne
  have hm_Sj : m ∈ Sj := Finset.min'_mem Sj hSj_ne
  have hm_drop : m ∈ l.drop (j : ℕ) := List.mem_toFinset.mp hm_Sj
  have hm_le_j : m ≤ j := le_trans (Finset.min'_le Sj m0 hm0_Sj) hm0_le
  have hmi : m < i := lt_of_le_of_lt hm_le_j hji
  have hm_no_edge : ∀ z ∈ l.drop (j : ℕ), (m, z) ∉ st.graph k := by
    intro z hz hmem
    have hz_Sj : z ∈ Sj := List.mem_toFinset.mpr hz
    have hm_le_z : m ≤ z := Finset.min'_le Sj z hz_Sj
    have hz_lt_m : z < m := hk_edges (m, z) hmem
    exact not_lt_of_ge hm_le_z hz_lt_m
  have him_not_edge : (i, m) ∉ st.graph k := hno_edge m hm_drop
  have hcnt_le : st.cnt k i ≤ st.cnt k m := hbest m hm_drop hm_no_edge
  have hA0 : 0 ≤ Real.log (4 * (n : ℝ) * T / delta n T) := by linarith
  have hgap_pos : 0 < gap inst j i := by unfold gap; have := hμ hji; linarith
  have hγ_pos : 0 < gamma T inst j i := by
    unfold gamma; positivity
  rcases Nat.eq_zero_or_pos (t : ℕ) with ht0 | ht_pos
  · have hst0 : st = State.init := by
      change stateAt tb fb τ (t : ℕ) = State.init
      rw [ht0, stateAt_zero]
    have hcnt0 : st.cnt k i = 0 := by rw [hst0]; rfl
    rw [hcnt0, Nat.cast_zero]
    exact hγ_pos
  · by_contra hnot_lt
    push_neg at hnot_lt
    have hγ_mono : gamma T inst m i ≤ gamma T inst j i :=
      gamma_mono_left inst hμ hA0 m j i hm_le_j hji
    have hcnt_i_le : (st.cnt k i : ℝ) ≤ etaHat st k i := etaHat_ge_cnt st k i
    have hcnt_m_le : (st.cnt k m : ℝ) ≤ etaHat st k m := etaHat_ge_cnt st k m
    have hcnt_im : (st.cnt k i : ℝ) ≤ (st.cnt k m : ℝ) := by exact_mod_cast hcnt_le
    have hγi : gamma T inst m i ≤ etaHat st k i := by linarith
    have hγm : gamma T inst m i ≤ etaHat st k m := by linarith
    obtain ⟨s, hs⟩ : ∃ s, (t : ℕ) = s + 1 := ⟨(t : ℕ) - 1, by omega⟩
    have hgd := hgoodAt (t : ℕ) ht_pos t.isLt.le
    have hea := edge_add n T F hn hT inst hμ st k hk hgd m i hmi hγi hγm
    obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ s (by omega)
    have hks := (hinvAll s (by omega) k hk).1
    have hst_eq : st = (stateAt tb fb τ s).update n T π (τ ⟨s, by omega⟩).1 (τ ⟨s, by omega⟩).2.2 := by
      change stateAt tb fb τ (t : ℕ) = _
      rw [hs, hπ]
    rw [hst_eq] at hea him_not_edge
    exact him_not_edge ((mem_graph_update T _ π _ _ k (i, m)).mpr (Or.inr ⟨hks, k, le_rfl, hks, hea⟩))

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

end SolLemma10HighLevels

open Classical in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (hG : goodEvent inst F tb fb τ)
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    (∑ t : Fin T, if (τ t).1 = k ∧ feedbackEvent (forc n T tb fb) τ t j i then (1 : ℝ) else 0) ≤
      gamma T inst j i + 1 := by
  obtain ⟨ha, hb, _⟩ := SolLemma10HighLevels.log_facts n T hn hT
  have hA : 0 ≤ Real.log (4 * n * T / delta n T) := by linarith
  have hB : 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by linarith
  have hgoodAt : ∀ t, 1 ≤ t → t ≤ T → SolLemma10HighLevels.GoodSt n T inst F (stateAt tb fb τ t) :=
    fun t h1 h2 m hm x => hG.1 t h1 h2 m hm x
  have hinvAll : ∀ t, t ≤ T → SolLemma10HighLevels.Inv F (stateAt tb fb τ t) := by
    intro t
    induction t with
    | zero => intro _; rw [SolLemma10HighLevels.stateAt_zero]; intro g _; simp [State.init]
    | succ t ih =>
      intro ht
      obtain ⟨π, hπ⟩ := SolLemma10HighLevels.stateAt_succ tb fb τ t (by omega)
      have hg := hgoodAt (t + 1) (by omega) ht
      rw [hπ] at hg ⊢
      exact SolLemma10HighLevels.inv_update T F inst hμ _ π _ _ hA hB (ih (by omega)) hg
  have hγ_nonneg : 0 ≤ gamma T inst j i := by
    unfold gamma; positivity
  refine SolLemma10HighLevels.sum_le_of_step_bound
    (fun m => (stateAt tb fb τ m).cnt k i)
    (fun t => (τ t).1 = k ∧ feedbackEvent (forc n T tb fb) τ t j i)
    (gamma T inst j i) hγ_nonneg ?_ ?_ ?_
  · rw [SolLemma10HighLevels.stateAt_zero]; rfl
  · intro t
    exact SolLemma10HighLevels.cnt_succ_ge tb fb τ t k i
  · intro t ⟨htk, hfb⟩
    refine ⟨SolLemma10HighLevels.cnt_succ_of_feedback tb fb τ t k j i htk hfb, ?_⟩
    exact SolLemma10HighLevels.cnt_lt_gamma_of_feedback
      n T F hn hT inst hμ tb htb fb τ hgoodAt hinvAll ha j i hji k hk t htk hfb
