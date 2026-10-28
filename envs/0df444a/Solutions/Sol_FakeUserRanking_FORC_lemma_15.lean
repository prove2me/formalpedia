-- Prove2me | solution 1 for FakeUserRanking.FORC.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:42:06.354172+00:00
-- url     : https://prove2.me/submissions/2967c335-730d-48bd-aad7-ac6593d13d43

import Mathlib
import Definitions.Def_FakeUserRanking_FORC_Model
import Definitions.Def_FakeUserRanking_FORC_Algorithm
import Definitions.Def_FakeUserRanking_FORC_GoodEvent

open FakeUserRanking.FORC

namespace L15Aux

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

lemma stateAt_succ {T : ℕ}
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (t : ℕ) (ht : t < T) :
    ∃ π, stateAt tb fb τ (t + 1) =
      (stateAt tb fb τ t).update n T π (τ ⟨t, ht⟩).1 (τ ⟨t, ht⟩).2.2 := by
  refine ⟨forcRank tb fb (algHist τ t) (stateAt tb fb τ t) (τ ⟨t, ht⟩).1, ?_⟩
  unfold stateAt
  rw [algHist_succ τ t ht, forcState_snoc]

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
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hT' : (2:ℝ) ≤ T := by exact_mod_cast hT
  have hL1 : 1 ≤ numLevels T := Nat.clog_pos (by norm_num) (by omega)
  have hLT : numLevels T ≤ T := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hL1' : (1:ℝ) ≤ numLevels T := by exact_mod_cast hL1
  have hLT' : (numLevels T : ℝ) ≤ T := by exact_mod_cast hLT
  have e1 : 4 * (n:ℝ) * T / delta n T = 4 * (n:ℝ) ^ 4 * (T:ℝ) ^ 2 := by
    unfold delta; field_simp
  have e2 : 2 * (numLevels T : ℝ) / delta n T = 2 * (numLevels T : ℝ) * (n:ℝ) ^ 3 * T := by
    unfold delta; field_simp
  rw [e1, e2]
  have hn3 : (1:ℝ) ≤ (n:ℝ) ^ 3 := one_le_pow₀ hn'
  have hn4 : (1:ℝ) ≤ (n:ℝ) ^ 4 := one_le_pow₀ hn'
  refine ⟨?_, ?_, ?_⟩
  · have : Real.exp 1 ≤ 4 * (n:ℝ) ^ 4 * (T:ℝ) ^ 2 := by
      have := Real.exp_one_lt_d9
      nlinarith
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos 1) this
  · apply Real.log_nonneg
    have : (1:ℝ) ≤ 2 * (numLevels T : ℝ) * (n:ℝ) ^ 3 := by nlinarith
    nlinarith
  · apply Real.log_le_log (by positivity)
    have h1 : (n:ℝ) ^ 3 ≤ (n:ℝ) ^ 4 := by nlinarith
    have h2 : 2 * (numLevels T : ℝ) * T ≤ 4 * (T:ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ (n:ℝ) ^ 3 := by positivity
    calc 2 * (numLevels T : ℝ) * (n:ℝ) ^ 3 * T = (n:ℝ) ^ 3 * (2 * (numLevels T : ℝ) * T) := by ring
      _ ≤ (n:ℝ) ^ 4 * (4 * (T:ℝ) ^ 2) := by
          apply mul_le_mul h1 h2 (by positivity) (by positivity)
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

lemma graph_mono (T : ℕ) (st : State n L) (π : Equiv.Perm (Fin n)) (k : Fin L) (o : Obs n)
    (g : Fin L) (e : Fin n × Fin n) (h : e ∈ st.graph g) : e ∈ (st.update n T π k o).graph g :=
  (mem_graph_update T st π k o g e).mpr (Or.inl h)

end L15Aux

open L15Aux in
theorem solution (n T F : ℕ) (hn : 1 ≤ n) (hT : 2 ≤ T)
    (inst : Instance n) (hμ : StrictAnti inst.μ)
    (tb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Finset (Fin n) → Fin n)
    (_htb : ∀ h k S, S.Nonempty → tb h k S ∈ S)
    (fb : List (Fin (numLevels T) × Obs n) → Fin (numLevels T) → Equiv.Perm (Fin n))
    (τ : Fin T → Step n (numLevels T)) (hG : goodEvent inst F tb fb τ)
    (j i : Fin n) (hji : j < i) (k : Fin (numLevels T)) (hk : F ≤ 2 ^ ((k : ℕ) + 1)) :
    (∀ t : ℕ, t ≤ T → (j, i) ∉ (stateAt tb fb τ t).graph k) ∧
    (∀ t : ℕ, 1 ≤ t → t ≤ T →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k i →
      gamma T inst j i ≤ etaHat (stateAt tb fb τ t) k j →
      ∀ t' : ℕ, t ≤ t' → t' ≤ T → (i, j) ∈ (stateAt tb fb τ t').graph k) := by
  obtain ⟨ha, hb, _⟩ := log_facts n T hn hT
  have hA : 0 ≤ Real.log (4 * n * T / delta n T) := by linarith
  have hB : 0 ≤ Real.log (2 * (numLevels T : ℝ) / delta n T) + 4 := by linarith
  have hgoodAt : ∀ t, 1 ≤ t → t ≤ T → GoodSt n T inst F (stateAt tb fb τ t) :=
    fun t h1 h2 m hm i => hG.1 t h1 h2 m hm i
  have hinvAll : ∀ t, t ≤ T → Inv F (stateAt tb fb τ t) := by
    intro t
    induction t with
    | zero => intro _; rw [stateAt_zero]; intro g _; simp [State.init]
    | succ t ih =>
      intro ht
      obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ t (by omega)
      have hg := hgoodAt (t + 1) (by omega) ht
      rw [hπ] at hg ⊢
      exact inv_update T F inst hμ _ π _ _ hA hB (ih (by omega)) hg
  refine ⟨?_, ?_⟩
  · intro t ht h
    have := (hinvAll t ht k hk).2 (j, i) h
    exact lt_asymm hji this
  · intro t ht1 htT hγi hγj
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hbase : (i, j) ∈ (stateAt tb fb τ (s + 1)).graph k := by
      have hgd := hgoodAt (s + 1) ht1 htT
      have hea := edge_add n T F hn hT inst hμ _ k hk hgd j i hji hγi hγj
      obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ s (by omega)
      have hks := (hinvAll s (by omega) k hk).1
      rw [hπ] at hea ⊢
      exact (mem_graph_update T _ π _ _ k (i, j)).mpr (Or.inr ⟨hks, k, le_rfl, hks, hea⟩)
    intro t' htt' ht'T
    induction t', htt' using Nat.le_induction with
    | base => exact hbase
    | succ t'' hle ih =>
      obtain ⟨π, hπ⟩ := stateAt_succ tb fb τ t'' (by omega)
      rw [hπ]
      exact graph_mono T _ π _ _ k _ (ih (by omega))
