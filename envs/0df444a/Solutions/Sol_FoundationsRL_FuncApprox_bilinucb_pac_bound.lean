-- Prove2me | solution 1 for FoundationsRL.FuncApprox.bilinucb_pac_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:42:30.372765+00:00
-- url     : https://prove2.me/submissions/3e86e99e-7486-42f1-980c-ab13556bbe9e

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

set_option autoImplicit false

namespace Cexf3d1

open FoundationsRL.RLBasics FoundationsRL.FuncApprox

/-- Two states (`true` = high, `false` = low), two actions, horizon 1, rewards of scale `L`. -/
noncomputable def M (L : ℝ) : EpisodicMDP Bool Bool 1 where
  P := fun _ _ _ _ => 1 / 2
  R := fun _ s a => if s then 2 * L else if a then L else 0
  d1 := fun _ => 1 / 2
  P_nonneg := by intros; norm_num
  P_sum_one := by intros; simp
  d1_nonneg := by intros; norm_num
  d1_sum_one := by simp

/-- The bad (over-optimistic) value function: claims the low-state bad action is worth `2L`. -/
noncomputable def Q1f (L : ℝ) : ℕ → Bool → Bool → ℝ :=
  fun _ s a => if s then 2 * L else if a then L else 2 * L

noncomputable def Qs (L : ℝ) : ℕ → Bool → Bool → ℝ :=
  fun h s a => if h < 1 then Qstar (M L) h s a else 0

noncomputable def qe (L : ℝ) : Bool → ℕ → Bool → Bool → ℝ :=
  fun q => cond q (Q1f L) (Qs L)

lemma isPolicy_det (g : ℕ → Bool → Bool) :
    IsPolicy 1 (detPolicy (H := 1) g : Policy Bool Bool 1) := by
  intro h _ s
  refine ⟨fun a => by unfold detPolicy; split_ifs <;> norm_num, ?_⟩
  unfold detPolicy; simp

lemma Qfun_eq (L : ℝ) (π : Policy Bool Bool 1) (s a : Bool) :
    FoundationsRL.RLBasics.Q (M L) π 0 s a = (M L).R 0 s a := by
  simp [FoundationsRL.RLBasics.Q, V, valueAux]

lemma Qstar_eq (L : ℝ) (s a : Bool) : Qstar (M L) 0 s a = (M L).R 0 s a := by
  unfold Qstar
  haveI : Nonempty {π : Policy Bool Bool 1 // IsPolicy 1 π} :=
    ⟨⟨_, isPolicy_det (fun _ _ => true)⟩⟩
  simp only [Qfun_eq]
  exact ciSup_const

lemma Vstar_eq (L : ℝ) (hL : 0 ≤ L) (s : Bool) :
    Vstar (M L) 0 s = if s then 2 * L else L := by
  unfold Vstar
  simp only [Qstar_eq]
  apply le_antisymm
  · apply ciSup_le; intro a; cases s <;> cases a <;> simp [M] <;> linarith
  · have := le_ciSup (Finite.bddAbove_range (fun a : Bool => (M L).R 0 s a)) true
    cases s <;> simpa [M] using this

lemma argmax_unique {α : Type*} (f : α → ℝ) (l : List α) (x : α) (hx : x ∈ l)
    (h : ∀ y ∈ l, y ≠ x → f y < f x) : l.argmax f = some x := by
  rcases hm : l.argmax f with _ | m
  · rw [List.argmax_eq_none] at hm; simp [hm] at hx
  · have hmem : m ∈ l := List.argmax_mem hm
    have hle := List.le_of_mem_argmax hx hm
    by_contra hne
    have := h m hmem (fun e => hne (by rw [e]))
    linarith

lemma greedy_Q1_false (L : ℝ) (hL : 0 < L) (h : ℕ) :
    greedyPolicy (qe L) true h false = false := by
  unfold greedyPolicy
  rw [argmax_unique _ _ false (by simp)]
  · rfl
  · intro y _ hy
    cases y
    · exact absurd rfl hy
    · simp [qe, Q1f]; linarith

lemma init_true (L : ℝ) (hL : 0 < L) : initValue (M L) (qe L) true = 2 * L := by
  unfold initValue
  simp only [Fintype.sum_bool, greedy_Q1_false L hL]
  simp [qe, Q1f, M]; ring

lemma init_false_lt (L : ℝ) (hL : 0 < L) : initValue (M L) (qe L) false < 2 * L := by
  unfold initValue
  simp only [Fintype.sum_bool]
  have e : ∀ s a, qe L false 0 s a = (M L).R 0 s a := by
    intro s a; simp [qe, Qs, Qstar_eq]
  rw [e, e]
  generalize greedyPolicy (qe L) false 0 true = a
  generalize greedyPolicy (qe L) false 0 false = b
  cases a <;> cases b <;> simp [M] <;> linarith

lemma bestQ_zero (L β : ℝ) (hL : 0 < L) (hβ : 0 ≤ β) (hist : List (Trajectory Bool Bool 1)) :
    bestQ (M L) (qe L) hist 1 β 0 = true := by
  unfold bestQ confSet
  rw [Finset.filter_true_of_mem (fun q _ h => by simpa using hβ)]
  rw [argmax_unique _ _ true (by simp)]
  · rfl
  · intro y _ hy
    cases y
    · rw [init_true L hL]; exact init_false_lt L hL
    · exact absurd rfl hy

lemma gap_val (L : ℝ) (hL : 0 < L) :
    (∑ s : Bool, (M L).d1 s * Vstar (M L) 0 s) -
      (∑ s : Bool, (M L).d1 s *
        V (M L) (detPolicy (greedyPolicy (qe L) true) : Policy Bool Bool 1) 0 s) = L / 2 := by
  simp only [Fintype.sum_bool, Vstar_eq L hL.le]
  simp [V, valueAux, detPolicy, Fintype.sum_bool, greedy_Q1_false L hL]
  generalize greedyPolicy (qe L) true 0 true = g
  cases g <;> simp [M] <;> ring

/-! ### Bellman rank exactly one -/

lemma resid_Qs_zero (L : ℝ) (π : Policy Bool Bool 1) :
    bellmanResidual (M L) π 0 (qe L false) = 0 := by
  have : (fun s a => qe L false 0 s a - ((M L).R 0 s a + ∑ s' : Bool, (M L).P 0 s a s' *
      (if 0 + 1 < 1 then ⨆ a' : Bool, qe L false (0 + 1) s' a' else 0))) =
      fun (_ : Bool) (_ : Bool) => (0 : ℝ) := by
    funext s a; simp [qe, Qs, Qstar_eq]
  unfold bellmanResidual
  rw [this]
  simp [layerStateActionExp]

lemma rank1 (L : ℝ) (hL : 0 < L) :
    IsBellmanRank (M L) {Q | ∃ Qf : Bool, qe L Qf = Q} 1 := by
  classical
  constructor
  · refine ⟨fun π h _ => bellmanResidual (M L) π h (Q1f L),
      fun Q _ _ => if Q = Q1f L then 1 else 0, ?_⟩
    rintro π _ Q ⟨Qf, rfl⟩ h hh
    have h0 : h = 0 := by omega
    subst h0
    simp only [Fin.sum_univ_one]
    cases Qf
    · by_cases e : qe L false = Q1f L
      · rw [if_pos e, e, mul_one]
      · rw [if_neg e, mul_zero, resid_Qs_zero]
    · simp [qe]
  · intro d hd
    by_contra hlt
    have : d = 0 := by omega
    subst this
    obtain ⟨X, W, hXW⟩ := hd
    have := hXW (detPolicy (fun _ _ => false)) (isPolicy_det _) (Q1f L) ⟨true, rfl⟩ 0 one_pos
    simp [bellmanResidual, layerStateActionExp, stateDist, detPolicy, Fintype.sum_bool,
      Q1f, M] at this
    linarith

/-! ### The output policy when the first episode starts high -/

lemma Rle (L : ℝ) (hL : 0 ≤ L) (s a : Bool) : (M L).R 0 s a ≤ 2 * L := by
  cases s <;> cases a <;> simp [M] <;> linarith

lemma empValue_le (L : ℝ) (hL : 0 ≤ L) (l : List (Trajectory Bool Bool 1)) (k : ℕ) :
    empValue (M L) l 1 k ≤ 2 * L := by
  unfold empValue batch
  simp only [Nat.cast_one, div_one, Finset.sum_range_one]
  have hlen : ((l.drop (k * 1)).take 1).length ≤ 1 := List.length_take_le _ _
  generalize (l.drop (k * 1)).take 1 = l' at hlen ⊢
  rcases l' with _ | ⟨τ, _ | ⟨τ2, t⟩⟩
  · simp; linarith
  · simpa [stateAt] using Rle L hL τ.1 (actionAt τ 0)
  · simp at hlen

lemma empValue_zero {T : ℕ} (L : ℝ) (hT : 0 < T) (hist : Fin T → Trajectory Bool Bool 1)
    (h0 : (hist ⟨0, hT⟩).1 = true) : empValue (M L) (List.ofFn hist) 1 0 = 2 * L := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  unfold empValue batch
  simp only [List.ofFn_succ, zero_mul, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Finset.sum_range_one,
    Nat.cast_one, div_one, add_zero]
  rw [Fin.mk_zero] at h0
  simp [stateAt, h0, M]

lemma output_eq {T : ℕ} (L β : ℝ) (hL : 0 < L) (hβ : 0 ≤ β) (K : ℕ) (hK : 0 < K) (hT : 0 < T)
    (hist : Fin T → Trajectory Bool Bool 1) (h0 : (hist ⟨0, hT⟩).1 = true) :
    biLinUCBOutput (M L) (qe L) (List.ofFn hist) 1 β K =
      (detPolicy (greedyPolicy (qe L) true) : Policy Bool Bool 1) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hidx : ((List.range (K' + 1)).argmax (empValue (M L) (List.ofFn hist) 1)) = some 0 := by
    rw [List.range_succ_eq_map, List.argmax_cons]
    rcases (List.map Nat.succ (List.range K')).argmax (empValue (M L) (List.ofFn hist) 1)
      with _ | c
    · rfl
    · have : ¬ (empValue (M L) (List.ofFn hist) 1 0 < empValue (M L) (List.ofFn hist) 1 c) := by
        rw [empValue_zero L hT hist h0]; exact not_lt.2 (empValue_le L hL.le _ c)
      simp [this]
  unfold biLinUCBOutput
  rw [hidx]
  simp only [Option.getD_some]
  unfold iterPolicy
  rw [bestQ_zero L β hL hβ]

/-! ### Probability bookkeeping -/

lemma sum_fin_succ_fun {X : Type} [Fintype X] {T : ℕ} (g : (Fin (T + 1) → X) → ℝ) :
    ∑ f, g f = ∑ x, ∑ rest : Fin T → X, g (Fin.cons x rest) := by
  rw [← (Fin.consEquiv (fun _ : Fin (T + 1) => X)).sum_comp, Fintype.sum_prod_type]
  rfl

lemma historyProb_cons (Mx : EpisodicMDP Bool Bool 1) (Lr : Learner Bool Bool 1) {T : ℕ}
    (x : Trajectory Bool Bool 1) (rest : Fin T → Trajectory Bool Bool 1) :
    historyProb Mx Lr (Fin.cons x rest : Fin (T + 1) → Trajectory Bool Bool 1) =
      trajProb Mx (Lr []) x * historyProb Mx (fun h => Lr (x :: h)) rest := by
  unfold historyProb
  rw [Fin.prod_univ_succ]
  simp [List.ofFn_succ]

lemma traj_sums (L : ℝ) (π : Policy Bool Bool 1) (hπ : ∀ s, π 0 s true + π 0 s false = 1) :
    (∑ τ : Trajectory Bool Bool 1, trajProb (M L) π τ) = 1 ∧
    (∑ τ : Trajectory Bool Bool 1, if τ.1 = false then trajProb (M L) π τ else 0) = 1 / 2 := by
  have key : ∀ g : Trajectory Bool Bool 1 → ℝ, (∑ τ : Trajectory Bool Bool 1, g τ) =
      ∑ s : Bool, ∑ p : Bool × Bool, g (s, fun _ => p) := by
    intro g
    rw [Fintype.sum_prod_type]
    congr 1; funext s
    exact ((Equiv.funUnique (Fin 1) (Bool × Bool)).symm.sum_comp (fun f => g (s, f))).symm
  rw [key, key]
  simp [trajProb, actionAt, nextStateAt, stateAt, M, Fintype.sum_prod_type, Fintype.sum_bool]
  have h1 := hπ true; have h2 := hπ false
  constructor <;> linarith

lemma trajProb_nonneg (L : ℝ) (π : Policy Bool Bool 1) (hπ : ∀ h s a, 0 ≤ π h s a)
    (τ : Trajectory Bool Bool 1) : 0 ≤ trajProb (M L) π τ := by
  unfold trajProb
  apply mul_nonneg (by simp [M])
  apply Finset.prod_nonneg; intro i _
  exact mul_nonneg (hπ _ _ _) (by simp [M])

lemma mass (L : ℝ) : ∀ (T : ℕ) (Lr : Learner Bool Bool 1),
    (∀ l s, Lr l 0 s true + Lr l 0 s false = 1) →
    ∑ hist : Fin T → Trajectory Bool Bool 1, historyProb (M L) Lr hist = 1 := by
  intro T
  induction T with
  | zero => intro Lr _; simp [historyProb]
  | succ T ih =>
    intro Lr hLr
    rw [sum_fin_succ_fun]
    simp_rw [historyProb_cons, ← Finset.mul_sum]
    simp_rw [ih _ (fun l s => hLr _ s), mul_one]
    exact (traj_sums L _ (hLr [])).1

lemma mass_low (L : ℝ) (T : ℕ) (Lr : Learner Bool Bool 1)
    (hLr : ∀ l s, Lr l 0 s true + Lr l 0 s false = 1) :
    ∑ hist : Fin (T + 1) → Trajectory Bool Bool 1,
      (if (hist 0).1 = false then historyProb (M L) Lr hist else 0) = 1 / 2 := by
  rw [sum_fin_succ_fun]
  simp_rw [Fin.cons_zero, historyProb_cons]
  have : ∀ x : Trajectory Bool Bool 1, (∑ rest : Fin T → Trajectory Bool Bool 1,
      (if x.1 = false then trajProb (M L) (Lr []) x *
        historyProb (M L) (fun h => Lr (x :: h)) rest else 0)) =
      if x.1 = false then trajProb (M L) (Lr []) x else 0 := by
    intro x
    split_ifs
    · rw [← Finset.mul_sum, mass L T _ (fun l s => hLr _ s), mul_one]
    · simp
  simp_rw [this]
  exact (traj_sums L _ (hLr [])).2

lemma learner_props (L β : ℝ) :
    (∀ l s, biLinUCBLearner (M L) (qe L) 1 β l 0 s true +
        biLinUCBLearner (M L) (qe L) 1 β l 0 s false = 1) ∧
    (∀ l h s a, 0 ≤ biLinUCBLearner (M L) (qe L) 1 β l h s a) := by
  constructor
  · intro l s
    simp only [biLinUCBLearner, iterPolicy, detPolicy]
    generalize greedyPolicy (qe L) _ 0 s = g
    cases g <;> simp
  · intro l h s a
    simp only [biLinUCBLearner, iterPolicy, detPolicy]
    split_ifs <;> norm_num

lemma prob_le (L β : ℝ) (T : ℕ) (hT : 0 < T)
    (E : (Fin T → Trajectory Bool Bool 1) → Prop)
    (hE : ∀ hist, E hist → (hist ⟨0, hT⟩).1 = false) :
    probEvent (M L) (biLinUCBLearner (M L) (qe L) 1 β) T E ≤ 1 / 2 := by
  obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
  obtain ⟨hs, hn⟩ := learner_props L β
  rw [← mass_low L T' _ hs]
  unfold probEvent
  apply Finset.sum_le_sum
  intro hist _
  have hp : 0 ≤ historyProb (M L) (biLinUCBLearner (M L) (qe L) 1 β) hist := by
    unfold historyProb
    exact Finset.prod_nonneg (fun t _ => trajProb_nonneg L _ (hn _) _)
  by_cases hEh : E hist
  · have := hE hist hEh
    rw [Fin.mk_zero] at this
    simp [hEh, this]
  · simp only [hEh, if_false]
    split_ifs <;> linarith

end Cexf3d1

open FoundationsRL.RLBasics FoundationsRL.FuncApprox in
theorem solution : ¬ (∃ c1 c2 c3 : ℝ, 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧
      ∀ {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
        {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
        (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
        (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) (d : ℕ),
        IsBellmanRank M {Q | ∃ Qf : Qc, qeval Qf = Q} d →
        ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ ≤ 1 →
        ∀ n K : ℕ, 0 < n → 0 < K →
          (n : ℝ) ≥ c1 * (H : ℝ) ^ 3 * d * Real.log (Fintype.card Qc / δ) / ε ^ 2 →
          (K : ℝ) ≥ c2 * H * d * Real.log (1 + (n : ℝ) / d) →
          ∀ β : ℝ,
            β = c3 * ((K : ℝ) * Real.log (Fintype.card Qc) + Real.log ((H : ℝ) * K / δ)) / n →
            probEvent M (biLinUCBLearner M qeval n β) (K * n)
                (fun histT =>
                  (∑ s : S, M.d1 s * Vstar M 0 s) -
                    (∑ s : S, M.d1 s *
                      V M (biLinUCBOutput M qeval (List.ofFn histT) n β K) 0 s) ≤ ε)
              ≥ 1 - δ) := by
  rintro ⟨c1, c2, c3, hc1, hc2, hc3, hmain⟩
  have hε : (0:ℝ) < c1 + 3 := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 2 * (c1 + 3) + 2 := ⟨_, rfl⟩
  have hL : 0 < L := by rw [hLdef]; linarith
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = ⌈c2⌉₊ + 1 := ⟨_, rfl⟩
  have hKpos : 0 < K := by omega
  have hT : 0 < K * 1 := by omega
  have hlog8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 8 by norm_num); linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hlog2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = c3 * ((K : ℝ) * Real.log (Fintype.card Bool) +
      Real.log (((1:ℕ):ℝ) * K / (1/4))) / ((1:ℕ):ℝ) := ⟨_, rfl⟩
  have hβ : 0 ≤ β := by
    have h4 : (1:ℝ) ≤ ((1:ℕ):ℝ) * K / (1/4) := by
      rw [Nat.cast_one, one_mul, le_div_iff₀ (by norm_num)]; linarith
    have := Real.log_nonneg h4
    rw [hβdef]
    apply div_nonneg _ (by norm_num)
    apply mul_nonneg hc3.le
    have hc : Real.log (↑(Fintype.card Bool)) = Real.log 2 := by simp
    rw [hc]
    have := mul_nonneg (show (0:ℝ) ≤ K by linarith) hlog2'
    linarith
  have hn : ((1:ℕ):ℝ) ≥ c1 * ((1:ℕ):ℝ) ^ 3 * ((1:ℕ):ℝ) *
      Real.log (Fintype.card Bool / (1/4)) / (c1 + 3) ^ 2 := by
    rw [ge_iff_le, div_le_iff₀ (by positivity)]
    simp only [Nat.cast_one, Fintype.card_bool, one_pow, mul_one, Nat.cast_ofNat]
    have : (2:ℝ) / (1/4) = 8 := by norm_num
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left hlog8 hc1.le, sq_nonneg (c1 - 1/2)]
  have hK : (K:ℝ) ≥ c2 * ((1:ℕ):ℝ) * ((1:ℕ):ℝ) * Real.log (1 + ((1:ℕ):ℝ) / ((1:ℕ):ℝ)) := by
    have h1 : c2 ≤ (⌈c2⌉₊ : ℝ) := Nat.le_ceil c2
    have h2 : (K:ℝ) = (⌈c2⌉₊ : ℝ) + 1 := by rw [hKdef]; push_cast; ring
    simp only [Nat.cast_one, mul_one, div_one]
    norm_num
    nlinarith
  have hP := hmain (Cexf3d1.M L) (Cexf3d1.qe L) false rfl 1 (Cexf3d1.rank1 L hL) (c1 + 3) (1/4)
    hε (by norm_num) (by norm_num) 1 K one_pos hKpos hn hK β hβdef
  have hle : probEvent (Cexf3d1.M L) (biLinUCBLearner (Cexf3d1.M L) (Cexf3d1.qe L) 1 β) (K * 1)
      (fun histT => (∑ s : Bool, (Cexf3d1.M L).d1 s * Vstar (Cexf3d1.M L) 0 s) -
        (∑ s : Bool, (Cexf3d1.M L).d1 s *
          V (Cexf3d1.M L) (biLinUCBOutput (Cexf3d1.M L) (Cexf3d1.qe L) (List.ofFn histT) 1 β K)
            0 s) ≤ c1 + 3) ≤ 1 / 2 := by
    apply Cexf3d1.prob_le L β (K * 1) hT
    intro hist hE
    by_contra hne
    rw [Bool.not_eq_false] at hne
    rw [Cexf3d1.output_eq L β hL hβ K hKpos hT hist hne, Cexf3d1.gap_val L hL] at hE
    rw [hLdef] at hE
    linarith
  exact absurd hP (not_le.2 (lt_of_le_of_lt hle (by norm_num)))
