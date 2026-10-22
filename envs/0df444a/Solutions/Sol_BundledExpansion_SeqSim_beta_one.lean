-- Prove2me | solution 1 for BundledExpansion.SeqSim.beta_one
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T10:31:05.437903+00:00
-- url     : https://prove2.me/submissions/55b15a24-d8f6-461b-ae00-591ec95dfe3f

import Mathlib
import Definitions.Def_BundledExpansion_SeqSim_Model

namespace BundledExpansion.SeqSim
open Set MeasureTheory intervalIntegral

/-! ## Part 1: basic facts -/

lemma other_ne (l : Fin 2) : other l ≠ l := by fin_cases l <;> decide

lemma sum_fin2_lo (l : Fin 2) (F : Fin 2 → ℝ) : ∑ i, F i = F l + F (other l) := by
  fin_cases l <;> simp [other, Fin.sum_univ_two] ; ring

lemma d_pos (P : Params) (hS : P.Standing) (hG : P.RatioGuard) (i : Fin 2)
    (t : ℝ) (ht : t ∈ Icc 0 P.T) : 0 < P.d i t := by
  obtain ⟨_, _, _, ha, hd⟩ := hS
  obtain ⟨h1, h2⟩ := hG t ht
  have := hd 0 t ht; have := hd 1 t ht
  have := ha 0 0; have := ha 0 1; have := ha 1 0; have := ha 1 1
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue]
    by_contra hc; push Not at hc
    nlinarith
  · simp only [Fin.mk_one, Fin.isValue]
    by_contra hc; push Not at hc
    nlinarith

lemma alpha_pos (P : Params) (hS : P.Standing) (hG : P.RatioGuard) : 0 < alpha P := by
  have hT := hS.1
  have ht : (0:ℝ) ∈ Icc 0 P.T := ⟨le_refl _, hT.le⟩
  have h0 := d_pos P hS hG 0 0 ht
  have h1 := d_pos P hS hG 1 0 ht
  obtain ⟨g1, g2⟩ := hG 0 ht
  have ha := hS.2.2.2.1
  have := ha 0 0; have := ha 0 1; have := ha 1 0; have := ha 1 1
  unfold alpha
  have := mul_lt_mul'' g1 g2 (by positivity) (by positivity)
  nlinarith [mul_pos h0 h1]

lemma uIcc_sub {P : Params} {x y : ℝ} (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) :
    uIcc x y ⊆ Icc 0 P.T := uIcc_subset_Icc hx hy

lemma d_ii (P : Params) (hR : P.Regular) (i : Fin 2) {x y : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) : IntervalIntegrable (P.d i) volume x y :=
  ((hR i).mono (uIcc_sub hx hy)).intervalIntegrable

lemma D_add (P : Params) (hR : P.Regular) (i : Fin 2) {x y z : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hz : z ∈ Icc 0 P.T) :
    D P i x y + D P i y z = D P i x z := by
  unfold D
  exact integral_add_adjacent_intervals (d_ii P hR i hx hy) (d_ii P hR i hy hz)

lemma D_nonneg (P : Params) (hS : P.Standing) (i : Fin 2) {x y : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hxy : x ≤ y) : 0 ≤ D P i x y := by
  unfold D
  apply integral_nonneg hxy
  intro u hu
  exact hS.2.2.2.2 i u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩

lemma D_lower (P : Params) (i : Fin 2) {x y m : ℝ} (hR : P.Regular)
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hxy : x ≤ y)
    (hm : ∀ t ∈ Icc 0 P.T, m ≤ P.d i t) : m * (y - x) ≤ D P i x y := by
  unfold D
  have : ∫ _ in x..y, m = m * (y - x) := by simp; ring
  rw [← this]
  apply integral_mono_on hxy intervalIntegrable_const (d_ii P hR i hx hy)
  intro u hu
  exact hm u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩

lemma D_cont_right (P : Params) (hR : P.Regular) (i : Fin 2) {s : ℝ}
    (hs : s ∈ Icc 0 P.T) (hT : 0 ≤ P.T) :
    ContinuousOn (fun t => D P i s t) (Icc 0 P.T) := by
  have h0 : (0:ℝ) ∈ Icc 0 P.T := ⟨le_refl _, hT⟩
  have hT' : P.T ∈ Icc 0 P.T := ⟨hT, le_refl _⟩
  have := continuousOn_primitive_interval' (μ := volume) (d_ii P hR i h0 hT')
    (a := s) (by rw [uIcc_of_le hT]; exact hs)
  rw [uIcc_of_le hT] at this
  exact this

lemma D_cont_left (P : Params) (hR : P.Regular) (i : Fin 2) {y : ℝ}
    (hy : y ∈ Icc 0 P.T) (hT : 0 ≤ P.T) :
    ContinuousOn (fun t => D P i t y) (Icc 0 P.T) := by
  have h0 : (0:ℝ) ∈ Icc 0 P.T := ⟨le_refl _, hT⟩
  have hc := D_cont_right P hR i h0 hT
  have : ContinuousOn (fun t => D P i 0 y - D P i 0 t) (Icc 0 P.T) :=
    continuousOn_const.sub hc
  apply this.congr
  intro t ht
  have := D_add P hR i h0 ht hy
  simp only; linarith

lemma D_left_ii (P : Params) (hR : P.Regular) (i : Fin 2) {x y z : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hz : z ∈ Icc 0 P.T) (hT : 0 ≤ P.T) :
    IntervalIntegrable (fun t => D P i t z) volume x y :=
  ((D_cont_left P hR i hz hT).mono (uIcc_sub hx hy)).intervalIntegrable

/-! ## Part 2: piecewise integrals -/

lemma mono_of_succ (τ : ℕ → ℝ) (N : ℕ) (h : ∀ k < N, τ k < τ (k + 1)) :
    ∀ i j, i ≤ j → j ≤ N → τ i ≤ τ j := by
  intro i j hij hjN
  induction j, hij using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih => exact le_trans (ih (by omega)) (h n (by omega)).le

lemma smono_of_succ (τ : ℕ → ℝ) (N : ℕ) (h : ∀ k < N, τ k < τ (k + 1)) :
    ∀ i j, i < j → j ≤ N → τ i < τ j := by
  intro i j hij hjN
  have := mono_of_succ τ N h (i+1) j hij hjN
  exact lt_of_lt_of_le (h i (by omega)) this

lemma piece_int (f : ℝ → ℝ) (τ : ℕ → ℝ) (n : ℕ) (hτ : ∀ k < n, τ k ≤ τ (k + 1))
    (g : ℕ → ℝ → ℝ) (hg : ∀ k < n, IntervalIntegrable (g k) volume (τ k) (τ (k + 1)))
    (heq : ∀ k < n, ∀ t ∈ Ioo (τ k) (τ (k + 1)), f t = g k t) :
    IntervalIntegrable f volume (τ 0) (τ n) ∧
      ∫ x in τ 0..τ n, f x = ∑ k ∈ Finset.range n, ∫ x in τ k..τ (k + 1), g k x := by
  have hfi : ∀ k < n, IntervalIntegrable f volume (τ k) (τ (k + 1)) := by
    intro k hk
    apply (hg k hk).congr_uIoo
    rw [uIoo_of_le (hτ k hk)]
    intro t ht; exact (heq k hk t ht).symm
  refine ⟨IntervalIntegrable.trans_iterate hfi, ?_⟩
  rw [← sum_integral_adjacent_intervals hfi]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  exact integral_congr_Ioo_of_le (hτ k hk) (fun t ht => heq k hk t ht)

/-! ## Part 3: supply sums -/

lemma filt_sum {α : Type} (l : List α) (p : α → Bool) (f : α → ℝ) :
    ((l.filter p).map f).sum = (l.map fun a => if p a then f a else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

lemma list_range_sum (m : ℕ) (g : ℕ → ℝ) :
    ((List.range m).map g).sum = ∑ k ∈ Finset.range m, g k := by
  induction m with
  | zero => simp
  | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma ite_sum_cut (τ : ℕ → ℝ) (N : ℕ) (hτ : ∀ k < N, τ k < τ (k + 1)) (v : ℕ → ℝ)
    (n k : ℕ) (hn : n ≤ N) (hk : k < n) (t : ℝ) (ht : t ∈ Ico (τ k) (τ (k + 1))) :
    ∑ j ∈ Finset.range n, (if τ j ≤ t then v j else 0) = ∑ j ∈ Finset.range (k + 1), v j := by
  rw [← Finset.sum_range_add_sum_Ico _ (show k + 1 ≤ n by omega)]
  have h2 : ∑ j ∈ Finset.Ico (k + 1) n, (if τ j ≤ t then v j else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    have := mono_of_succ τ N hτ (k+1) j hj.1 (by omega)
    rw [if_neg (by linarith [ht.2])]
  rw [h2, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  have := mono_of_succ τ N hτ j k (by omega) (by omega)
  rw [if_pos (by linarith [ht.1])]

lemma ite_sum_all (τ : ℕ → ℝ) (v : ℕ → ℝ) (n : ℕ) (t : ℝ) (ht : ∀ j < n, τ j ≤ t) :
    ∑ j ∈ Finset.range n, (if τ j ≤ t then v j else 0) = ∑ j ∈ Finset.range n, v j := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [if_pos (ht j hj)]

lemma D_telescope (P : Params) (hR : P.Regular) (i : Fin 2) (τ : ℕ → ℝ) (n : ℕ)
    (hin : ∀ k ≤ n, τ k ∈ Icc 0 P.T) :
    ∑ k ∈ Finset.range n, D P i (τ k) (τ (k + 1)) = D P i (τ 0) (τ n) := by
  induction n with
  | zero => simp [D]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (fun k hk => hin k (by omega))]
    exact D_add P hR i (hin 0 (by omega)) (hin n (by omega)) (hin (n+1) le_rfl)

lemma exists_piece (τ : ℕ → ℝ) (n : ℕ) (hτ : ∀ k < n, τ k < τ (k + 1)) (t : ℝ)
    (ht : t ∈ Ico (τ 0) (τ n)) : ∃ k < n, t ∈ Ico (τ k) (τ (k + 1)) := by
  induction n with
  | zero => exact absurd (lt_of_le_of_lt ht.1 ht.2) (lt_irrefl _)
  | succ n ih =>
    by_cases h : t < τ n
    · obtain ⟨k, hk, hk2⟩ := ih (fun k hk => hτ k (by omega)) ⟨ht.1, h⟩
      exact ⟨k, by omega, hk2⟩
    · exact ⟨n, by omega, ⟨not_lt.mp h, ht.2⟩⟩

/-! ## Part 4: holding from pieces -/

noncomputable def pieceHold (P : Params) (x y : ℝ) : ℝ :=
  ∑ i : Fin 2, P.h i * ∫ t in x..y, D P i t y

lemma pieceHold_nonneg (P : Params) (hS : P.Standing) {x y : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hxy : x ≤ y) : 0 ≤ pieceHold P x y := by
  unfold pieceHold
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (hS.2.2.1 i).le
  apply integral_nonneg hxy
  intro u hu
  exact D_nonneg P hS i ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩ hy hu.2

lemma holding_of_pieces (P : Params) (hR : P.Regular) (hT : 0 ≤ P.T) (plan : List Repl)
    (s e : ℝ) (τ : ℕ → ℝ) (n : ℕ) (hτ : ∀ k < n, τ k < τ (k + 1)) (h0 : τ 0 = s)
    (hn : τ n = e) (hin : ∀ k ≤ n, τ k ∈ Icc 0 P.T) (c : Fin 2 → ℕ → ℝ)
    (hexc : ∀ k < n, ∀ t ∈ Ico (τ k) (τ (k + 1)), ∀ i,
      excess P plan s i t = D P i t (τ (k + 1)) + c i k) :
    (∀ i, IntervalIntegrable (excess P plan s i) volume s e) ∧
    holding P plan s e = ∑ k ∈ Finset.range n, pieceHold P (τ k) (τ (k + 1)) +
      ∑ i : Fin 2, P.h i * ∑ k ∈ Finset.range n, (τ (k + 1) - τ k) * c i k := by
  have key : ∀ i, IntervalIntegrable (excess P plan s i) volume s e ∧
      ∫ t in s..e, excess P plan s i t = ∑ k ∈ Finset.range n,
        ((∫ t in τ k..τ (k + 1), D P i t (τ (k + 1))) + (τ (k + 1) - τ k) * c i k) := by
    intro i
    have := piece_int (excess P plan s i) τ n (fun k hk => (hτ k hk).le)
      (fun k t => D P i t (τ (k + 1)) + c i k)
      (fun k hk => (D_left_ii P hR i (hin k (by omega)) (hin (k+1) (by omega))
        (hin (k+1) (by omega)) hT).add intervalIntegrable_const)
      (fun k hk t ht => hexc k hk t (Ioo_subset_Ico_self ht) i)
    rw [h0, hn] at this
    refine ⟨this.1, ?_⟩
    rw [this.2]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [integral_add (D_left_ii P hR i (hin k (by omega)) (hin (k+1) (by omega))
        (hin (k+1) (by omega)) hT) intervalIntegrable_const]
    simp
  refine ⟨fun i => (key i).1, ?_⟩
  unfold holding pieceHold
  simp_rw [(key _).2, Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-! ## Part 5: simultaneous cycles -/

lemma sim_supply (P : Params) (C : SimCycle) (i : Fin 2) (t : ℝ) :
    excess P (C.plan P) C.start i t = ∑ k ∈ Finset.range C.K,
      (if C.τ k ≤ t then ∑ j : Fin 2, P.a i j * C.q P k j else 0) - D P i C.start t := by
  unfold excess SimCycle.plan
  rw [filt_sum, List.map_map, list_range_sum]
  simp

lemma sim_q_eq (P : Params) (hα : alpha P ≠ 0) (C : SimCycle) (k : ℕ) (i : Fin 2) :
    ∑ j : Fin 2, P.a i j * C.q P k j = D P i (C.τ k) (C.τ (k + 1)) := by
  unfold SimCycle.q
  simp only [Fin.sum_univ_two, Fin.isValue, if_pos, one_ne_zero, if_false]
  fin_cases i <;> simp <;> field_simp <;> unfold alpha <;> ring

/-- structural hypotheses on a simultaneous cycle -/
def SimStruct (P : Params) (C : SimCycle) : Prop :=
  0 ≤ C.start ∧ C.stop ≤ P.T ∧ 1 ≤ C.K ∧ C.τ 0 = C.start ∧ C.τ C.K = C.stop ∧
    (∀ k < C.K, C.τ k < C.τ (k + 1))

lemma SimStruct.mem {P : Params} {C : SimCycle} (h : SimStruct P C) :
    ∀ k ≤ C.K, C.τ k ∈ Icc 0 P.T := by
  obtain ⟨h1, h2, _, h4, h5, h6⟩ := h
  intro k hk
  have a := mono_of_succ C.τ C.K h6 0 k (by omega) hk
  have b := mono_of_succ C.τ C.K h6 k C.K hk le_rfl
  constructor <;> linarith

lemma sim_excess (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) (k : ℕ) (hk : k < C.K) (t : ℝ)
    (ht : t ∈ Ico (C.τ k) (C.τ (k + 1))) (i : Fin 2) :
    excess P (C.plan P) C.start i t = D P i t (C.τ (k + 1)) := by
  have hα := (alpha_pos P hS hG).ne'
  have hm := h.mem
  obtain ⟨_, _, _, h4, _, h6⟩ := h
  rw [sim_supply]
  simp_rw [sim_q_eq P hα C]
  rw [ite_sum_cut C.τ C.K h6 (fun j => D P i (C.τ j) (C.τ (j + 1))) C.K k le_rfl hk t ht]
  rw [D_telescope P hR i C.τ (k+1) (fun j hj => hm j (by omega)), h4]
  have htm : t ∈ Icc 0 P.T := by
    have q1 := hm k (by omega); have q2 := hm (k+1) (by omega)
    constructor <;> linarith [ht.1, ht.2, q1.1, q2.2]
  have := D_add P hR i (h4 ▸ hm 0 (by omega)) htm (hm (k+1) (by omega))
  linarith

lemma sim_excess_end (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) (i : Fin 2) :
    excess P (C.plan P) C.start i C.stop = 0 := by
  have hα := (alpha_pos P hS hG).ne'
  have hm := h.mem
  obtain ⟨_, _, _, h4, h5, h6⟩ := h
  rw [sim_supply]
  simp_rw [sim_q_eq P hα C]
  rw [ite_sum_all C.τ _ C.K C.stop (fun j hj => h5 ▸ mono_of_succ C.τ C.K h6 j C.K hj.le le_rfl)]
  rw [D_telescope P hR i C.τ C.K hm, h4, h5]
  ring

lemma sim_holding (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) :
    (∀ i, IntervalIntegrable (excess P (C.plan P) C.start i) volume C.start C.stop) ∧
    holding P (C.plan P) C.start C.stop =
      ∑ k ∈ Finset.range C.K, pieceHold P (C.τ k) (C.τ (k + 1)) := by
  have hm := h.mem
  have := holding_of_pieces P hR hS.1.le (C.plan P) C.start C.stop C.τ C.K h.2.2.2.2.2
    h.2.2.2.1 h.2.2.2.2.1 hm (fun _ _ => 0)
    (fun k hk t ht i => by rw [sim_excess P hS hR hG C h k hk t ht i]; ring)
  refine ⟨this.1, ?_⟩
  rw [this.2]; simp

lemma sim_purchase (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) :
    purchase P (C.plan P) = commonPurchase P C.start C.stop := by
  have hm := h.mem
  obtain ⟨_, _, _, h4, h5, h6⟩ := h
  unfold purchase SimCycle.plan
  rw [List.map_map, list_range_sum]
  have : ∀ k, ((fun r : Repl => ∑ j : Fin 2, P.c j * r.q j) ∘
      (fun k => (⟨C.τ k, C.q P k⟩ : Repl))) k =
      ((P.c 0 * P.a 1 1 - P.c 1 * P.a 1 0) * D P 0 (C.τ k) (C.τ (k+1)) +
      (P.c 1 * P.a 0 0 - P.c 0 * P.a 0 1) * D P 1 (C.τ k) (C.τ (k+1))) / alpha P := by
    intro k
    simp only [Function.comp, Fin.sum_univ_two, SimCycle.q]
    simp
    ring
  simp_rw [this]
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    D_telescope P hR 0 C.τ C.K hm, D_telescope P hR 1 C.τ C.K hm, h4, h5]
  rfl

/-! ## Part 6: guard integrated, sim validity -/

lemma guard_int (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    {x y : ℝ} (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hxy : x ≤ y) :
    P.a 0 1 * D P 1 x y ≤ P.a 1 1 * D P 0 x y ∧
    P.a 1 0 * D P 0 x y ≤ P.a 0 0 * D P 1 x y := by
  unfold D
  simp only [← intervalIntegral.integral_const_mul]
  have hm : ∀ u ∈ Icc x y, u ∈ Icc 0 P.T := fun u hu => ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩
  constructor
  · apply integral_mono_on hxy ((d_ii P hR 1 hx hy).const_mul _) ((d_ii P hR 0 hx hy).const_mul _)
    intro u hu; exact (hG u (hm u hu)).1.le
  · apply integral_mono_on hxy ((d_ii P hR 0 hx hy).const_mul _) ((d_ii P hR 1 hx hy).const_mul _)
    intro u hu; exact (hG u (hm u hu)).2.le

lemma SimStruct.of_valid {P : Params} {C : SimCycle} (h : C.Valid P) : SimStruct P C :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

lemma sim_valid (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) : C.Valid P := by
  have hα := alpha_pos P hS hG
  have hm := h.mem
  refine ⟨hα, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, ?_, ?_, ?_⟩
  · intro k hk j
    have g := guard_int P hS hR hG (hm k hk.le) (hm (k+1) hk) (h.2.2.2.2.2 k hk).le
    unfold SimCycle.q
    fin_cases j
    · simp; apply div_nonneg _ hα.le; linarith [g.1]
    · simp; apply div_nonneg _ hα.le; linarith [g.2]
  · intro k _ i; exact sim_q_eq P hα.ne' C k i
  · intro t ht i
    rcases eq_or_lt_of_le ht.2 with h2 | h2
    · rw [h2, sim_excess_end P hS hR hG C h i]
    · obtain ⟨k, hk, hkt⟩ := exists_piece C.τ C.K h.2.2.2.2.2 t
        ⟨h.2.2.2.1 ▸ ht.1, h.2.2.2.2.1 ▸ h2⟩
      rw [sim_excess P hS hR hG C h k hk t hkt i]
      have q1 := hm k hk.le; have q2 := hm (k+1) hk
      exact D_nonneg P hS i ⟨le_trans q1.1 hkt.1, le_trans hkt.2.le q2.2⟩ q2 hkt.2.le

lemma sim_cost_eq (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) (β : ℝ) :
    C.cost P β = β * P.A * C.K + commonPurchase P C.start C.stop +
      ∑ k ∈ Finset.range C.K, pieceHold P (C.τ k) (C.τ (k + 1)) := by
  unfold SimCycle.cost SimCycle.fixed
  rw [sim_purchase P hS hR hG C h, (sim_holding P hS hR hG C h).2]

lemma sim_cost_ge (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SimCycle) (h : SimStruct P C) (β : ℝ) :
    β * P.A * C.K + commonPurchase P C.start C.stop ≤ C.cost P β := by
  rw [sim_cost_eq P hS hR hG C h]
  have hm := h.mem
  have : 0 ≤ ∑ k ∈ Finset.range C.K, pieceHold P (C.τ k) (C.τ (k + 1)) := by
    apply Finset.sum_nonneg
    intro k hk; rw [Finset.mem_range] at hk
    exact pieceHold_nonneg P hS (hm k hk.le) (hm (k+1) hk) (h.2.2.2.2.2 k hk).le
  linarith

noncomputable def simSet (P : Params) (β : ℝ) : Set ℝ :=
  {x : ℝ | ∃ C : SimCycle, C.IsPolicy P ∧ x = C.cost P β}

lemma optSim_def (P : Params) (β : ℝ) : optSim P β = sInf (simSet P β) := rfl

lemma simSet_bdd (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (β : ℝ) (hβ : 0 ≤ β) : BddBelow (simSet P β) := by
  refine ⟨commonPurchase P 0 P.T, ?_⟩
  rintro x ⟨C, hC, rfl⟩
  have h := sim_cost_ge P hS hR hG C (SimStruct.of_valid hC.1) β
  rw [hC.2.1, hC.2.2] at h
  have : 0 ≤ β * P.A * C.K := by
    have := hS.2.1
    positivity
  linarith

def simC0 (P : Params) : SimCycle := ⟨0, P.T, 1, fun n => if n = 0 then 0 else P.T⟩

lemma simC0_policy (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard) :
    (simC0 P).IsPolicy P := by
  refine ⟨sim_valid P hS hR hG _ ⟨le_refl _, le_refl _, le_refl _, rfl, rfl, ?_⟩, rfl, rfl⟩
  intro k hk
  simp [simC0] at hk ⊢
  subst hk; simpa using hS.1

lemma simSet_ne (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (β : ℝ) : (simSet P β).Nonempty :=
  ⟨_, simC0 P, simC0_policy P hS hR hG, rfl⟩

lemma optSim_le (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (β : ℝ) (hβ : 0 ≤ β) (C : SimCycle) (hC : C.IsPolicy P) : optSim P β ≤ C.cost P β :=
  csInf_le (simSet_bdd P hS hR hG β hβ) ⟨C, hC, rfl⟩

lemma le_optSim (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (β b : ℝ) (hb : ∀ C : SimCycle, C.IsPolicy P → b ≤ C.cost P β) : b ≤ optSim P β := by
  apply le_csInf (simSet_ne P hS hR hG β)
  rintro x ⟨C, hC, rfl⟩
  exact hb C hC

lemma sim_cost_shift (P : Params) (C : SimCycle) (β β' : ℝ) :
    C.cost P β' = C.cost P β + (β' - β) * P.A * C.K := by
  unfold SimCycle.cost SimCycle.fixed; ring

theorem beta_monotone_proof (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    StrictMonoOn (optSim P) (Set.Icc (1 : ℝ) 2) := by
  intro β hβ β' hβ' hlt
  have hA := hS.2.1
  have key : optSim P β + (β' - β) * P.A ≤ optSim P β' := by
    apply le_optSim P hS hR hG
    intro C hC
    rw [sim_cost_shift P C β β']
    have h1 := optSim_le P hS hR hG β (by linarith [hβ.1]) C hC
    have hK : (1:ℝ) ≤ C.K := by exact_mod_cast hC.1.2.2.2.1
    have : (β' - β) * P.A * 1 ≤ (β' - β) * P.A * C.K :=
      mul_le_mul_of_nonneg_left hK (by nlinarith)
    linarith
  have : 0 < (β' - β) * P.A := mul_pos (by linarith) hA
  linarith

/-! ## Part 7: ratio functions and uniform constants -/

noncomputable def gl (P : Params) (l : Fin 2) (t : ℝ) : ℝ :=
  P.a l l / P.a (other l) l * P.d (other l) t - P.d l t

noncomputable def gr (P : Params) (l : Fin 2) (t : ℝ) : ℝ :=
  P.d l t - P.a l (other l) / P.a (other l) (other l) * P.d (other l) t

lemma gl_pos (P : Params) (hS : P.Standing) (hG : P.RatioGuard) (l : Fin 2) (t : ℝ)
    (ht : t ∈ Icc 0 P.T) : 0 < gl P l t := by
  have ha := hS.2.2.2.1
  obtain ⟨g1, g2⟩ := hG t ht
  unfold gl
  fin_cases l
  · simp [other]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (ha 1 0)]; linarith
  · simp [other]
    rw [div_mul_eq_mul_div, lt_div_iff₀ (ha 0 1)]; linarith

lemma gr_pos (P : Params) (hS : P.Standing) (hG : P.RatioGuard) (l : Fin 2) (t : ℝ)
    (ht : t ∈ Icc 0 P.T) : 0 < gr P l t := by
  have ha := hS.2.2.2.1
  obtain ⟨g1, g2⟩ := hG t ht
  unfold gr
  fin_cases l
  · simp [other]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (ha 1 1)]; linarith
  · simp [other]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (ha 0 0)]; linarith

lemma gl_cont (P : Params) (hR : P.Regular) (l : Fin 2) :
    ContinuousOn (gl P l) (Icc 0 P.T) :=
  (continuousOn_const.mul (hR _)).sub (hR _)

lemma gr_cont (P : Params) (hR : P.Regular) (l : Fin 2) :
    ContinuousOn (gr P l) (Icc 0 P.T) :=
  (hR _).sub (continuousOn_const.mul (hR _))

lemma int_gl (P : Params) (hR : P.Regular) (l : Fin 2) {x y : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) :
    ∫ t in x..y, gl P l t =
      P.a l l / P.a (other l) l * D P (other l) x y - D P l x y := by
  unfold gl D
  rw [integral_sub ((d_ii P hR _ hx hy).const_mul _) (d_ii P hR _ hx hy),
    intervalIntegral.integral_const_mul]

lemma int_gr (P : Params) (hR : P.Regular) (l : Fin 2) {x y : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) :
    ∫ t in x..y, gr P l t =
      D P l x y - P.a l (other l) / P.a (other l) (other l) * D P (other l) x y := by
  unfold gr D
  rw [integral_sub (d_ii P hR _ hx hy) ((d_ii P hR _ hx hy).const_mul _),
    intervalIntegral.integral_const_mul]

lemma int_lower {T : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T)) {x y m : ℝ}
    (hx : x ∈ Icc 0 T) (hy : y ∈ Icc 0 T) (hxy : x ≤ y) (hm : ∀ t ∈ Icc 0 T, m ≤ f t) :
    m * (y - x) ≤ ∫ t in x..y, f t := by
  have : ∫ _ in x..y, m = m * (y - x) := by simp; ring
  rw [← this]
  apply integral_mono_on hxy intervalIntegrable_const
    ((hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable)
  intro u hu
  exact hm u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩

lemma int_upper {T : ℝ} (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T)) {x y M : ℝ}
    (hx : x ∈ Icc 0 T) (hy : y ∈ Icc 0 T) (hxy : x ≤ y) (hM : ∀ t ∈ Icc 0 T, f t ≤ M) :
    ∫ t in x..y, f t ≤ M * (y - x) := by
  have : ∫ _ in x..y, M = M * (y - x) := by simp; ring
  rw [← this]
  apply integral_mono_on hxy ((hf.mono (uIcc_subset_Icc hx hy)).intervalIntegrable)
    intervalIntegrable_const
  intro u hu
  exact hM u ⟨le_trans hx.1 hu.1, le_trans hu.2 hy.2⟩

lemma pos_bounds {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) (hf : ContinuousOn f (Icc 0 T))
    (hpos : ∀ t ∈ Icc 0 T, 0 < f t) :
    ∃ m > 0, ∃ M, ∀ t ∈ Icc 0 T, m ≤ f t ∧ f t ≤ M := by
  have hne : (Icc 0 T).Nonempty := nonempty_Icc.2 hT
  obtain ⟨a, ha, hamin⟩ := isCompact_Icc.exists_isMinOn hne hf
  obtain ⟨b, hb, hbmax⟩ := isCompact_Icc.exists_isMaxOn hne hf
  exact ⟨f a, hpos a ha, f b, fun t ht => ⟨hamin ht, hbmax ht⟩⟩

structure Consts (P : Params) where
  m0 : ℝ
  M0 : ℝ
  m0_pos : 0 < m0
  M0_pos : 0 < M0
  hgl : ∀ l, ∀ t ∈ Icc 0 P.T, m0 ≤ gl P l t ∧ gl P l t ≤ M0
  hgr : ∀ l, ∀ t ∈ Icc 0 P.T, m0 ≤ gr P l t ∧ gr P l t ≤ M0
  hd : ∀ i, ∀ t ∈ Icc 0 P.T, m0 ≤ P.d i t

lemma consts_exist (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard) :
    Nonempty (Consts P) := by
  have hT := hS.1.le
  obtain ⟨a1, ha1, b1, h1⟩ := pos_bounds hT _ (gl_cont P hR 0) (gl_pos P hS hG 0)
  obtain ⟨a2, ha2, b2, h2⟩ := pos_bounds hT _ (gl_cont P hR 1) (gl_pos P hS hG 1)
  obtain ⟨a3, ha3, b3, h3⟩ := pos_bounds hT _ (gr_cont P hR 0) (gr_pos P hS hG 0)
  obtain ⟨a4, ha4, b4, h4⟩ := pos_bounds hT _ (gr_cont P hR 1) (gr_pos P hS hG 1)
  obtain ⟨a5, ha5, b5, h5⟩ := pos_bounds hT _ (hR 0) (d_pos P hS hG 0)
  obtain ⟨a6, ha6, b6, h6⟩ := pos_bounds hT _ (hR 1) (d_pos P hS hG 1)
  let m := min (min (min a1 a2) (min a3 a4)) (min a5 a6)
  let M := max (max (max b1 b2) (max b3 b4)) 1
  have hm1 : m ≤ a1 := by simp [m]
  have hm2 : m ≤ a2 := by simp [m]
  have hm3 : m ≤ a3 := by simp [m]
  have hm4 : m ≤ a4 := by simp [m]
  have hm5 : m ≤ a5 := by simp [m]
  have hm6 : m ≤ a6 := by simp [m]
  have hM1 : b1 ≤ M := by simp [M]
  have hM2 : b2 ≤ M := by simp [M]
  have hM3 : b3 ≤ M := by simp [M]
  have hM4 : b4 ≤ M := by simp [M]
  have hM : 1 ≤ M := by simp [M]
  refine ⟨⟨m, M, by positivity, by linarith, ?_, ?_, ?_⟩⟩
  · intro l t ht
    fin_cases l
    · exact ⟨le_trans hm1 (h1 t ht).1, le_trans (h1 t ht).2 hM1⟩
    · exact ⟨le_trans hm2 (h2 t ht).1, le_trans (h2 t ht).2 hM2⟩
  · intro l t ht
    fin_cases l
    · exact ⟨le_trans hm3 (h3 t ht).1, le_trans (h3 t ht).2 hM3⟩
    · exact ⟨le_trans hm4 (h4 t ht).1, le_trans (h4 t ht).2 hM4⟩
  · intro i t ht
    fin_cases i
    · exact le_trans hm5 (h5 t ht).1
    · exact le_trans hm6 (h6 t ht).1

/-- the equation (8) -/
def Eq8 (P : Params) (l : Fin 2) (s y e : ℝ) : Prop :=
  P.a l l / P.a (other l) l * D P (other l) s y +
    P.a l (other l) / P.a (other l) (other l) * D P (other l) y e = D P l s e

lemma eq8_int (P : Params) (hR : P.Regular) (l : Fin 2) {s y e : ℝ}
    (hs : s ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (he : e ∈ Icc 0 P.T) (h : Eq8 P l s y e) :
    ∫ t in s..y, gl P l t = ∫ t in y..e, gr P l t := by
  rw [int_gl P hR l hs hy, int_gr P hR l hy he]
  have := D_add P hR l hs hy he
  unfold Eq8 at h
  linarith

lemma root_ratio (P : Params) (hR : P.Regular) (K : Consts P) (l : Fin 2) {s y e : ℝ}
    (hs : s ∈ Icc 0 P.T) (he : e ∈ Icc 0 P.T) (hy : y ∈ Icc s e) (h : Eq8 P l s y e) :
    K.m0 / (K.m0 + K.M0) * (e - s) ≤ y - s ∧ K.m0 / (K.m0 + K.M0) * (e - s) ≤ e - y := by
  have hyT : y ∈ Icc 0 P.T := ⟨le_trans hs.1 hy.1, le_trans hy.2 he.2⟩
  have hI := eq8_int P hR l hs hyT he h
  have a1 := int_lower _ (gl_cont P hR l) hs hyT hy.1 (fun t ht => (K.hgl l t ht).1)
  have a2 := int_upper _ (gl_cont P hR l) hs hyT hy.1 (fun t ht => (K.hgl l t ht).2)
  have a3 := int_lower _ (gr_cont P hR l) hyT he hy.2 (fun t ht => (K.hgr l t ht).1)
  have a4 := int_upper _ (gr_cont P hR l) hyT he hy.2 (fun t ht => (K.hgr l t ht).2)
  have hp := K.m0_pos; have hP := K.M0_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith),
    div_le_iff₀ (by linarith)]
  constructor <;> nlinarith

lemma root_exists (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (l : Fin 2) {s e : ℝ} (hs : s ∈ Icc 0 P.T) (he : e ∈ Icc 0 P.T) (hse : s < e) :
    ∃ y ∈ Ioo s e, Eq8 P l s y e := by
  let φ : ℝ → ℝ := fun y => P.a l l / P.a (other l) l * D P (other l) s y +
    P.a l (other l) / P.a (other l) (other l) * D P (other l) y e
  have hT := hS.1.le
  have hsub : Icc s e ⊆ Icc 0 P.T := Icc_subset_Icc hs.1 he.2
  have hc : ContinuousOn φ (Icc s e) :=
    ((continuousOn_const.mul (D_cont_right P hR _ hs hT)).add
      (continuousOn_const.mul (D_cont_left P hR _ he hT))).mono hsub
  have hφs : φ s < D P l s e := by
    have := int_gr P hR l hs he
    have h2 := int_lower _ (gr_cont P hR l) hs he hse.le (fun t ht => (gr_pos P hS hG l t ht).le)
    have h3 : 0 < ∫ t in s..e, gr P l t := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        ((gr_cont P hR l).mono (uIcc_subset_Icc hs he)).intervalIntegrable _ hse
      intro t ht; exact gr_pos P hS hG l t ⟨le_trans hs.1 ht.1.le, le_trans ht.2.le he.2⟩
    simp only [φ, D, integral_same, mul_zero, zero_add] at this ⊢
    linarith
  have hφe : D P l s e < φ e := by
    have := int_gl P hR l hs he
    have h3 : 0 < ∫ t in s..e, gl P l t := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
        ((gl_cont P hR l).mono (uIcc_subset_Icc hs he)).intervalIntegrable _ hse
      intro t ht; exact gl_pos P hS hG l t ⟨le_trans hs.1 ht.1.le, le_trans ht.2.le he.2⟩
    simp only [φ, D, integral_same, mul_zero, add_zero] at this ⊢
    linarith
  obtain ⟨y, hy, hφy⟩ := intermediate_value_Ioo hse.le hc ⟨hφs, hφe⟩
  exact ⟨y, hy, hφy⟩

/-! ## Part 8: sequential cycles -/

lemma fin2_cases (l i : Fin 2) : i = l ∨ i = other l := by
  fin_cases l <;> fin_cases i <;> simp [other]

lemma sum_ite_fin2 (l : Fin 2) (x : ℝ) (g : Fin 2 → ℝ) :
    ∑ j : Fin 2, g j * (if j = l then x else 0) = g l * x := by
  fin_cases l <;> simp [Fin.sum_univ_two]

lemma seq_supply (P : Params) (C : SeqCycle) (i : Fin 2) (t : ℝ) :
    excess P (C.plan P) C.start i t =
      ∑ k ∈ Finset.range C.m, (if C.τ k ≤ t then P.a i C.lead * C.leadQ P k else 0) +
      (if C.τ C.m ≤ t then P.a i C.follow * C.followQ P else 0) - D P i C.start t := by
  unfold excess SeqCycle.plan
  rw [List.filter_append, List.map_append, List.sum_append, filt_sum, filt_sum,
    List.map_map, list_range_sum]
  simp only [Function.comp_def, decide_eq_true_eq, sum_ite_fin2, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

/-- structural hypotheses on a sequential cycle -/
def SeqStruct (P : Params) (C : SeqCycle) : Prop :=
  0 ≤ C.start ∧ C.stop ≤ P.T ∧ 1 ≤ C.m ∧ C.τ 0 = C.start ∧ C.τ (C.m + 1) = C.stop ∧
    (∀ k < C.m + 1, C.τ k < C.τ (k + 1)) ∧
    P.a C.lead C.lead * (∑ k ∈ Finset.range C.m, C.leadQ P k) +
      P.a C.lead C.follow * C.followQ P = D P C.lead C.start C.stop

lemma SeqStruct.of_valid {P : Params} {C : SeqCycle} (h : C.Valid P) : SeqStruct P C :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1⟩

lemma SeqStruct.mem {P : Params} {C : SeqCycle} (h : SeqStruct P C) :
    ∀ k ≤ C.m + 1, C.τ k ∈ Icc 0 P.T := by
  obtain ⟨h1, h2, _, h4, h5, h6, _⟩ := h
  intro k hk
  have a := mono_of_succ C.τ (C.m + 1) h6 0 k (by omega) hk
  have b := mono_of_succ C.τ (C.m + 1) h6 k (C.m + 1) hk le_rfl
  constructor <;> linarith

lemma leadQ_sum (P : Params) (hR : P.Regular) (C : SeqCycle) (h : SeqStruct P C) :
    ∑ k ∈ Finset.range C.m, C.leadQ P k =
      D P C.follow C.start (C.τ C.m) / P.a C.follow C.lead := by
  unfold SeqCycle.leadQ
  rw [← Finset.sum_div, D_telescope P hR _ C.τ C.m (fun k hk => h.mem k (by omega)), h.2.2.2.1]

lemma seq_eq8 (P : Params) (hS : P.Standing) (hR : P.Regular) (C : SeqCycle)
    (h : SeqStruct P C) : Eq8 P C.lead C.start (C.τ C.m) C.stop := by
  have he := h.2.2.2.2.2.2
  rw [leadQ_sum P hR C h] at he
  unfold SeqCycle.followQ at he
  unfold Eq8
  rw [← he]
  unfold SeqCycle.follow
  ring

noncomputable def cS (P : Params) (C : SeqCycle) (i : Fin 2) (k : ℕ) : ℝ :=
  P.a i C.lead / P.a C.follow C.lead * D P C.follow C.start (C.τ (k + 1)) -
    D P i C.start (C.τ (k + 1))

lemma seq_excess (P : Params) (hS : P.Standing) (hR : P.Regular) (C : SeqCycle)
    (h : SeqStruct P C) (k : ℕ) (hk : k < C.m) (t : ℝ)
    (ht : t ∈ Ico (C.τ k) (C.τ (k + 1))) (i : Fin 2) :
    excess P (C.plan P) C.start i t = D P i t (C.τ (k + 1)) + cS P C i k := by
  have hm := h.mem
  have h6 := h.2.2.2.2.2.1
  rw [seq_supply]
  rw [ite_sum_cut C.τ (C.m + 1) h6 (fun j => P.a i C.lead * C.leadQ P j) C.m k
    (by omega) hk t ht]
  have hf : ¬ C.τ C.m ≤ t := by
    have := mono_of_succ C.τ (C.m + 1) h6 (k+1) C.m (by omega) (by omega)
    linarith [ht.2]
  rw [if_neg hf, ← Finset.mul_sum]
  unfold SeqCycle.leadQ
  rw [← Finset.sum_div, D_telescope P hR _ C.τ (k+1) (fun j hj => hm j (by omega)),
    h.2.2.2.1]
  have htm : t ∈ Icc 0 P.T := by
    have q1 := hm k (by omega); have q2 := hm (k+1) (by omega)
    constructor <;> linarith [ht.1, ht.2, q1.1, q2.2]
  have := D_add P hR i (h.2.2.2.1 ▸ hm 0 (by omega)) htm (hm (k+1) (by omega))
  unfold cS
  rw [add_zero]
  have e : D P i C.start t = D P i C.start (C.τ (k + 1)) - D P i t (C.τ (k + 1)) := by linarith
  rw [e]; ring

lemma seq_excess_last (P : Params) (hS : P.Standing) (hR : P.Regular) (C : SeqCycle)
    (h : SeqStruct P C) (t : ℝ) (ht : t ∈ Icc (C.τ C.m) C.stop) (i : Fin 2) :
    excess P (C.plan P) C.start i t = D P i t C.stop := by
  have hm := h.mem
  have h6 := h.2.2.2.2.2.1
  rw [seq_supply]
  rw [ite_sum_all C.τ _ C.m t (fun j hj =>
    le_trans (mono_of_succ C.τ (C.m + 1) h6 j C.m hj.le (by omega)) ht.1)]
  rw [if_pos ht.1, ← Finset.mul_sum, leadQ_sum P hR C h]
  have hsT := h.2.2.2.1 ▸ hm 0 (by omega)
  have heT := h.2.2.2.2.1 ▸ hm (C.m + 1) le_rfl
  have hmT := hm C.m (by omega)
  have htm : t ∈ Icc 0 P.T := ⟨le_trans hmT.1 ht.1, le_trans ht.2 heT.2⟩
  have key : P.a i C.lead * (D P C.follow C.start (C.τ C.m) / P.a C.follow C.lead) +
      P.a i C.follow * C.followQ P = D P i C.start C.stop := by
    rcases fin2_cases C.lead i with hi | hi
    · subst hi
      have := h.2.2.2.2.2.2
      rw [leadQ_sum P hR C h] at this
      exact this
    · rw [hi]
      unfold SeqCycle.followQ
      have := D_add P hR (other C.lead) hsT hmT heT
      unfold SeqCycle.follow
      have h1 : P.a (other C.lead) C.lead ≠ 0 := (hS.2.2.2.1 _ _).ne'
      have h2 : P.a (other C.lead) (other C.lead) ≠ 0 := (hS.2.2.2.1 _ _).ne'
      field_simp
      linarith
  have := D_add P hR i hsT htm heT
  linarith

lemma cS_follow (P : Params) (hS : P.Standing) (C : SeqCycle) (k : ℕ) :
    cS P C C.follow k = 0 := by
  unfold cS
  have : P.a C.follow C.lead ≠ 0 := (hS.2.2.2.1 _ _).ne'
  field_simp; ring

lemma cS_lead (P : Params) (hR : P.Regular) (C : SeqCycle) (h : SeqStruct P C) (k : ℕ)
    (hk : k < C.m) :
    cS P C C.lead k = ∫ t in C.start..C.τ (k + 1), gl P C.lead t := by
  have hm := h.mem
  rw [int_gl P hR _ (h.2.2.2.1 ▸ hm 0 (by omega)) (hm (k+1) (by omega))]
  rfl

lemma seq_holding (P : Params) (hS : P.Standing) (hR : P.Regular) (C : SeqCycle)
    (h : SeqStruct P C) :
    (∀ i, IntervalIntegrable (excess P (C.plan P) C.start i) volume C.start C.stop) ∧
    holding P (C.plan P) C.start C.stop =
      ∑ k ∈ Finset.range (C.m + 1), pieceHold P (C.τ k) (C.τ (k + 1)) +
      P.h C.lead * ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k := by
  have hm := h.mem
  have := holding_of_pieces P hR hS.1.le (C.plan P) C.start C.stop C.τ (C.m + 1)
    h.2.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.1 hm (fun i k => if k < C.m then cS P C i k else 0)
    (by
      intro k hk t ht i
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk' | hk'
      · rw [seq_excess P hS hR C h k hk' t ht i, if_pos hk']
      · subst hk'
        rw [seq_excess_last P hS hR C h t ⟨ht.1, h.2.2.2.2.1 ▸ ht.2.le⟩ i,
          if_neg (lt_irrefl _), add_zero, h.2.2.2.2.1])
  refine ⟨this.1, ?_⟩
  rw [this.2]
  congr 1
  rw [sum_fin2_lo C.lead]
  have hf : ∑ k ∈ Finset.range (C.m + 1), (C.τ (k + 1) - C.τ k) *
      (if k < C.m then cS P C C.follow k else 0) = 0 := by
    apply Finset.sum_eq_zero; intro k _
    split_ifs
    · rw [cS_follow P hS]; ring
    · ring
  unfold SeqCycle.follow at hf
  rw [hf, mul_zero, add_zero, Finset.sum_range_succ, if_neg (lt_irrefl _), mul_zero, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  rw [if_pos hk]

lemma purchase_alg (P : Params) (hS : P.Standing) (hα : alpha P ≠ 0) (l : Fin 2)
    (s e X Y : ℝ)
    (hE : P.a l l * (X / P.a (other l) l) + P.a l (other l) * (Y / P.a (other l) (other l)) =
      D P l s e) (hF : X + Y = D P (other l) s e) :
    P.c l * (X / P.a (other l) l) + P.c (other l) * (Y / P.a (other l) (other l)) =
      commonPurchase P s e := by
  have ha := hS.2.2.2.1
  unfold commonPurchase
  unfold alpha at hα ⊢
  fin_cases l
  · simp only [other, Fin.zero_eta, Fin.isValue, if_true] at hE hF ⊢
    rw [← hE, ← hF]
    have := (ha 1 0).ne'; have := (ha 1 1).ne'
    have h' : P.a 1 1 * P.a 0 0 - P.a 1 0 * P.a 0 1 ≠ 0 := by intro h; apply hα; linarith
    have h'' : P.a 0 0 * P.a 1 1 - P.a 1 0 * P.a 0 1 ≠ 0 := by intro h; apply hα; linarith
    field_simp
    ring
  · simp only [other, Fin.mk_one, Fin.isValue, one_ne_zero, if_false] at hE hF ⊢
    rw [← hE, ← hF]
    have := (ha 0 1).ne'; have := (ha 0 0).ne'
    have h' : P.a 1 1 * P.a 0 0 - P.a 1 0 * P.a 0 1 ≠ 0 := by intro h; apply hα; linarith
    have h'' : P.a 0 0 * P.a 1 1 - P.a 1 0 * P.a 0 1 ≠ 0 := by intro h; apply hα; linarith
    field_simp
    ring

lemma seq_purchase (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (h : SeqStruct P C) :
    purchase P (C.plan P) = commonPurchase P C.start C.stop := by
  have hm := h.mem
  have hα := (alpha_pos P hS hG).ne'
  unfold purchase SeqCycle.plan
  rw [List.map_append, List.sum_append, List.map_map, list_range_sum]
  simp only [Function.comp_def, sum_ite_fin2, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  rw [← Finset.mul_sum, leadQ_sum P hR C h]
  have hsT := h.2.2.2.1 ▸ hm 0 (by omega)
  have heT := h.2.2.2.2.1 ▸ hm (C.m + 1) le_rfl
  have hmT := hm C.m (by omega)
  have hE := h.2.2.2.2.2.2
  rw [leadQ_sum P hR C h] at hE
  have hF := D_add P hR C.follow hsT hmT heT
  unfold SeqCycle.followQ at hE ⊢
  exact purchase_alg P hS hα C.lead C.start C.stop _ _ hE hF

/-! ## Part 9: sequential validity and gaps -/

lemma cS_nonneg (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (h : SeqStruct P C) (k : ℕ) (hk : k < C.m) (i : Fin 2) :
    0 ≤ cS P C i k := by
  have hm := h.mem
  rcases fin2_cases C.lead i with hi | hi
  · subst hi
    rw [cS_lead P hR C h k hk]
    have hsT := h.2.2.2.1 ▸ hm 0 (by omega)
    have := mono_of_succ C.τ (C.m+1) h.2.2.2.2.2.1 0 (k+1) (by omega) (by omega)
    rw [h.2.2.2.1] at this
    apply integral_nonneg this
    intro u hu
    exact (gl_pos P hS hG _ u ⟨le_trans hsT.1 hu.1, le_trans hu.2 (hm (k+1) (by omega)).2⟩).le
  · rw [hi]; exact (cS_follow P hS C k).ge

lemma seq_valid (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (h : SeqStruct P C) : C.Valid P := by
  have hm := h.mem
  have h6 := h.2.2.2.2.2.1
  refine ⟨alpha_pos P hS hG, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h6, ?_,
    h.2.2.2.2.2.2, ?_⟩
  · intro k hk
    have q1 := hm k (by omega); have q2 := hm (k+1) (by omega)
    have g := guard_int P hS hR hG q1 q2 (h6 k (by omega)).le
    refine ⟨?_, g.2, g.1⟩
    unfold D
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (d_ii P hR 1 q1 q2) _ (h6 k (by omega))
    intro u hu
    exact d_pos P hS hG 1 u ⟨le_trans q1.1 hu.1.le, le_trans hu.2.le q2.2⟩
  · intro t ht i
    have heT := h.2.2.2.2.1 ▸ hm (C.m + 1) le_rfl
    by_cases htm : t < C.τ C.m
    · obtain ⟨k, hk, hkt⟩ := exists_piece C.τ C.m (fun k hk => h6 k (by omega)) t
        ⟨h.2.2.2.1 ▸ ht.1, htm⟩
      rw [seq_excess P hS hR C h k hk t hkt i]
      have q1 := hm k (by omega); have q2 := hm (k+1) (by omega)
      have := D_nonneg P hS i ⟨le_trans q1.1 hkt.1, le_trans hkt.2.le q2.2⟩ q2 hkt.2.le
      linarith [cS_nonneg P hS hR hG C h k hk i]
    · push Not at htm
      rw [seq_excess_last P hS hR C h t ⟨htm, ht.2⟩ i]
      have q1 := hm C.m (by omega)
      exact D_nonneg P hS i ⟨le_trans q1.1 htm, le_trans ht.2 heT.2⟩ heT ht.2

lemma seq_cost_eq (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (h : SeqStruct P C) :
    C.cost P = P.A * (C.m + 1) + commonPurchase P C.start C.stop +
      holding P (C.plan P) C.start C.stop := by
  unfold SeqCycle.cost SeqCycle.fixed
  rw [seq_purchase P hS hR hG C h]

lemma mono0 (τ : ℕ → ℝ) (n : ℕ) (hτ : ∀ k < n, τ k ≤ τ (k + 1)) : τ 0 ≤ τ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (ih (fun k hk => hτ k (by omega))) (hτ n (by omega))

lemma riemann (τ : ℕ → ℝ) (n : ℕ) (hτ : ∀ k < n, τ k ≤ τ (k + 1)) :
    (τ n - τ 0) ^ 2 / 2 ≤
      ∑ k ∈ Finset.range n, (τ (k + 1) - τ k) * (τ (k + 1) - τ 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have := ih (fun k hk => hτ k (by omega))
    have h1 := hτ n (by omega)
    have h2 : 0 ≤ τ n - τ 0 := by
      have := mono0 τ n (fun k hk => hτ k (by omega))
      linarith
    nlinarith [mul_nonneg h2 (sub_nonneg.mpr h1)]

noncomputable def hmin (P : Params) : ℝ := min (P.h 0) (P.h 1)

lemma hmin_pos (P : Params) (hS : P.Standing) : 0 < hmin P :=
  lt_min (hS.2.2.1 0) (hS.2.2.1 1)

lemma hmin_le (P : Params) (i : Fin 2) : hmin P ≤ P.h i := by
  fin_cases i
  · exact min_le_left _ _
  · exact min_le_right _ _

noncomputable def Consts.θ {P : Params} (K : Consts P) : ℝ := K.m0 / (K.m0 + K.M0)

lemma Consts.θ_pos {P : Params} (K : Consts P) : 0 < K.θ := by
  unfold Consts.θ; have := K.m0_pos; have := K.M0_pos; positivity

lemma seq_gap1 (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (K : Consts P) (C : SeqCycle) (h : SeqStruct P C) :
    ∑ k ∈ Finset.range (C.m + 1), pieceHold P (C.τ k) (C.τ (k + 1)) +
      hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 / 2 ≤
      holding P (C.plan P) C.start C.stop := by
  rw [(seq_holding P hS hR C h).2]
  have hm := h.mem
  have h6 := h.2.2.2.2.2.1
  have hsT := h.2.2.2.1 ▸ hm 0 (by omega)
  have heT := h.2.2.2.2.1 ▸ hm (C.m + 1) le_rfl
  have hmT := hm C.m (by omega)
  -- lower bound on the sum
  have hsum : K.m0 * ((C.τ C.m - C.τ 0) ^ 2 / 2) ≤
      ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k := by
    have r := riemann C.τ C.m (fun k hk => (h6 k (by omega)).le)
    have : ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * (K.m0 * (C.τ (k + 1) - C.τ 0)) ≤
        ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k := by
      apply Finset.sum_le_sum
      intro k hk; rw [Finset.mem_range] at hk
      apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (h6 k (by omega)).le)
      rw [cS_lead P hR C h k hk, ← h.2.2.2.1]
      exact int_lower _ (gl_cont P hR _) (h.2.2.2.1 ▸ hsT) (hm (k+1) (by omega))
        (mono_of_succ C.τ (C.m+1) h6 0 (k+1) (by omega) (by omega))
        (fun t ht => (K.hgl _ t ht).1)
    have e : ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * (K.m0 * (C.τ (k + 1) - C.τ 0)) =
        K.m0 * ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * (C.τ (k + 1) - C.τ 0) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    rw [e] at this
    nlinarith [K.m0_pos]
  have hr := root_ratio P hR K C.lead hsT heT
    ⟨by rw [← h.2.2.2.1]; exact mono_of_succ C.τ (C.m+1) h6 0 C.m (by omega) (by omega),
     by rw [← h.2.2.2.2.1]; exact (h6 C.m (by omega)).le⟩ (seq_eq8 P hS hR C h)
  have hθ : K.θ * (C.stop - C.start) ≤ C.τ C.m - C.τ 0 := by
    rw [h.2.2.2.1]; exact hr.1
  have hθ0 := K.θ_pos
  have hes : 0 ≤ C.stop - C.start := by
    have := mono_of_succ C.τ (C.m+1) h6 0 (C.m+1) (by omega) le_rfl
    rw [h.2.2.2.1, h.2.2.2.2.1] at this; linarith
  have hsq : (K.θ * (C.stop - C.start)) ^ 2 ≤ (C.τ C.m - C.τ 0) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hθ 2
  have hh := hmin_le P C.lead
  have hS0 : 0 ≤ ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k := by
    have : 0 ≤ K.m0 * ((C.τ C.m - C.τ 0) ^ 2 / 2) := by have := K.m0_pos; positivity
    linarith
  have hm0 := K.m0_pos
  have hmp := hmin_pos P hS
  have step1 : hmin P * (K.m0 * ((K.θ * (C.stop - C.start)) ^ 2 / 2)) ≤
      hmin P * ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k := by
    apply mul_le_mul_of_nonneg_left _ hmp.le
    nlinarith
  have step2 : hmin P * ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k ≤
      P.h C.lead * ∑ k ∈ Finset.range C.m, (C.τ (k + 1) - C.τ k) * cS P C C.lead k :=
    mul_le_mul_of_nonneg_right hh hS0
  have : hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 / 2 =
      hmin P * (K.m0 * ((K.θ * (C.stop - C.start)) ^ 2 / 2)) := by ring
  linarith

lemma pieceHold_split (P : Params) (hR : P.Regular) (hT : 0 ≤ P.T) {x y z : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hz : z ∈ Icc 0 P.T) :
    pieceHold P x z = pieceHold P x y + pieceHold P y z +
      (y - x) * ∑ i : Fin 2, P.h i * D P i y z := by
  unfold pieceHold
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← integral_add_adjacent_intervals (D_left_ii P hR i hx hy hz hT)
    (D_left_ii P hR i hy hz hz hT)]
  have : ∫ t in x..y, D P i t z = ∫ t in x..y, (D P i t y + D P i y z) := by
    apply integral_congr
    intro t ht
    have htT : t ∈ Icc 0 P.T := uIcc_sub hx hy ht
    exact (D_add P hR i htT hy hz).symm
  rw [this, integral_add (D_left_ii P hR i hx hy hy hT) intervalIntegrable_const]
  simp
  ring

lemma seq_gap2 (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (K : Consts P) (C : SeqCycle) (h : SeqStruct P C) (hm1 : C.m = 1) :
    holding P (C.plan P) C.start C.stop ≤
      pieceHold P C.start C.stop - hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 := by
  rw [(seq_holding P hS hR C h).2]
  have hm := h.mem
  have h6 := h.2.2.2.2.2.1
  have hsT := h.2.2.2.1 ▸ hm 0 (by omega)
  have heT := h.2.2.2.2.1 ▸ hm (C.m + 1) le_rfl
  have hE := seq_eq8 P hS hR C h
  rw [hm1] at hE h6 hm ⊢
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have h0 := h.2.2.2.1
  have h2 := h.2.2.2.2.1
  rw [hm1] at h2
  simp only [show (1:ℕ) + 1 = 2 from rfl] at h2 ⊢
  rw [h0, h2]
  have hyT := hm 1 (by omega)
  rw [pieceHold_split P hR hS.1.le hsT hyT heT]
  rw [cS_lead P hR C h 0 (by omega)]
  simp only [zero_add]
  rw [int_gl P hR _ hsT hyT, sum_fin2_lo C.lead]
  have hr := root_ratio P hR K C.lead hsT heT
    ⟨by rw [← h0]; exact (h6 0 (by omega)).le, by rw [← h2]; exact (h6 1 (by omega)).le⟩ hE
  unfold Eq8 at hE
  have hDl := D_add P hR C.lead hsT hyT heT
  have hDf := D_lower P (other C.lead) hR hyT heT (by rw [← h2]; exact (h6 1 (by omega)).le)
    (K.hd _)
  have hDf0 := D_nonneg P hS (other C.lead) hyT heT (by rw [← h2]; exact (h6 1 (by omega)).le)
  have hcoef : 0 ≤ P.a C.lead (other C.lead) / P.a (other C.lead) (other C.lead) := by
    have := hS.2.2.2.1; exact (div_pos (this _ _) (this _ _)).le
  set y := C.τ 1
  have hys : 0 ≤ y - C.start := by
    have := (h6 0 (by omega)).le; rw [h0] at this; simp only [y]; linarith
  have hl := (hS.2.2.1 C.lead).le
  have hf := hmin_le P (other C.lead)
  have hθ0 := K.θ_pos
  have hm0 := K.m0_pos
  have hmp := hmin_pos P hS
  -- key identity
  have key : P.h C.lead * ((y - C.start) *
      (P.a C.lead C.lead / P.a (other C.lead) C.lead * D P (other C.lead) C.start y -
        D P C.lead C.start y)) =
      (y - C.start) * (P.h C.lead * D P C.lead y C.stop) -
      (y - C.start) * P.h C.lead *
        (P.a C.lead (other C.lead) / P.a (other C.lead) (other C.lead) *
          D P (other C.lead) y C.stop) := by
    have : P.a C.lead C.lead / P.a (other C.lead) C.lead * D P (other C.lead) C.start y -
        D P C.lead C.start y = D P C.lead y C.stop -
        P.a C.lead (other C.lead) / P.a (other C.lead) (other C.lead) *
          D P (other C.lead) y C.stop := by linarith
    rw [this]; ring
  rw [key]
  have t1 : 0 ≤ (y - C.start) * P.h C.lead *
      (P.a C.lead (other C.lead) / P.a (other C.lead) (other C.lead) *
        D P (other C.lead) y C.stop) := by positivity
  have t2 : hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 ≤
      (y - C.start) * (P.h (other C.lead) * D P (other C.lead) y C.stop) := by
    have a1 : K.θ * (C.stop - C.start) * (K.θ * (C.stop - C.start)) ≤
        (y - C.start) * (C.stop - y) := by
      have hes' : 0 ≤ C.stop - C.start := by
        have := (h6 1 (by omega)).le; rw [h2] at this; simp only [y] at hys; linarith
      exact mul_le_mul hr.1 hr.2 (mul_nonneg hθ0.le hes') hys
    have a2 : hmin P * K.m0 * (C.stop - y) ≤ P.h (other C.lead) * D P (other C.lead) y C.stop := by
      have : 0 ≤ C.stop - y := by
        have := (h6 1 (by omega)).le; rw [h2] at this; simp only [y]; linarith
      calc hmin P * K.m0 * (C.stop - y) = hmin P * (K.m0 * (C.stop - y)) := by ring
        _ ≤ P.h (other C.lead) * D P (other C.lead) y C.stop :=
          mul_le_mul hf hDf (by positivity) (hS.2.2.1 _).le
    have a3 : hmin P * K.m0 * ((y - C.start) * (C.stop - y)) ≤
        (y - C.start) * (P.h (other C.lead) * D P (other C.lead) y C.stop) := by
      have := mul_le_mul_of_nonneg_left a2 hys
      linarith
    have a4 : hmin P * K.m0 * (K.θ * (C.stop - C.start) * (K.θ * (C.stop - C.start))) ≤
        hmin P * K.m0 * ((y - C.start) * (C.stop - y)) :=
      mul_le_mul_of_nonneg_left a1 (by positivity)
    nlinarith
  nlinarith

/-! ## Part 10: chains of cycles -/

def Chain : List SeqCycle → ℝ → ℝ → Prop
  | [], a, b => a = b
  | C :: cs, a, b => C.start = a ∧ Chain cs C.stop b

lemma chain_of_valid_aux : ∀ (cs : List SeqCycle) (a b : ℝ), cs ≠ [] →
    cs.head?.map SeqCycle.start = some a → cs.getLast?.map SeqCycle.stop = some b →
    (∀ p ∈ cs.zip cs.tail, p.1.stop = p.2.start) → Chain cs a b := by
  intro cs
  induction cs with
  | nil => intro a b h; exact absurd rfl h
  | cons C cs ih =>
    intro a b _ hh hl hz
    simp at hh
    refine ⟨hh, ?_⟩
    cases cs with
    | nil => simp at hl; exact hl
    | cons C2 cs2 =>
      have hz1 : C.stop = C2.start := hz (C, C2) (by simp)
      apply ih C.stop b (by simp) (by simp [hz1])
      · simpa using hl
      · intro p hp
        apply hz p
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp ⊢
        right; exact hp

lemma chain_of_valid (P : Params) (S : SeqPolicy) (h : S.Valid P) : Chain S.cycles 0 P.T :=
  chain_of_valid_aux S.cycles 0 P.T h.1 h.2.1 h.2.2.1 h.2.2.2.2

lemma valid_of_chain_aux : ∀ (cs : List SeqCycle) (a b : ℝ), Chain cs a b → cs ≠ [] →
    cs.head?.map SeqCycle.start = some a ∧ cs.getLast?.map SeqCycle.stop = some b ∧
    (∀ p ∈ cs.zip cs.tail, p.1.stop = p.2.start) := by
  intro cs
  induction cs with
  | nil => intro a b _ h; exact absurd rfl h
  | cons C cs ih =>
    intro a b hc _
    obtain ⟨h1, h2⟩ := hc
    refine ⟨by simp [h1], ?_⟩
    cases cs with
    | nil =>
      simp [Chain] at h2
      simp [h2]
    | cons C2 cs2 =>
      obtain ⟨i1, i2, i3⟩ := ih C.stop b h2 (by simp)
      refine ⟨by simpa using i2, ?_⟩
      intro p hp
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with hp | hp
      · subst hp; simp at i1; simp [i1]
      · exact i3 p (by simpa using hp)

lemma cP_add (P : Params) (hR : P.Regular) {x y z : ℝ}
    (hx : x ∈ Icc 0 P.T) (hy : y ∈ Icc 0 P.T) (hz : z ∈ Icc 0 P.T) :
    commonPurchase P x y + commonPurchase P y z = commonPurchase P x z := by
  unfold commonPurchase
  rw [← D_add P hR 0 hx hy hz, ← D_add P hR 1 hx hy hz]
  ring

lemma chain_sum (P : Params) (hR : P.Regular) : ∀ (cs : List SeqCycle) (a b : ℝ),
    Chain cs a b → (∀ C ∈ cs, SeqStruct P C) → a ∈ Icc 0 P.T → b ∈ Icc 0 P.T →
    (cs.map (fun C => commonPurchase P C.start C.stop)).sum = commonPurchase P a b ∧
    (cs.map (fun C => C.stop - C.start)).sum = b - a := by
  intro cs
  induction cs with
  | nil =>
    intro a b hc _ _ _
    simp [Chain] at hc; subst hc
    simp [commonPurchase, D]
  | cons C cs ih =>
    intro a b hc hst ha hb
    obtain ⟨h1, h2⟩ := hc
    have hC := hst C (by simp)
    have hsT := hC.2.2.2.1 ▸ hC.mem 0 (by omega)
    have heT := hC.2.2.2.2.1 ▸ hC.mem (C.m + 1) le_rfl
    obtain ⟨i1, i2⟩ := ih C.stop b h2 (fun D hD => hst D (by simp [hD])) heT hb
    simp only [List.map_cons, List.sum_cons, i1, i2]
    rw [h1] at hsT ⊢
    constructor
    · exact cP_add P hR hsT heT hb
    · ring

lemma list_cs : ∀ (xs : List ℝ), xs.sum ^ 2 ≤ xs.length * (xs.map (· ^ 2)).sum := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.sum_cons, List.length_cons, List.map_cons]
    push_cast
    set S := xs.sum
    set Q := (xs.map (· ^ 2)).sum
    set n : ℝ := (xs.length : ℝ)
    have hQ : 0 ≤ Q := by
      apply List.sum_nonneg; intro y hy; simp at hy; obtain ⟨z, _, rfl⟩ := hy; positivity
    have hn : 0 ≤ n := by positivity
    rcases eq_or_lt_of_le hn with hn0 | hnp
    · rw [← hn0] at ih
      have : S = 0 := by nlinarith
      rw [this, ← hn0]; nlinarith
    · have h1 : 0 ≤ n * (Q + n * x ^ 2 - 2 * x * S) := by nlinarith [sq_nonneg (S - n * x)]
      have h2 : 0 ≤ Q + n * x ^ 2 - 2 * x * S := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith

lemma list_len_le (cs : List SeqCycle) :
    (cs.length : ℝ) ≤ (cs.map (fun C => (C.m : ℝ) + 1)).sum := by
  induction cs with
  | nil => simp
  | cons C cs ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    push_cast
    have : (0:ℝ) ≤ C.m := by positivity
    linarith

/-! ## Part 11: concatenation of a chain into a partition -/

lemma concat (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (K : Consts P) : ∀ (cs : List SeqCycle) (a b : ℝ), Chain cs a b →
    (∀ C ∈ cs, SeqStruct P C) →
    ∃ (N : ℕ) (τ : ℕ → ℝ), τ 0 = a ∧ τ N = b ∧ (∀ k < N, τ k < τ (k + 1)) ∧
      (N : ℝ) = (cs.map (fun C => (C.m : ℝ) + 1)).sum ∧
      ∑ k ∈ Finset.range N, pieceHold P (τ k) (τ (k + 1)) +
        hmin P * K.m0 * K.θ ^ 2 / 2 * (cs.map (fun C => (C.stop - C.start) ^ 2)).sum ≤
        (cs.map (fun C => holding P (C.plan P) C.start C.stop)).sum := by
  intro cs
  induction cs with
  | nil =>
    intro a b hc _
    simp [Chain] at hc
    exact ⟨0, fun _ => a, rfl, hc, fun k hk => absurd hk (Nat.not_lt_zero _), by simp, by simp⟩
  | cons C cs ih =>
    intro a b hc hst
    obtain ⟨h1, h2⟩ := hc
    have hC := hst C (by simp)
    obtain ⟨N', τ', t0, tN, tinc, tsum, tgap⟩ := ih C.stop b h2 (fun D hD => hst D (by simp [hD]))
    let τ : ℕ → ℝ := fun n => if n < C.m + 1 then C.τ n else τ' (n - (C.m + 1))
    have hτ1 : ∀ k < C.m + 1, τ k = C.τ k := fun k hk => by simp only [τ]; rw [if_pos hk]
    have hτ2 : ∀ k, τ (C.m + 1 + k) = τ' k := fun k => by
      simp only [τ]; rw [if_neg (by omega)]; congr 1; omega
    have hτm : τ (C.m + 1) = C.τ (C.m + 1) := by
      have := hτ2 0; simp only [add_zero] at this; rw [this, t0, hC.2.2.2.2.1]
    have hτ3 : ∀ k ≤ C.m + 1, τ k = C.τ k := by
      intro k hk
      rcases lt_or_eq_of_le hk with hk | hk
      · exact hτ1 k hk
      · subst hk; exact hτm
    refine ⟨C.m + 1 + N', τ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hτ1 0 (by omega), hC.2.2.2.1, h1]
    · rw [hτ2, tN]
    · intro k hk
      by_cases hk2 : k < C.m + 1
      · rw [hτ3 k hk2.le, hτ3 (k+1) hk2]; exact hC.2.2.2.2.2.1 k hk2
      · obtain ⟨j, rfl⟩ : ∃ j, k = C.m + 1 + j := ⟨k - (C.m + 1), by omega⟩
        rw [hτ2, show C.m + 1 + j + 1 = C.m + 1 + (j + 1) by omega, hτ2]
        exact tinc j (by omega)
    · simp only [List.map_cons, List.sum_cons]
      rw [← tsum]; push_cast; ring
    · rw [Finset.sum_range_add]
      have e1 : ∑ k ∈ Finset.range (C.m + 1), pieceHold P (τ k) (τ (k + 1)) =
          ∑ k ∈ Finset.range (C.m + 1), pieceHold P (C.τ k) (C.τ (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k hk; rw [Finset.mem_range] at hk
        rw [hτ3 k hk.le, hτ3 (k+1) hk]
      have e2 : ∑ k ∈ Finset.range N', pieceHold P (τ (C.m + 1 + k)) (τ (C.m + 1 + k + 1)) =
          ∑ k ∈ Finset.range N', pieceHold P (τ' k) (τ' (k + 1)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hτ2, show C.m + 1 + k + 1 = C.m + 1 + (k + 1) by omega, hτ2]
      rw [e1, e2]
      have g := seq_gap1 P hS hR hG K C hC
      simp only [List.map_cons, List.sum_cons]
      have : hmin P * K.m0 * K.θ ^ 2 / 2 * ((C.stop - C.start) ^ 2 +
          (cs.map (fun C => (C.stop - C.start) ^ 2)).sum) =
          hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 / 2 +
          hmin P * K.m0 * K.θ ^ 2 / 2 * (cs.map (fun C => (C.stop - C.start) ^ 2)).sum := by
        ring
      rw [this]
      linarith

/-! ## Part 12: sequential policy costs -/

noncomputable def seqSet (P : Params) : Set ℝ :=
  {x : ℝ | ∃ S : SeqPolicy, S.Valid P ∧ x = S.cost P}

lemma seq_policy_cost (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (S : SeqPolicy) (hV : S.Valid P) :
    S.cost P = P.A * (S.cycles.map (fun C => (C.m : ℝ) + 1)).sum + commonPurchase P 0 P.T +
      (S.cycles.map (fun C => holding P (C.plan P) C.start C.stop)).sum := by
  have hst : ∀ C ∈ S.cycles, SeqStruct P C := fun C hC => SeqStruct.of_valid (hV.2.2.2.1 C hC)
  have hT := hS.1.le
  have := (chain_sum P hR S.cycles 0 P.T (chain_of_valid P S hV) hst ⟨le_refl _, hT⟩
    ⟨hT, le_refl _⟩).1
  rw [← this]
  unfold SeqPolicy.cost
  have : ∀ cs : List SeqCycle, (∀ C ∈ cs, SeqStruct P C) →
      (cs.map (SeqCycle.cost P)).sum = P.A * (cs.map (fun C => (C.m : ℝ) + 1)).sum +
        (cs.map (fun C => commonPurchase P C.start C.stop)).sum +
        (cs.map (fun C => holding P (C.plan P) C.start C.stop)).sum := by
    intro cs
    induction cs with
    | nil => simp
    | cons C cs ih =>
      intro h
      simp only [List.map_cons, List.sum_cons]
      rw [ih (fun D hD => h D (by simp [hD])), seq_cost_eq P hS hR hG C (h C (by simp))]
      ring
  exact this S.cycles hst

lemma seq_hold_nonneg (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (C : SeqCycle) (h : SeqStruct P C) : 0 ≤ holding P (C.plan P) C.start C.stop := by
  have K := (consts_exist P hS hR hG).some
  have g := seq_gap1 P hS hR hG K C h
  have hm := h.mem
  have : 0 ≤ ∑ k ∈ Finset.range (C.m + 1), pieceHold P (C.τ k) (C.τ (k + 1)) := by
    apply Finset.sum_nonneg; intro k hk; rw [Finset.mem_range] at hk
    exact pieceHold_nonneg P hS (hm k hk.le) (hm (k+1) hk) (h.2.2.2.2.2.1 k hk).le
  have : 0 ≤ hmin P * K.m0 * K.θ ^ 2 * (C.stop - C.start) ^ 2 / 2 := by
    have := hmin_pos P hS; have := K.m0_pos; have := K.θ_pos; positivity
  linarith

lemma seq_cost_ge (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    (S : SeqPolicy) (hV : S.Valid P) :
    P.A * (S.cycles.map (fun C => (C.m : ℝ) + 1)).sum + commonPurchase P 0 P.T ≤ S.cost P := by
  rw [seq_policy_cost P hS hR hG S hV]
  have : 0 ≤ (S.cycles.map (fun C => holding P (C.plan P) C.start C.stop)).sum := by
    apply List.sum_nonneg
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨C, hC, rfl⟩ := hx
    exact seq_hold_nonneg P hS hR hG C (SeqStruct.of_valid (hV.2.2.2.1 C hC))
  linarith

lemma seqSet_bdd (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard) :
    BddBelow (seqSet P) := by
  refine ⟨commonPurchase P 0 P.T, ?_⟩
  rintro x ⟨S, hS', rfl⟩
  have h := seq_cost_ge P hS hR hG S hS'
  have : 0 ≤ P.A * (S.cycles.map (fun C => (C.m : ℝ) + 1)).sum := by
    apply mul_nonneg hS.2.1.le
    apply List.sum_nonneg; intro x hx; simp at hx; obtain ⟨C, _, rfl⟩ := hx; positivity
  linarith

/-- a one-split sequential cycle on `[s, e]` with lead cluster `0` and split point `y` -/
def cyc1 (s y e : ℝ) : SeqCycle :=
  ⟨s, e, 0, 1, fun n => if n = 0 then s else if n = 1 then y else e⟩

lemma cyc1_struct (P : Params) (hS : P.Standing) {s y e : ℝ} (hs : 0 ≤ s) (he : e ≤ P.T)
    (hy : y ∈ Ioo s e) (h8 : Eq8 P 0 s y e) : SeqStruct P (cyc1 s y e) := by
  refine ⟨hs, he, le_refl _, rfl, rfl, ?_, ?_⟩
  · intro k hk
    simp only [cyc1] at hk ⊢
    interval_cases k
    · simp; exact hy.1
    · simp; exact hy.2
  · unfold Eq8 at h8
    simp [cyc1, SeqCycle.leadQ, SeqCycle.followQ, SeqCycle.follow, other] at h8 ⊢
    rw [← h8]; ring

lemma cyc1_exists (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard)
    {s e : ℝ} (hs : 0 ≤ s) (hse : s < e) (he : e ≤ P.T) :
    ∃ y, y ∈ Ioo s e ∧ SeqStruct P (cyc1 s y e) := by
  obtain ⟨y, hy, h8⟩ := root_exists P hS hR hG 0 ⟨hs, by linarith⟩ ⟨by linarith, he⟩ hse
  exact ⟨y, hy, cyc1_struct P hS hs he hy h8⟩

lemma seqSet_ne (P : Params) (hS : P.Standing) (hR : P.Regular) (hG : P.RatioGuard) :
    (seqSet P).Nonempty := by
  obtain ⟨y, _, hy⟩ := cyc1_exists P hS hR hG (le_refl 0) hS.1 (le_refl _)
  refine ⟨_, ⟨⟨[cyc1 0 y P.T]⟩, ?_, rfl⟩⟩
  refine ⟨by simp, by simp [cyc1], by simp [cyc1], ?_, by simp⟩
  intro C hC
  have : C = cyc1 0 y P.T := by simpa using hC
  rw [this]
  exact seq_valid P hS hR hG _ hy

/-! ## Part 13: the `β = 1` endpoint -/

lemma optSeq_def (P : Params) : optSeq P = sInf (seqSet P) := rfl

lemma seq_N_ge_one (S : SeqPolicy) (h : S.cycles ≠ []) :
    (1 : ℝ) ≤ (S.cycles.map (fun C => (C.m : ℝ) + 1)).sum := by
  have := list_len_le S.cycles
  have h2 : 1 ≤ S.cycles.length := List.length_pos_iff.mpr h
  have : (1:ℝ) ≤ S.cycles.length := by exact_mod_cast h2
  linarith

theorem beta_one_proof (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    optSim P 1 < optSeq P := by
  obtain ⟨K⟩ := consts_exist P hS hR hG
  have hT := hS.1
  have hA := hS.2.1
  set cP := commonPurchase P 0 P.T with hcP
  set c1 := hmin P * K.m0 * K.θ ^ 2 / 2 with hc1
  have hc1p : 0 < c1 := by
    have := hmin_pos P hS; have := K.m0_pos; have := K.θ_pos; positivity
  have hlow : cP + P.A ≤ optSeq P := by
    apply le_csInf (seqSet_ne P hS hR hG)
    rintro x ⟨S, hV, rfl⟩
    have h1 := seq_cost_ge P hS hR hG S hV
    have h2 := seq_N_ge_one S hV.1
    nlinarith
  set B := optSeq P + 1 with hB
  set Nmax := (B - cP) / P.A with hNmax
  have hNmax_pos : 0 < Nmax := by rw [hNmax]; apply div_pos _ hA; linarith
  set g := c1 * P.T ^ 2 / Nmax with hg
  have hgp : 0 < g := by positivity
  have claim : ∀ x ∈ seqSet P, min B (optSim P 1 + g) ≤ x := by
    rintro x ⟨S, hV, rfl⟩
    have hst : ∀ C ∈ S.cycles, SeqStruct P C := fun C hC => SeqStruct.of_valid (hV.2.2.2.1 C hC)
    have hch := chain_of_valid P S hV
    obtain ⟨N, τ, t0, tN, tinc, tsum, tgap⟩ := concat P hS hR hG K S.cycles 0 P.T hch hst
    have hN1 : (1:ℝ) ≤ N := by rw [tsum]; exact seq_N_ge_one S hV.1
    have hN1' : 1 ≤ N := by exact_mod_cast hN1
    have hsim : SimStruct P ⟨0, P.T, N, τ⟩ := ⟨le_refl _, le_refl _, hN1', t0, tN, tinc⟩
    have hpol : (⟨0, P.T, N, τ⟩ : SimCycle).IsPolicy P :=
      ⟨sim_valid P hS hR hG _ hsim, rfl, rfl⟩
    have h1 := optSim_le P hS hR hG 1 zero_le_one _ hpol
    rw [sim_cost_eq P hS hR hG _ hsim] at h1
    simp only at h1
    have hcost := seq_policy_cost P hS hR hG S hV
    have hbase : optSim P 1 + c1 * (S.cycles.map (fun C => (C.stop - C.start) ^ 2)).sum ≤
        S.cost P := by
      rw [hcost, ← tsum]
      rw [← hc1] at tgap
      rw [← hcP] at h1
      linarith
    by_cases hc : S.cost P ≤ B
    · apply le_trans (min_le_right _ _)
      have hge := seq_cost_ge P hS hR hG S hV
      rw [← tsum] at hge
      have hNle : (N : ℝ) ≤ Nmax := by
        rw [hNmax, le_div_iff₀ hA]; linarith
      have hr : (S.cycles.length : ℝ) ≤ Nmax := by
        have := list_len_le S.cycles; rw [← tsum] at this; linarith
      have hr1 : (1:ℝ) ≤ S.cycles.length := by
        exact_mod_cast List.length_pos_iff.mpr hV.1
      have hL := (chain_sum P hR S.cycles 0 P.T hch hst ⟨le_refl _, hT.le⟩
        ⟨hT.le, le_refl _⟩).2
      have hcs := list_cs (S.cycles.map (fun C => C.stop - C.start))
      rw [hL, List.length_map, List.map_map] at hcs
      have e : ((fun x : ℝ => x ^ 2) ∘ fun C : SeqCycle => C.stop - C.start) =
          (fun C => (C.stop - C.start) ^ 2) := rfl
      rw [e] at hcs
      set Q := (S.cycles.map (fun C => (C.stop - C.start) ^ 2)).sum
      have hQ : P.T ^ 2 / Nmax ≤ Q := by
        rw [div_le_iff₀ hNmax_pos]
        have : 0 ≤ Q := by
          apply List.sum_nonneg; intro y hy; simp at hy; obtain ⟨z, _, rfl⟩ := hy; positivity
        nlinarith
      have : g ≤ c1 * Q := by
        rw [hg, mul_div_assoc]; exact mul_le_mul_of_nonneg_left hQ hc1p.le
      linarith
    · push Not at hc
      exact le_trans (min_le_left _ _) hc.le
  have hm : min B (optSim P 1 + g) ≤ optSeq P := le_csInf (seqSet_ne P hS hR hG) claim
  have : min B (optSim P 1 + g) = optSim P 1 + g := by
    rcases min_choice B (optSim P 1 + g) with h | h
    · rw [h] at hm; linarith
    · exact h
  rw [this] at hm
  linarith

end BundledExpansion.SeqSim

open BundledExpansion.SeqSim in
theorem solution (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    optSim P 1 < optSeq P :=
  beta_one_proof P hS hR hG
