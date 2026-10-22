-- Prove2me | solution 1 for BundledExpansion.SeqSim.beta_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T10:11:34.507785+00:00
-- url     : https://prove2.me/submissions/07977ec2-618f-4c05-89f2-6cce3496b61b

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

end BundledExpansion.SeqSim

open BundledExpansion.SeqSim in
theorem solution (P : Params) (hS : P.Standing)
    (hR : P.Regular) (hG : P.RatioGuard) :
    StrictMonoOn (optSim P) (Set.Icc (1 : ℝ) 2) :=
  beta_monotone_proof P hS hR hG
