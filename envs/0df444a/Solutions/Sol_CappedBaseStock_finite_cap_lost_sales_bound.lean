-- Prove2me | solution 1 for CappedBaseStock.finite_cap_lost_sales_bound
-- status  : ACCEPTED   (prove)
-- author  : @StellaXin
-- created : 2026-09-08T02:42:16.064206+00:00
-- url     : https://prove2.me/submissions/4d90111e-2bf8-4c2b-b771-c8956c3517d7

import Definitions.Def_CappedBaseStock_Model

/-! Direct proof of the finite-cap lost-sales moment bound.
Every finite-horizon, demand-law, integrability, and limiting argument needed
by the solution is proved here, starting from the actual empty initial state. -/


noncomputable section
open scoped NNReal ENNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

def position {L : ℕ} (s : State L) : ℝ≥0 := s.1 + ∑ i : Fin L, s.2 i

lemma shift_sum (n : ℕ) (f : Fin (n+1) → ℝ≥0) (q : ℝ≥0) :
    (∑ i : Fin (n+1), if hi : i.val + 1 < n+1 then f ⟨i.val+1, hi⟩ else q)
      + f 0 = (∑ i : Fin (n+1), f i) + q := by
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  simp [Fin.succ, add_comm, add_left_comm, add_assoc]

lemma pipelineSum_step (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    (∑ i : Fin c.L, (step c s q d).2 i) + arrival c s =
      (∑ i : Fin c.L, s.2 i) + q := by
  rcases c with ⟨L, hL, h, p, hh, hp⟩
  cases L with
  | zero => omega
  | succ n => simpa [step, arrival] using shift_sum n s.2 q

lemma position_step (c : Parameters) (s : State c.L) (q d : ℝ≥0) :
    position (step c s q d) + filledDemand c s d = position s + q := by
  have hs := pipelineSum_step c s q d
  have hfilled : s.1 + arrival c s - d + min d (s.1 + arrival c s) =
      s.1 + arrival c s := by
    simpa [min_comm] using (tsub_add_min (a := s.1 + arrival c s) (b := d))
  simp only [position, step, filledDemand]
  simpa only [step] using (by linear_combination hs + hfilled :
    s.1 + arrival c s - d +
      (∑ i : Fin c.L, (step c s q d).2 i) + min d (s.1 + arrival c s) =
    s.1 + (∑ i : Fin c.L, s.2 i) + q)

lemma cbsOrder_le_cap (L : ℕ) (S r : ℝ≥0) (s : State L) :
    cbsOrder L S r s ≤ r := min_le_right _ _

lemma position_add_order_le (L : ℕ) (S r : ℝ≥0) (s : State L)
    (hs : position s ≤ S) : position s + cbsOrder L S r s ≤ S := by
  calc
    position s + cbsOrder L S r s ≤ position s + (S - position s) := by
      exact add_le_add le_rfl (min_le_left (S - position s) r)
    _ = S := add_tsub_cancel_of_le hs

lemma cbsRun_position_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    position (cbsRun c S r ω t) ≤ S := by
  induction t with
  | zero => simp [cbsRun, initialState, position]
  | succ t ih =>
      have hp := position_step c (cbsRun c S r ω t)
        (cbsOrder c.L S r (cbsRun c S r ω t)) (ω.1 t)
      have hb := position_add_order_le c.L S r (cbsRun c S r ω t) ih
      rw [← hp] at hb
      exact (le_add_right le_rfl).trans hb

lemma cbsRun_slot (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ)
    (i : Fin c.L) :
    (cbsRun c S r ω t).2 i = if t + i.val < c.L then 0 else
      cbsOrder c.L S r (cbsRun c S r ω (t + i.val - c.L)) := by
  induction t generalizing i with
  | zero => simp [cbsRun, initialState, i.isLt]
  | succ t ih =>
      simp only [cbsRun, step]
      split_ifs with hi ht
      · rw [ih]
        split_ifs <;> simp_all <;> omega
      · rw [ih]
        split_ifs <;> simp_all
        · omega
        · congr 3 <;> omega
      · omega
      · have hi' : i.val + 1 = c.L := by omega
        congr 3
        omega

lemma cbsRun_arrival (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    arrival c (cbsRun c S r ω t) = if t < c.L then 0 else
      cbsOrder c.L S r (cbsRun c S r ω (t - c.L)) := by
  simpa [arrival] using cbsRun_slot c S r ω t
    ⟨0, lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos⟩

lemma cbsRun_pipeline_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ)
    (i : Fin c.L) : (cbsRun c S r ω t).2 i ≤ r := by
  rw [cbsRun_slot]
  split_ifs
  · exact zero_le
  · exact cbsOrder_le_cap _ _ _ _

lemma cbsRun_arrival_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    arrival c (cbsRun c S r ω t) ≤ r := by
  exact cbsRun_pipeline_le _ _ _ _ _ _

lemma cbsRun_inventory_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsRun c S r ω t).1 ≤ S := by
  exact (le_add_right le_rfl).trans (cbsRun_position_le c S r ω t)

lemma cbsRun_future_arrival (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) (i : Fin c.L) :
    arrival c (cbsRun c S r ω (t + i.val)) = (cbsRun c S r ω t).2 i := by
  rw [cbsRun_arrival, cbsRun_slot]

lemma cbsRun_arrival_after_leadTime (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) : arrival c (cbsRun c S r ω (t + c.L)) =
      cbsOrder c.L S r (cbsRun c S r ω t) := by
  rw [cbsRun_arrival]
  simp

lemma cbsRun_block_resources (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    (cbsRun c S r ω t).1 +
      (∑ j ∈ Finset.range (c.L + 1), arrival c (cbsRun c S r ω (t+j))) ≤ S := by
  rw [Finset.sum_range_succ, cbsRun_arrival_after_leadTime]
  have hsum : (∑ j ∈ Finset.range c.L, arrival c (cbsRun c S r ω (t+j))) =
      ∑ i : Fin c.L, (cbsRun c S r ω t).2 i := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => cbsRun_future_arrival c S r ω t i)
  rw [hsum, ← add_assoc]
  exact position_add_order_le _ _ _ _ (cbsRun_position_le c S r ω t)

lemma cbsRun_slot_sum (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (N : ℕ) (i : Fin c.L) :
    (∑ t ∈ Finset.range N, (cbsRun c S r ω t).2 i) =
      ∑ t ∈ Finset.range (N + i.val - c.L),
        cbsOrder c.L S r (cbsRun c S r ω t) := by
  induction N with
  | zero => simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt i.isLt)]
  | succ N ih =>
      rw [Finset.sum_range_succ, cbsRun_slot, ih]
      by_cases h : N + i.val < c.L
      · have hN : N + i.val - c.L = 0 := by omega
        have hN' : N + 1 + i.val - c.L = 0 := by omega
        simp [h, hN, hN']
      · rw [if_neg h, show N + 1 + i.val - c.L = (N + i.val - c.L) + 1 by omega,
          Finset.sum_range_succ]

lemma cbsRun_pipeline_sum_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (N : ℕ) :
    (∑ t ∈ Finset.range N, ∑ i : Fin c.L, (cbsRun c S r ω t).2 i) ≤
      (c.L : ℝ≥0) * ∑ t ∈ Finset.range N, cbsOrder c.L S r (cbsRun c S r ω t) := by
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin c.L, ∑ t ∈ Finset.range N, (cbsRun c S r ω t).2 i) ≤
        ∑ _i : Fin c.L, ∑ t ∈ Finset.range N,
          cbsOrder c.L S r (cbsRun c S r ω t) := by
      apply Finset.sum_le_sum
      intro i _
      rw [cbsRun_slot_sum]
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ = _ := by simp

lemma cbsRun_inventory_zero_initial (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) (ht : t ≤ c.L) : (cbsRun c S r ω t).1 = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hi := ih (by omega)
      have ha : arrival c (cbsRun c S r ω t) = 0 := by
        rw [cbsRun_arrival, if_pos (by omega)]
      simp only [cbsRun, step, hi, ha, zero_add, zero_tsub]

end CappedBaseStockBounds


open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace CappedBaseStockBounds
open CappedBaseStock

def reversePrefixIndex (t i : ℕ) : ℕ := if i ≤ t then t - i else i

lemma reversePrefixIndex_injective (t : ℕ) : Function.Injective (reversePrefixIndex t) := by
  intro i j h
  unfold reversePrefixIndex at h
  split_ifs at h <;> omega

lemma measurePreserving_reindex (P : DemandLaw) (f : ℕ → ℕ) (hf : Function.Injective f) :
    MeasurePreserving (fun d : DemandPath => fun i => d (f i))
      (demandPathLaw P) (demandPathLaw P) := by
  constructor
  · fun_prop
  · exact Measure.map_infinitePi_infinitePi_of_inj hf

lemma measurePreserving_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) :
    MeasurePreserving (fun ω : Sample => fun i => ω.1 (f i))
      (sampleLaw P) (demandPathLaw P) := by
  exact (measurePreserving_reindex P f hf).comp measurePreserving_fst

lemma lintegral_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, F (fun i => ω.1 (f i)) ∂sampleLaw P) =
      ∫⁻ d, F d ∂demandPathLaw P := by
  exact (measurePreserving_sample_reindex P f hf).lintegral_comp hF

lemma integral_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ) (hF : Measurable F) :
    (∫ ω, F (fun i => ω.1 (f i)) ∂sampleLaw P) =
      ∫ d, F d ∂demandPathLaw P := by
  have hm := measurePreserving_sample_reindex P f hf
  rw [← integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable, hm.map_eq]

lemma integrable_sample_reindex (P : DemandLaw) (f : ℕ → ℕ)
    (hf : Function.Injective f) (F : DemandPath → ℝ)
    (hF : Integrable F (demandPathLaw P)) :
    Integrable (fun ω => F (fun i => ω.1 (f i))) (sampleLaw P) := by
  exact (measurePreserving_sample_reindex P f hf).integrable_comp_of_integrable hF

end CappedBaseStockBounds


noncomputable section
open scoped BigOperators NNReal ENNReal
open CappedBaseStock
namespace CappedBaseStockBounds

/-- A finite Lindley recursion is bounded by any common upper bound on its
initial-load term and all the nonempty-cut suffix sums. -/
lemma lindley_terminal_bound (u a : ℕ → ℝ) (n : ℕ) (B : ℝ)
    (hstep : ∀ t < n, u (t + 1) ≤ max (u t + a t) 0)
    (hinit : u 0 + ∑ i ∈ Finset.range n, a i ≤ B)
    (htail : ∀ k, 1 ≤ k → k ≤ n → ∑ i ∈ Finset.Ico k n, a i ≤ B) :
    u n ≤ B := by
  have haux : ∀ t, t ≤ n →
      u t ≤ B - (∑ i ∈ Finset.range n, a i) + ∑ i ∈ Finset.range t, a i := by
    intro t
    induction t with
    | zero =>
        intro _
        simp only [Finset.range_zero, Finset.sum_empty]
        linarith
    | succ t ih =>
        intro ht
        have ht0 : t < n := by omega
        have hi := ih (by omega)
        have hs := htail (t + 1) (by omega) ht
        rw [Finset.sum_Ico_eq_sub _ ht] at hs
        apply (hstep t ht0).trans
        apply max_le
        · rw [Finset.sum_range_succ]
          linarith
        · linarith
  have h := haux n le_rfl
  linarith

/-- The certificate random variable is an upper envelope for every suffix of
the corresponding chronological demand block. -/
lemma demand_suffix_le_certificate_envelope (d : DemandPath) (r : ℝ)
    (n k : ℕ) (hk : k ≤ n) :
    (∑ i ∈ Finset.Ico k n, ((d i : ℝ) - r)) ≤
      finiteInventory d r n + ∑ i ∈ Finset.range n, ((d i : ℝ) - r) := by
  have hm : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have hi := Finset.le_sup' (fun j => ∑ i ∈ Finset.range j, (r - (d i : ℝ))) hm
  change (∑ i ∈ Finset.range k, (r - (d i : ℝ))) ≤ finiteInventory d r n at hi
  rw [Finset.sum_Ico_eq_sub _ hk]
  have hn : (∑ i ∈ Finset.range k, (r - (d i : ℝ))) =
      -(∑ i ∈ Finset.range k, ((d i : ℝ) - r)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hn] at hi
  linarith

/-- Recursion over `L+1` periods: the starting term is bounded by `z`, while
all other terms fit the chronological final `L`-demand certificate envelope. -/
lemma shortfall_window_bound (u a : ℕ → ℝ) (d : DemandPath)
    (L : ℕ) (r z : ℝ)
    (hstep : ∀ t < L + 1, u (t + 1) ≤ max (u t + a t - r) 0)
    (hblock : u 0 + ∑ i ∈ Finset.range (L + 1), (a i - r) ≤ z)
    (hdom : ∀ i < L, a (i + 1) ≤ (d i : ℝ)) :
    u (L + 1) ≤ max z
      (finiteInventory d r L + ∑ i ∈ Finset.range L, ((d i : ℝ) - r)) := by
  apply lindley_terminal_bound u (fun t => a t - r) (L + 1)
  · intro t ht
    simpa only [sub_eq_add_neg, add_assoc] using hstep t ht
  · exact hblock.trans (le_max_left _ _)
  · intro k hk hkn
    have ht : (∑ i ∈ Finset.Ico k (L + 1), (a i - r)) ≤
        ∑ i ∈ Finset.Ico (k - 1) L, ((d i : ℝ) - r) := by
      have hk' : k - 1 + 1 = k := by omega
      have hr : (∑ i ∈ Finset.Ico (k - 1) L, (a (i + 1) - r)) =
          ∑ i ∈ Finset.Ico k (L + 1), (a i - r) := by
        simpa only [hk', Nat.add_comm] using
          (Finset.sum_Ico_add (fun i => a i - r) (k - 1) L 1)
      rw [← hr]
      apply Finset.sum_le_sum
      intro i hi
      exact sub_le_sub_right (hdom i (Finset.mem_Ico.mp hi).2) r
    exact ht.trans ((demand_suffix_le_certificate_envelope d r L (k - 1)
      (by omega)).trans (le_max_right _ _))

/-- Finite-horizon material balance. The terminal inventory position is the
only boundary term when loss is measured against the nominal order rate. -/
lemma cumulative_loss_identity (M q A D : ℕ → ℝ) (r : ℝ) (N : ℕ)
    (hflow : ∀ t < N, M (t + 1) = M t + q t - A t) :
    (∑ t ∈ Finset.range N, (D t - A t)) =
      (∑ t ∈ Finset.range N, D t) - (N : ℝ) * r +
        (∑ t ∈ Finset.range N, (r - q t)) + M N - M 0 := by
  have hs : (∑ t ∈ Finset.range N, (M (t + 1) - M t)) =
      ∑ t ∈ Finset.range N, (q t - A t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hf := hflow t (Finset.mem_range.mp ht)
    linarith
  rw [Finset.sum_range_sub] at hs
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hs ⊢
  linarith

/-- Cumulative order deficits are controlled by on-hand inventory and the
post-order shortfall. The sole pipeline hypothesis is its elementary aggregate
bound from an initially empty pipeline. -/
lemma cumulative_deficit_bound (J U Q q : ℕ → ℝ) (L N : ℕ) (r z : ℝ)
    (hposition : ∀ t < N,
      J t + U t = ((L : ℝ) + 1) * r + z - Q t - q t)
    (hpipeline : (∑ t ∈ Finset.range N, Q t) ≤
      (L : ℝ) * ∑ t ∈ Finset.range N, q t) :
    ((L : ℝ) + 1) * (∑ t ∈ Finset.range N, (r - q t)) ≤
      (∑ t ∈ Finset.range N, J t) +
        (∑ t ∈ Finset.range N, U t) - (N : ℝ) * z := by
  have hs : (∑ t ∈ Finset.range N, (J t + U t)) =
      ∑ t ∈ Finset.range N, (((L : ℝ) + 1) * r + z - Q t - q t) := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hposition t (Finset.mem_range.mp ht)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs ⊢
  nlinarith

/-- Shifting the sum of a nonnegative inventory sequence by one period can
only increase it when the initial inventory is zero. -/
lemma inventory_sum_shift (J : ℕ → ℝ) (N : ℕ) (hzero : J 0 = 0)
    (hnonneg : 0 ≤ J N) :
    (∑ t ∈ Finset.range N, J t) ≤ ∑ t ∈ Finset.range N, J (t + 1) := by
  have h := Finset.sum_range_sub J N
  rw [Finset.sum_sub_distrib, hzero] at h
  linarith

/-- Deterministic finite-horizon loss bound, retaining the terminal inventory
position as an explicit, uniformly bounded startup error. -/
lemma cumulative_loss_bound (M J U Q q A D : ℕ → ℝ)
    (L N : ℕ) (r z S : ℝ)
    (hflow : ∀ t < N, M (t + 1) = M t + q t - A t)
    (hposition : ∀ t < N,
      J t + U t = ((L : ℝ) + 1) * r + z - Q t - q t)
    (hpipeline : (∑ t ∈ Finset.range N, Q t) ≤
      (L : ℝ) * ∑ t ∈ Finset.range N, q t)
    (hMzero : M 0 = 0) (hMbound : M N ≤ S)
    (hJzero : J 0 = 0) (hJnonneg : 0 ≤ J N) :
    (∑ t ∈ Finset.range N, (D t - A t)) ≤
      (∑ t ∈ Finset.range N, D t) - (N : ℝ) * r +
        ((∑ t ∈ Finset.range N, J (t + 1)) +
          (∑ t ∈ Finset.range N, U t) - (N : ℝ) * z) /
            ((L : ℝ) + 1) + S := by
  have hdef := cumulative_deficit_bound J U Q q L N r z hposition hpipeline
  have hshift := inventory_sum_shift J N hJzero hJnonneg
  have hden : 0 < (L : ℝ) + 1 := by positivity
  have hb : (∑ t ∈ Finset.range N, (r - q t)) ≤
      ((∑ t ∈ Finset.range N, J (t + 1)) +
        (∑ t ∈ Finset.range N, U t) - (N : ℝ) * z) / ((L : ℝ) + 1) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  rw [cumulative_loss_identity M q A D r N hflow, hMzero]
  linarith

/-- Real-valued post-order inventory-position shortfall. -/
def shortfall (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) : ℝ :=
  (S : ℝ) - (position (cbsRun c S r ω t) : ℝ) -
    (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ)

lemma shortfall_nonneg (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    0 ≤ shortfall c S r ω t := by
  have hp := position_add_order_le c.L S r (cbsRun c S r ω t)
    (cbsRun_position_le c S r ω t)
  have hp' : (position (cbsRun c S r ω t) : ℝ) +
      (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ) ≤ (S : ℝ) := by exact_mod_cast hp
  unfold shortfall
  linarith

lemma shortfall_le (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    shortfall c S r ω t ≤ (S : ℝ) := by
  unfold shortfall
  have hm := (position (cbsRun c S r ω t)).coe_nonneg
  have hq := (cbsOrder c.L S r (cbsRun c S r ω t)).coe_nonneg
  linarith

lemma shortfall_eq_max (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    shortfall c S r ω t = max
      ((S : ℝ) - (position (cbsRun c S r ω t) : ℝ) - (r : ℝ)) 0 := by
  have hp := cbsRun_position_le c S r ω t
  have hq : (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ) =
      min ((S : ℝ) - (position (cbsRun c S r ω t) : ℝ)) (r : ℝ) := by
    change ((min (S - position (cbsRun c S r ω t)) r : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_min, NNReal.coe_sub hp]
  unfold shortfall
  rw [hq]
  rcases le_total ((S : ℝ) - (position (cbsRun c S r ω t) : ℝ)) (r : ℝ) with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_left (by linarith)]

lemma cbsRun_real_position_flow (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    (position (cbsRun c S r ω (t + 1)) : ℝ) =
      (position (cbsRun c S r ω t) : ℝ) +
        (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ) -
        (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ) := by
  have hp := position_step c (cbsRun c S r ω t)
    (cbsOrder c.L S r (cbsRun c S r ω t)) (ω.1 t)
  have hp' : (position (cbsRun c S r ω (t + 1)) : ℝ) +
      (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ) =
        (position (cbsRun c S r ω t) : ℝ) +
          (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ) := by exact_mod_cast hp
  linarith

lemma shortfall_step (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    shortfall c S r ω (t + 1) = max
      (shortfall c S r ω t +
        (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ) - (r : ℝ)) 0 := by
  rw [shortfall_eq_max, cbsRun_real_position_flow]
  congr 1
  unfold shortfall
  ring

lemma cbsRun_real_inventory_flow (c : Parameters) (S r : ℝ≥0) (ω : Sample) (t : ℕ) :
    ((cbsRun c S r ω (t + 1)).1 : ℝ) =
      ((cbsRun c S r ω t).1 : ℝ) + (arrival c (cbsRun c S r ω t) : ℝ) -
        (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ) := by
  have hp : (cbsRun c S r ω (t + 1)).1 +
      filledDemand c (cbsRun c S r ω t) (ω.1 t) =
      (cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t) := by
    simp only [cbsRun, step, filledDemand]
    simpa [min_comm] using
      (tsub_add_min (a := (cbsRun c S r ω t).1 + arrival c (cbsRun c S r ω t))
        (b := ω.1 t))
  have hp' : ((cbsRun c S r ω (t + 1)).1 : ℝ) +
      (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ) =
      ((cbsRun c S r ω t).1 : ℝ) + (arrival c (cbsRun c S r ω t) : ℝ) := by
    exact_mod_cast hp
  linarith

lemma cbsRun_inventory_block_identity (c : Parameters) (S r : ℝ≥0)
    (ω : Sample) (t n : ℕ) :
    (∑ j ∈ Finset.range n,
      (filledDemand c (cbsRun c S r ω (t + j)) (ω.1 (t + j)) : ℝ)) =
      ((cbsRun c S r ω t).1 : ℝ) +
        (∑ j ∈ Finset.range n, (arrival c (cbsRun c S r ω (t + j)) : ℝ)) -
          ((cbsRun c S r ω (t + n)).1 : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have hf := cbsRun_real_inventory_flow c S r ω (t + n)
    rw [show t + (n + 1) = (t + n) + 1 by omega]
    linarith

lemma shortfall_block_identity (c : Parameters) (S r : ℝ≥0)
    (ω : Sample) (t : ℕ) :
    shortfall c S r ω t +
      (∑ j ∈ Finset.range (c.L + 1),
        (filledDemand c (cbsRun c S r ω (t + j)) (ω.1 (t + j)) : ℝ)) =
      (S : ℝ) - ((cbsRun c S r ω (t + (c.L + 1))).1 : ℝ) := by
  rw [cbsRun_inventory_block_identity]
  have hsum : (∑ j ∈ Finset.range c.L,
      (arrival c (cbsRun c S r ω (t + j)) : ℝ)) =
      ∑ i : Fin c.L, ((cbsRun c S r ω t).2 i : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x : ℝ≥0 => (x : ℝ))
      (cbsRun_future_arrival c S r ω t i))
  rw [Finset.sum_range_succ, hsum, cbsRun_arrival_after_leadTime]
  simp only [shortfall, position, NNReal.coe_add, NNReal.coe_sum]
  ring

/-- The manuscript's shortfall envelope, proved for every zero-start sample
path; its chronological demand block begins one period after the block start. -/
lemma cbsRun_shortfall_window (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (t : ℕ) (z : ℝ) (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z) :
    shortfall c S r ω (t + (c.L + 1)) ≤ max z
      (finiteInventory (fun i => ω.1 (t + 1 + i)) (r : ℝ) c.L +
        ∑ i ∈ Finset.range c.L, ((ω.1 (t + 1 + i) : ℝ) - (r : ℝ))) := by
  apply shortfall_window_bound (fun j => shortfall c S r ω (t + j))
    (fun j => (filledDemand c (cbsRun c S r ω (t + j)) (ω.1 (t + j)) : ℝ))
    (fun i => ω.1 (t + 1 + i)) c.L (r : ℝ) z
  · intro j _
    simpa only [Nat.add_assoc] using le_of_eq (shortfall_step c S r ω (t + j))
  · have hb := shortfall_block_identity c S r ω t
    simp only [Nat.add_zero]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one]
    have hi := (cbsRun c S r ω (t + (c.L + 1))).1.coe_nonneg
    linarith
  · intro i _
    have hfill : filledDemand c (cbsRun c S r ω (t + (i + 1)))
        (ω.1 (t + (i + 1))) ≤ ω.1 (t + (i + 1)) := min_le_left _ _
    have hf : (filledDemand c (cbsRun c S r ω (t + (i + 1)))
        (ω.1 (t + (i + 1))) : ℝ) ≤ (ω.1 (t + (i + 1)) : ℝ) := by
      exact_mod_cast hfill
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hf

lemma lostSales_real_eq (c : Parameters) (s : State c.L) (d : ℝ≥0) :
    (lostSales c s d : ℝ) = (d : ℝ) - (filledDemand c s d : ℝ) := by
  have he : lostSales c s d + filledDemand c s d = d := by
    exact tsub_add_min
  have he' : (lostSales c s d : ℝ) + (filledDemand c s d : ℝ) = (d : ℝ) := by
    exact_mod_cast he
  linarith

/-- The actual zero-start CBS cumulative loss estimate, with a deterministic
boundary term at most `S`; no stationarity assumption is used. -/
lemma cbsRun_cumulative_loss_bound (c : Parameters) (S r : ℝ≥0) (ω : Sample)
    (N : ℕ) (z : ℝ) (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z) :
    (∑ t ∈ Finset.range N,
      (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) ≤
      (∑ t ∈ Finset.range N, (ω.1 t : ℝ)) - (N : ℝ) * (r : ℝ) +
        ((∑ t ∈ Finset.range N, ((cbsRun c S r ω (t + 1)).1 : ℝ)) +
          (∑ t ∈ Finset.range N, shortfall c S r ω t) - (N : ℝ) * z) /
            ((c.L : ℝ) + 1) + (S : ℝ) := by
  simp only [lostSales_real_eq]
  apply cumulative_loss_bound
    (fun t => (position (cbsRun c S r ω t) : ℝ))
    (fun t => ((cbsRun c S r ω t).1 : ℝ))
    (shortfall c S r ω)
    (fun t => ∑ i : Fin c.L, ((cbsRun c S r ω t).2 i : ℝ))
    (fun t => (cbsOrder c.L S r (cbsRun c S r ω t) : ℝ))
    (fun t => (filledDemand c (cbsRun c S r ω t) (ω.1 t) : ℝ))
    (fun t => (ω.1 t : ℝ)) c.L N (r : ℝ) z (S : ℝ)
  · intro t _
    exact cbsRun_real_position_flow c S r ω t
  · intro t _
    simp only [shortfall, position, NNReal.coe_add, NNReal.coe_sum]
    linarith
  · have hp := cbsRun_pipeline_sum_le c S r ω N
    exact_mod_cast hp
  · simp [cbsRun, initialState, position]
  · exact_mod_cast cbsRun_position_le c S r ω N
  · simp [cbsRun, initialState]
  · exact (cbsRun c S r ω N).1.coe_nonneg

lemma measurable_shortfall (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Measurable (fun ω => shortfall c S r ω t) := by
  unfold shortfall position
  have hs := measurable_cbsRun c S r t
  have hq := (measurable_cbsOrder c.L S r).comp hs
  fun_prop

end CappedBaseStockBounds


noncomputable section
open scoped NNReal ENNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

lemma sum_reverse_Ico (f : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    (∑ i ∈ Finset.Ico k m, f i) =
      ∑ j ∈ Finset.range (m-k), f (m-1-j) := by
  apply Finset.sum_bij (fun i _ => m-1-i)
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    simp only [Finset.mem_range]
    omega
  · intro i hi j hj hij
    simp only [Finset.mem_Ico] at hi hj
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨m-1-j, ?_, ?_⟩
    · simp only [Finset.mem_Ico]
      omega
    · omega
  · intro i hi
    simp only [Finset.mem_Ico] at hi
    congr 1
    omega

lemma inventory_window_bound (u A : ℕ → ℝ) (d rev : DemandPath)
    (m : ℕ) (r z : ℝ)
    (hstep : ∀ i < m, u (i+1) ≤ max (u i + A i - (d i : ℝ)) 0)
    (hcap : ∀ i < m, A i ≤ r)
    (hresources : u 0 + ∑ i ∈ Finset.range m, A i ≤ (m : ℝ)*r+z)
    (hrev : ∀ i < m, rev i = d (m-1-i)) :
    u m ≤ max (finiteInventory rev r m)
      (z - ∑ i ∈ Finset.range m, ((rev i : ℝ)-r)) := by
  have hsum : (∑ i ∈ Finset.range m, ((d i : ℝ)-r)) =
      ∑ i ∈ Finset.range m, ((rev i : ℝ)-r) := by
    rw [← Nat.Ico_zero_eq_range, sum_reverse_Ico _ m 0 (Nat.zero_le _)]
    simp only [Nat.sub_zero, Nat.Ico_zero_eq_range]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrev i (Finset.mem_range.mp hi)]
  apply lindley_terminal_bound u (fun i => A i - (d i : ℝ)) m
  · intro i hi
    simpa only [sub_eq_add_neg, add_assoc] using hstep i hi
  · apply le_trans _ (le_max_right _ _)
    rw [← hsum]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    linarith
  · intro k hk hkm
    apply le_trans _ (le_max_left _ _)
    calc
      (∑ i ∈ Finset.Ico k m, (A i - (d i : ℝ))) ≤
          ∑ i ∈ Finset.Ico k m, (r - (d i : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact sub_le_sub_right (hcap i (Finset.mem_Ico.mp hi).2) _
      _ = ∑ i ∈ Finset.range (m-k), (r - (rev i : ℝ)) := by
        rw [sum_reverse_Ico _ m k hkm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hrev i (by have := Finset.mem_range.mp hi; omega)]
      _ ≤ finiteInventory rev r m := by
        exact Finset.le_sup' (fun j => ∑ i ∈ Finset.range j, (r - (rev i : ℝ)))
          (Finset.mem_range.mpr (by omega))

lemma cbsRun_inventory_envelope (c : Parameters) (r z : ℝ)
    (hr : 0 ≤ r) (hz : 0 ≤ z) (ω : Sample) (t : ℕ) (ht : c.L ≤ t) :
    let S := Real.toNNReal (((c.L : ℝ)+1)*r+z)
    let rev : DemandPath := fun i => ω.1 (reversePrefixIndex t i)
    ((cbsRun c S (Real.toNNReal r) ω (t+1)).1 : ℝ) ≤
      max (finiteInventory rev r (c.L+1))
        (z - ∑ i ∈ Finset.range (c.L+1), ((rev i : ℝ)-r)) := by
  dsimp only
  let S := Real.toNNReal (((c.L : ℝ)+1)*r+z)
  let R := Real.toNNReal r
  have hS : (S : ℝ) = ((c.L : ℝ)+1)*r+z := by
    apply Real.coe_toNNReal
    positivity
  have hR : (R : ℝ) = r := Real.coe_toNNReal r hr
  have hend : t - c.L + (c.L+1) = t+1 := by omega
  have hbound := inventory_window_bound
    (fun i => ((cbsRun c S R ω (t-c.L+i)).1 : ℝ))
    (fun i => (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ))
    (fun i => ω.1 (t-c.L+i)) (fun i => ω.1 (reversePrefixIndex t i))
    (c.L+1) r z ?_ ?_ ?_ ?_
  · simpa only [hend] using hbound
  · intro i hi
    have heq : t-c.L+(i+1) = (t-c.L+i)+1 := by omega
    rw [heq]
    simp only [cbsRun, step, NNReal.coe_sub_def, NNReal.coe_add]
    exact le_rfl
  · intro i hi
    simpa only [hR] using
      (show (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ) ≤ (R : ℝ) by
        exact_mod_cast cbsRun_arrival_le c S R ω (t-c.L+i))
  · have hb := cbsRun_block_resources c S R ω (t-c.L)
    have hb' : ((cbsRun c S R ω (t-c.L)).1 : ℝ) +
        ∑ i ∈ Finset.range (c.L+1),
          (arrival c (cbsRun c S R ω (t-c.L+i)) : ℝ) ≤ (S : ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.add_zero, hS, Nat.cast_add, Nat.cast_one] using hb'
  · intro i hi
    change ω.1 (reversePrefixIndex t i) = ω.1 (t-c.L+(c.L+1-1-i))
    apply congrArg ω.1
    unfold reversePrefixIndex
    rw [if_pos (by omega)]
    omega

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock

namespace CappedBaseStockBounds

lemma integrable_demand (P : DemandLaw) (i : ℕ) :
    Integrable (fun d : DemandPath => (d i : ℝ)) (demandPathLaw P) := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i).integrable_comp_of_integrable
    P.finiteMean

lemma integral_demand (P : DemandLaw) (i : ℕ) :
    (∫ d : DemandPath, (d i : ℝ) ∂demandPathLaw P) = mean P := by
  have hm := measurePreserving_eval_infinitePi (fun _ : ℕ => P.law) i
  change (∫ d : DemandPath, ((Function.eval i) d : ℝ) ∂demandPathLaw P) = _
  rw [← integral_map_of_stronglyMeasurable hm.measurable NNReal.continuous_coe.stronglyMeasurable]
  change (∫ x : ℝ≥0, (x : ℝ) ∂(Measure.infinitePi (fun _ : ℕ => P.law)).map
    (Function.eval i)) = mean P
  rw [hm.map_eq]
  rfl

lemma integrable_demand_sum (P : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : DemandPath => ∑ i ∈ Finset.range m, ((d i : ℝ) - r))
      (demandPathLaw P) := by
  exact integrable_finsetSum _ (fun i _ => (integrable_demand P i).sub (integrable_const r))

lemma integral_demand_sum (P : DemandLaw) (r : ℝ) (m : ℕ) :
    (∫ d : DemandPath, (∑ i ∈ Finset.range m, ((d i : ℝ) - r)) ∂demandPathLaw P) =
      (m : ℝ) * (mean P - r) := by
  rw [integral_finsetSum (f := fun i (d : DemandPath) => (d i : ℝ) - r) _
    (fun i _ => (integrable_demand P i).sub (integrable_const r))]
  simp only [integral_sub (f := fun d : DemandPath => (d _ : ℝ)) (g := fun _ => r)
    (integrable_demand P _) (integrable_const r), integral_demand,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

lemma finiteInventory_succ (d : DemandPath) (r : ℝ) (m : ℕ) :
    finiteInventory d r (m + 1) =
      max (∑ i ∈ Finset.range (m + 1), (r - (d i : ℝ))) (finiteInventory d r m) := by
  unfold finiteInventory
  simp only [Finset.range_add_one (n := m + 1)]
  exact Finset.sup'_insert (by simp) _

lemma finiteInventory_nonneg (d : DemandPath) (r : ℝ) (m : ℕ) :
    0 ≤ finiteInventory d r m := by
  unfold finiteInventory
  simpa only [Finset.range_zero, Finset.sum_empty] using
    Finset.le_sup' (f := fun k => ∑ i ∈ Finset.range k, (r - (d i : ℝ)))
    (by simp : 0 ∈ Finset.range (m + 1))

lemma measurable_finiteInventory (r : ℝ) (m : ℕ) :
    Measurable (fun d : DemandPath => finiteInventory d r m) := by
  induction m with
  | zero => simpa [finiteInventory] using (measurable_const : Measurable (fun _ : DemandPath => (0 : ℝ)))
  | succ m ih =>
    simp only [finiteInventory_succ]
    exact Measurable.max (by fun_prop) ih

lemma integrable_finiteInventory (P : DemandLaw) (r : ℝ) (m : ℕ) :
    Integrable (fun d : DemandPath => finiteInventory d r m) (demandPathLaw P) := by
  induction m with
  | zero => simpa [finiteInventory] using (integrable_const (0 : ℝ) :
      Integrable (fun _ : DemandPath => (0 : ℝ)) (demandPathLaw P))
  | succ m ih =>
    simp only [finiteInventory_succ]
    exact (integrable_finsetSum _ (fun i _ => (integrable_const r).sub
      (integrable_demand P i))).sup ih

lemma inventory_envelope_expectation (P : DemandLaw) (r z : ℝ) (m : ℕ)
    (hrmu : r ≤ mean P) (_hz : 0 ≤ z)
    (hcert : (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r))) :
    (∫⁻ d, ENNReal.ofReal (max (finiteInventory d r m)
      (z - ∑ i ∈ Finset.range m, ((d i : ℝ) - r))) ∂demandPathLaw P) ≤
      ENNReal.ofReal z := by
  let B : DemandPath → ℝ := fun d => ∑ i ∈ Finset.range m, ((d i : ℝ) - r)
  let E : DemandPath → ℝ := fun d => max (finiteInventory d r m + B d - z) 0
  have hB : Integrable B (demandPathLaw P) := integrable_demand_sum P r m
  have hE : Integrable E (demandPathLaw P) :=
    (((integrable_finiteInventory P r m).add hB).sub (integrable_const z)).sup
      (integrable_const 0)
  have hEnonneg : 0 ≤ᵐ[demandPathLaw P] E :=
    Filter.Eventually.of_forall (fun d => le_max_right _ _)
  have hEcert : ENNReal.ofReal (∫ d, E d ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hE hEnonneg]
    simpa [E, B, certificateExcess, ENNReal.ofReal_max] using hcert
  have hEbound : (∫ d, E d ∂demandPathLaw P) ≤ (m : ℝ) * (mean P - r) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu))).mp hEcert
  have hid (d : DemandPath) : max (finiteInventory d r m) (z - B d) = z - B d + E d := by
    dsimp [E]
    rcases le_total (finiteInventory d r m) (z - B d) with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]
      ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
      ring
  have hEnv : Integrable (fun d => max (finiteInventory d r m) (z - B d))
      (demandPathLaw P) :=
    (integrable_finiteInventory P r m).sup ((integrable_const z).sub hB)
  rw [← ofReal_integral_eq_lintegral_ofReal hEnv
    (Filter.Eventually.of_forall (fun d => (finiteInventory_nonneg d r m).trans (le_max_left _ _)))]
  apply ENNReal.ofReal_le_ofReal
  simp_rw [hid]
  rw [integral_add (f := fun d => z - B d) (g := E) ((integrable_const z).sub hB) hE,
    integral_sub (f := fun _ => z) (g := B) (integrable_const z) hB]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hBmean : (∫ d, B d ∂demandPathLaw P) = (m : ℝ) * (mean P - r) :=
    integral_demand_sum P r m
  rw [hBmean]
  linarith

lemma excess_envelope_expectation (P : DemandLaw) (r z : ℝ) (m : ℕ)
    (hrmu : r ≤ mean P) (hz : 0 ≤ z)
    (hcert : (∫⁻ d, certificateExcess d r z m ∂demandPathLaw P) ≤
      ENNReal.ofReal ((m : ℝ) * (mean P - r))) :
    (∫⁻ d, ENNReal.ofReal (z + max (finiteInventory d r m +
      (∑ i ∈ Finset.range m, ((d i : ℝ) - r)) - z) 0) ∂demandPathLaw P) ≤
      ENNReal.ofReal (z + (m : ℝ) * (mean P - r)) := by
  have hmax (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by simp
  simp_rw [ENNReal.ofReal_add hz (le_max_right _ _), hmax]
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  rw [ENNReal.ofReal_add hz (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu))]
  exact add_le_add le_rfl hcert

end CappedBaseStockBounds


open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators Topology
noncomputable section
namespace CappedBaseStockBounds
open CappedBaseStock

lemma averageCost_le_of_sum_bound (P : DemandLaw) (f : ℕ → Sample → ℝ≥0∞)
    (a C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ᶠ T : ℕ in atTop,
      (∑ t ∈ Finset.range (T+1), ∫⁻ ω, f t ω ∂sampleLaw P) ≤ a*(T+1)+C) :
    averageCost P f ≤ a := by
  have hlim : Tendsto (fun T : ℕ => a + C / (T+1 : ℝ≥0∞)) atTop (𝓝 a) := by
    have hinv : Tendsto (fun T : ℕ => ((T+1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hmul := ENNReal.Tendsto.const_mul hinv (Or.inr hC)
    simpa [div_eq_mul_inv] using tendsto_const_nhds.add hmul
  unfold averageCost
  apply (limsup_le_limsup ?_).trans (le_of_eq hlim.limsup_eq)
  filter_upwards [h] with T hT
  calc
    _ ≤ (a * (T+1) + C) / (T+1) := ENNReal.div_le_div_right hT _
    _ = a + C / (T+1) := by
      rw [ENNReal.add_div, ENNReal.mul_div_cancel_right (by simp) (by simp)]

lemma averageCost_le_of_lintegral_le (P : DemandLaw) (f : ℕ → Sample → ℝ≥0∞)
    (a : ℝ≥0∞) (h : ∀ t, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ a) :
    averageCost P f ≤ a := by
  apply averageCost_le_of_sum_bound P f a 0 (by simp)
  apply Filter.Eventually.of_forall
  intro T
  calc
    _ ≤ ∑ t ∈ Finset.range (T+1), a := Finset.sum_le_sum (fun t _ => h t)
    _ = _ := by simp [mul_comm]

lemma sum_le_of_eventually_le (u : ℕ → ℝ≥0∞) (a B : ℝ≥0∞) (m : ℕ)
    (hB : ∀ t, u t ≤ B) (ha : ∀ t, m ≤ t → u t ≤ a) (N : ℕ) :
    (∑ t ∈ Finset.range N, u t) ≤ a*N+B*m := by
  by_cases hm : m ≤ N
  · rw [← Finset.sum_range_add_sum_Ico u hm]
    have hb : (∑ t ∈ Finset.range m, u t) ≤ B*m := by
      calc
        _ ≤ ∑ t ∈ Finset.range m, B := Finset.sum_le_sum (fun t _ => hB t)
        _ = _ := by simp [mul_comm]
    have ht : (∑ t ∈ Finset.Ico m N, u t) ≤ a*N := by
      calc
        _ ≤ ∑ t ∈ Finset.Ico m N, a := Finset.sum_le_sum (fun t ht => ha t (Finset.mem_Ico.mp ht).1)
        _ = a*(N-m : ℕ) := by simp [mul_comm]
        _ ≤ a*N := by gcongr; omega
    simpa [add_comm] using add_le_add hb ht
  · have hnm : N ≤ m := by omega
    calc
      _ ≤ ∑ t ∈ Finset.range N, B := Finset.sum_le_sum (fun t _ => hB t)
      _ = B*N := by simp [mul_comm]
      _ ≤ B*m := by gcongr
      _ ≤ a*N+B*m := le_add_left le_rfl

lemma averageCost_le_of_eventually_lintegral_le (P : DemandLaw)
    (f : ℕ → Sample → ℝ≥0∞) (a B : ℝ≥0∞) (hBtop : B ≠ ∞)
    (hB : ∀ t, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ B)
    (h : ∀ᶠ t : ℕ in atTop, (∫⁻ ω, f t ω ∂sampleLaw P) ≤ a) :
    averageCost P f ≤ a := by
  obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp h
  apply averageCost_le_of_sum_bound P f a (B*m) (ENNReal.mul_ne_top hBtop (by simp))
  apply Filter.Eventually.of_forall
  intro T
  simpa only [Nat.cast_add, Nat.cast_one] using
    sum_le_of_eventually_le _ a B m hB hm (T+1)

end CappedBaseStockBounds


noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology
open CappedBaseStock
namespace CappedBaseStockBounds

lemma integrable_cbs_inventory (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω => ((cbsRun c S r ω t).1 : ℝ)) (sampleLaw P) := by
  apply (integrable_const (S : ℝ)).mono'
  · have hm := (measurable_cbsRun c S r t).fst
    exact (NNReal.continuous_coe.measurable.comp hm).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      (show ((cbsRun c S r ω t).1 : ℝ) ≤ (S : ℝ) from
        NNReal.coe_le_coe.mpr (cbsRun_inventory_le c S r ω t))

lemma integral_inventory_le_of_lintegral (P : DemandLaw) (c : Parameters)
    (S r : ℝ≥0) (t : ℕ) (z : ℝ) (hz : 0 ≤ z)
    (h : (∫⁻ ω, ((cbsRun c S r ω t).1 : ℝ≥0∞) ∂sampleLaw P) ≤ ENNReal.ofReal z) :
    (∫ ω, ((cbsRun c S r ω t).1 : ℝ) ∂sampleLaw P) ≤ z := by
  apply (ENNReal.ofReal_le_ofReal_iff hz).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_cbs_inventory P c S r t)
    (Filter.Eventually.of_forall (fun _ => NNReal.coe_nonneg _))]
  simpa only [ENNReal.ofReal_coe_nnreal] using h

lemma finite_cap_inventory_lintegral (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) (t : ℕ) :
    (∫⁻ ω, ((cbsRun c (Real.toNNReal (((c.L : ℝ)+1)*r+z))
      (Real.toNNReal r) ω (t+1)).1 : ℝ≥0∞) ∂sampleLaw P) ≤ ENNReal.ofReal z := by
  by_cases ht : c.L ≤ t
  · let F : DemandPath → ℝ≥0∞ := fun d =>
      ENNReal.ofReal (max (finiteInventory d r (c.L+1))
        (z - ∑ i ∈ Finset.range (c.L+1), ((d i : ℝ)-r)))
    have hF : Measurable F := by
      have hm := measurable_finiteInventory r (c.L+1)
      dsimp [F]
      fun_prop
    calc
      _ ≤ ∫⁻ ω, F (fun i => ω.1 (reversePrefixIndex t i)) ∂sampleLaw P := by
        apply lintegral_mono
        intro ω
        dsimp only
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal
          (cbsRun_inventory_envelope c r z feasible.1 feasible.2.2.1 ω t ht)
      _ = ∫⁻ d, F d ∂demandPathLaw P :=
        lintegral_sample_reindex P (reversePrefixIndex t)
          (reversePrefixIndex_injective t) F hF
      _ ≤ ENNReal.ofReal z := inventory_envelope_expectation P r z (c.L+1)
        feasible.2.1 feasible.2.2.1 (by
          simpa only [Nat.cast_add, Nat.cast_one] using feasible.2.2.2.2)
  · have hz (ω : Sample) : (cbsRun c (Real.toNNReal (((c.L : ℝ)+1)*r+z))
        (Real.toNNReal r) ω (t+1)).1 = 0 :=
      cbsRun_inventory_zero_initial c _ _ ω (t+1) (by omega)
    simp only [hz, ENNReal.coe_zero, lintegral_zero]
    exact zero_le

lemma finite_cap_inventory_proved (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      ((cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω (t + 1)).1 : ℝ≥0∞)) ≤ ENNReal.ofReal z := by
  exact averageCost_le_of_lintegral_le P _ (ENNReal.ofReal z)
    (finite_cap_inventory_lintegral P c r z feasible)

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

lemma integrable_sample_demand (P : DemandLaw) (t : ℕ) :
    Integrable (fun ω : Sample => (ω.1 t : ℝ)) (sampleLaw P) := by
  exact measurePreserving_fst.integrable_comp_of_integrable (integrable_demand P t)

lemma integral_sample_demand (P : DemandLaw) (t : ℕ) :
    (∫ ω : Sample, (ω.1 t : ℝ) ∂sampleLaw P) = mean P := by
  have h := integral_sample_reindex P id Function.injective_id
    (fun d => (d t : ℝ)) (by fun_prop)
  simpa only [id_eq, integral_demand] using h

lemma integrable_nonneg_bounded {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (f : α → ℝ) (B : ℝ) (hm : Measurable f)
    (hn : ∀ x, 0 ≤ f x) (hb : ∀ x, f x ≤ B) : Integrable f μ := by
  exact (integrable_const B).mono_nonneg hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hn) (Filter.Eventually.of_forall hb)

lemma integrable_shortfall (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω => shortfall c S r ω t) (sampleLaw P) :=
  integrable_nonneg_bounded _ _ (S : ℝ) (measurable_shortfall c S r t)
    (fun ω => shortfall_nonneg c S r ω t) (fun ω => shortfall_le c S r ω t)

lemma integrable_inventory (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω => ((cbsRun c S r ω t).1 : ℝ)) (sampleLaw P) := by
  apply integrable_nonneg_bounded _ _ (S : ℝ)
  · exact NNReal.continuous_coe.measurable.comp ((measurable_cbsRun c S r t).fst)
  · intro ω
    positivity
  · intro ω
    exact_mod_cast cbsRun_inventory_le c S r ω t

lemma integrable_loss (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    Integrable (fun ω => (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ))
      (sampleLaw P) := by
  apply (integrable_sample_demand P t).mono_nonneg
  · have hm := measurable_cbsRun c S r t
    have h : Measurable (fun ω => (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ)) := by
      unfold lostSales arrival
      fun_prop
    exact h.aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun ω => NNReal.coe_nonneg _)
  · apply Filter.Eventually.of_forall
    intro ω
    exact_mod_cast (tsub_le_self : lostSales c (cbsRun c S r ω t) (ω.1 t) ≤ ω.1 t)

lemma integral_inventory_bound (P : DemandLaw) (c : Parameters) (S r : ℝ≥0)
    (z : ℝ) (hz : 0 ≤ z) (t : ℕ)
    (hI : (∫⁻ ω, ((cbsRun c S r ω t).1 : ℝ≥0∞) ∂sampleLaw P) ≤ ENNReal.ofReal z) :
    (∫ ω, ((cbsRun c S r ω t).1 : ℝ) ∂sampleLaw P) ≤ z := by
  apply (ENNReal.ofReal_le_ofReal_iff hz).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_inventory P c S r t)
    (Filter.Eventually.of_forall (fun ω => NNReal.coe_nonneg _))]
  simpa only [ENNReal.ofReal_coe_nnreal] using hI

lemma integral_shortfall_le_stock (P : DemandLaw) (c : Parameters) (S r : ℝ≥0) (t : ℕ) :
    (∫ ω, shortfall c S r ω t ∂sampleLaw P) ≤ (S : ℝ) := by
  have h := integral_mono (integrable_shortfall P c S r t) (integrable_const (S : ℝ))
    (fun ω => shortfall_le c S r ω t)
  simpa using h

lemma real_sum_le_of_eventually_le (u : ℕ → ℝ) (a B : ℝ) (m : ℕ)
    (ha0 : 0 ≤ a) (hB0 : 0 ≤ B) (hB : ∀ t, u t ≤ B)
    (ha : ∀ t, m ≤ t → u t ≤ a) (N : ℕ) :
    (∑ t ∈ Finset.range N, u t) ≤ a * N + B * m := by
  by_cases hm : m ≤ N
  · rw [← Finset.sum_range_add_sum_Ico u hm]
    have hb : (∑ t ∈ Finset.range m, u t) ≤ B * m := by
      calc
        _ ≤ ∑ t ∈ Finset.range m, B := Finset.sum_le_sum (fun t _ => hB t)
        _ = _ := by simp [mul_comm]
    have ht : (∑ t ∈ Finset.Ico m N, u t) ≤ a * N := by
      calc
        _ ≤ ∑ t ∈ Finset.Ico m N, a :=
          Finset.sum_le_sum (fun t ht => ha t (Finset.mem_Ico.mp ht).1)
        _ = a * (N - m : ℕ) := by simp [mul_comm]
        _ ≤ a * N := by gcongr; omega
    linarith
  · have hnm : N ≤ m := by omega
    calc
      _ ≤ ∑ t ∈ Finset.range N, B := Finset.sum_le_sum (fun t _ => hB t)
      _ = B * N := by simp [mul_comm]
      _ ≤ B * m := by gcongr
      _ ≤ a * N + B * m := by nlinarith [mul_nonneg ha0 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

lemma integral_shortfall_window_bound (P : DemandLaw) (c : Parameters) (S r : ℝ≥0)
    (z : ℝ) (hz : 0 ≤ z) (hrmu : (r : ℝ) ≤ mean P)
    (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z)
    (hcert : (∫⁻ d, certificateExcess d (r : ℝ) z c.L ∂demandPathLaw P) ≤
      ENNReal.ofReal ((c.L : ℝ) * (mean P - (r : ℝ)))) (t : ℕ) :
    (∫ ω, shortfall c S r ω (t + (c.L + 1)) ∂sampleLaw P) ≤
      z + (c.L : ℝ) * (mean P - (r : ℝ)) := by
  let F : DemandPath → ℝ≥0∞ := fun d => ENNReal.ofReal (z + max
    (finiteInventory d (r : ℝ) c.L +
      (∑ i ∈ Finset.range c.L, ((d i : ℝ) - (r : ℝ))) - z) 0)
  have hm : Measurable F := by
    dsimp [F]
    apply ENNReal.measurable_ofReal.comp
    exact measurable_const.add ((((measurable_finiteInventory (r : ℝ) c.L).add
      (by fun_prop)).sub measurable_const).max measurable_const)
  have hlin : (∫⁻ ω, ENNReal.ofReal (shortfall c S r ω (t + (c.L + 1))) ∂sampleLaw P) ≤
      ENNReal.ofReal (z + (c.L : ℝ) * (mean P - (r : ℝ))) := by
    calc
      _ ≤ ∫⁻ ω, F (fun i => ω.1 (t + 1 + i)) ∂sampleLaw P := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        dsimp [F]
        have he := cbsRun_shortfall_window c S r ω t z hS
        have hmax (x : ℝ) : max z x = z + max (x-z) 0 := by
          rcases le_total z x with h | h
          · rw [max_eq_right h, max_eq_left (sub_nonneg.mpr h)]
            ring
          · rw [max_eq_left h, max_eq_right (sub_nonpos.mpr h)]
            ring
        rwa [hmax] at he
      _ = ∫⁻ d, F d ∂demandPathLaw P :=
        lintegral_sample_reindex P (fun i => t + 1 + i)
          (by intro i j h; exact Nat.add_left_cancel h) F hm
      _ ≤ _ := excess_envelope_expectation P (r : ℝ) z c.L hrmu hz hcert
  apply (ENNReal.ofReal_le_ofReal_iff
    (add_nonneg hz (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu)))).mp
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_shortfall P c S r _)
    (Filter.Eventually.of_forall (fun ω => shortfall_nonneg c S r ω _))]
  exact hlin

lemma sum_integral_shortfall_bound (P : DemandLaw) (c : Parameters) (S r : ℝ≥0)
    (z : ℝ) (hz : 0 ≤ z) (hrmu : (r : ℝ) ≤ mean P)
    (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z)
    (hcert : (∫⁻ d, certificateExcess d (r : ℝ) z c.L ∂demandPathLaw P) ≤
      ENNReal.ofReal ((c.L : ℝ) * (mean P - (r : ℝ)))) (N : ℕ) :
    (∑ t ∈ Finset.range N, ∫ ω, shortfall c S r ω t ∂sampleLaw P) ≤
      (z + (c.L : ℝ) * (mean P - (r : ℝ))) * (N : ℝ) +
        (S : ℝ) * ((c.L : ℝ) + 1) := by
  have h := real_sum_le_of_eventually_le
    (fun t => ∫ ω, shortfall c S r ω t ∂sampleLaw P)
    (z + (c.L : ℝ) * (mean P - (r : ℝ))) (S : ℝ) (c.L + 1)
    (add_nonneg hz (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr hrmu))) S.coe_nonneg
    (integral_shortfall_le_stock P c S r) ?_ N
  · simpa only [Nat.cast_add, Nat.cast_one] using h
  · intro t ht
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le ht
    simpa only [Nat.add_comm] using integral_shortfall_window_bound P c S r z hz hrmu hS hcert u

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

/-- Integrating the finite-horizon samplewise material-balance estimate is
legitimate because inventory and shortfall are bounded and demand is integrable. -/
lemma cbsRun_cumulative_expected_loss_bound (P : DemandLaw) (c : Parameters)
    (S r : ℝ≥0) (N : ℕ) (z : ℝ)
    (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z) :
    (∑ t ∈ Finset.range N,
      ∫ ω, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) ≤
      (N : ℝ) * mean P - (N : ℝ) * (r : ℝ) +
        ((∑ t ∈ Finset.range N,
            ∫ ω, ((cbsRun c S r ω (t + 1)).1 : ℝ) ∂sampleLaw P) +
          (∑ t ∈ Finset.range N,
            ∫ ω, shortfall c S r ω t ∂sampleLaw P) - (N : ℝ) * z) /
            ((c.L : ℝ) + 1) + (S : ℝ) := by
  have hD := integrable_finsetSum (Finset.range N)
    (fun t _ => integrable_sample_demand P t)
  have hI := integrable_finsetSum (Finset.range N)
    (fun t _ => integrable_inventory P c S r (t + 1))
  have hU := integrable_finsetSum (Finset.range N)
    (fun t _ => integrable_shortfall P c S r t)
  have hLoss := integrable_finsetSum (Finset.range N)
    (fun t _ => integrable_loss P c S r t)
  have hR := (hD.sub (integrable_const ((N : ℝ) * (r : ℝ)))).add
    (((hI.add hU).sub (integrable_const ((N : ℝ) * z))).div_const ((c.L : ℝ) + 1))
  have hb := integral_mono hLoss (hR.add (integrable_const (S : ℝ)))
    (fun ω => cbsRun_cumulative_loss_bound c S r ω N z hS)
  have e1 := integral_add hR (integrable_const (S : ℝ))
  have e2 := integral_add (hD.sub (integrable_const ((N : ℝ) * (r : ℝ))))
    (((hI.add hU).sub (integrable_const ((N : ℝ) * z))).div_const ((c.L : ℝ) + 1))
  have e3 := integral_sub hD (integrable_const ((N : ℝ) * (r : ℝ)))
  have e4 := integral_sub (hI.add hU) (integrable_const ((N : ℝ) * z))
  have e5 := integral_add hI hU
  simp only [Pi.add_apply, Pi.sub_apply] at hb e1 e2 e3 e4 e5
  rw [integral_finsetSum (Finset.range N) (fun t _ => integrable_loss P c S r t),
    e1, e2, e3, integral_div, e4, e5,
    integral_finsetSum (Finset.range N) (fun t _ => integrable_sample_demand P t),
    integral_finsetSum (Finset.range N) (fun t _ => integrable_inventory P c S r (t + 1)),
    integral_finsetSum (Finset.range N) (fun t _ => integrable_shortfall P c S r t)] at hb
  simpa only [integral_sample_demand, integral_const, probReal_univ,
    one_smul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hb

end CappedBaseStockBounds


noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators
open CappedBaseStock
namespace CappedBaseStockBounds

lemma lost_average_bound_of_inventory_bound (P : DemandLaw) (c : Parameters)
    (S r : ℝ≥0) (z : ℝ) (hz : 0 ≤ z) (hrmu : (r : ℝ) ≤ mean P)
    (hS : (S : ℝ) = ((c.L : ℝ) + 1) * (r : ℝ) + z)
    (hcert : (∫⁻ d, certificateExcess d (r : ℝ) z c.L ∂demandPathLaw P) ≤
      ENNReal.ofReal ((c.L : ℝ) * (mean P - (r : ℝ))))
    (hI : ∀ t, (∫⁻ ω, ((cbsRun c S r ω (t + 1)).1 : ℝ≥0∞) ∂sampleLaw P) ≤
      ENNReal.ofReal z) :
    averageCost P (fun t ω => (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((mean P - (r : ℝ)) +
        (z + (c.L : ℝ) * (mean P - (r : ℝ))) / ((c.L : ℝ) + 1)) := by
  let a : ℝ := (mean P - (r : ℝ)) +
    (z + (c.L : ℝ) * (mean P - (r : ℝ))) / ((c.L : ℝ) + 1)
  have ha : 0 ≤ a := by
    have hdelta : 0 ≤ mean P - (r : ℝ) := sub_nonneg.mpr hrmu
    dsimp [a]
    positivity
  have hden : 0 < (c.L : ℝ) + 1 := by positivity
  have hsum (N : ℕ) :
      (∑ t ∈ Finset.range N,
        ∫ ω, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) ≤
        a * (N : ℝ) + 2 * (S : ℝ) := by
    have hl := cbsRun_cumulative_expected_loss_bound P c S r N z hS
    have hu := sum_integral_shortfall_bound P c S r z hz hrmu hS hcert N
    have hi : (∑ t ∈ Finset.range N,
        ∫ ω, ((cbsRun c S r ω (t + 1)).1 : ℝ) ∂sampleLaw P) ≤ (N : ℝ) * z := by
      calc
        _ ≤ ∑ t ∈ Finset.range N, z := Finset.sum_le_sum
          (fun t _ => integral_inventory_bound P c S r z hz (t+1) (hI t))
        _ = _ := by simp
    have hquot :
        ((∑ t ∈ Finset.range N,
            ∫ ω, ((cbsRun c S r ω (t + 1)).1 : ℝ) ∂sampleLaw P) +
          (∑ t ∈ Finset.range N, ∫ ω, shortfall c S r ω t ∂sampleLaw P) -
            (N : ℝ) * z) / ((c.L : ℝ) + 1) ≤
        ((z + (c.L : ℝ) * (mean P - (r : ℝ))) * (N : ℝ) +
          (S : ℝ) * ((c.L : ℝ) + 1)) / ((c.L : ℝ) + 1) := by
      apply div_le_div_of_nonneg_right _ hden.le
      linarith
    calc
      _ ≤ (N : ℝ) * mean P - (N : ℝ) * (r : ℝ) +
        ((z + (c.L : ℝ) * (mean P - (r : ℝ))) * (N : ℝ) +
          (S : ℝ) * ((c.L : ℝ) + 1)) / ((c.L : ℝ) + 1) + (S : ℝ) := by
            linarith
      _ = _ := by dsimp [a]; field_simp; ring
  apply averageCost_le_of_sum_bound P _ (ENNReal.ofReal a) (ENNReal.ofReal (2 * (S : ℝ)))
    ENNReal.ofReal_ne_top
  apply Filter.Eventually.of_forall
  intro T
  have hlin (t : ℕ) :
      (∫⁻ ω, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ≥0∞) ∂sampleLaw P) =
        ENNReal.ofReal (∫ ω, (lostSales c (cbsRun c S r ω t) (ω.1 t) : ℝ) ∂sampleLaw P) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_loss P c S r t)
      (Filter.Eventually.of_forall (fun ω => NNReal.coe_nonneg _))]
    simp only [ENNReal.ofReal_coe_nnreal]
  simp_rw [hlin]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => integral_nonneg
    (fun ω => NNReal.coe_nonneg _))]
  calc
    _ ≤ ENNReal.ofReal (a * ((T+1 : ℕ) : ℝ) + 2 * (S : ℝ)) :=
      ENNReal.ofReal_le_ofReal (hsum (T+1))
    _ = _ := by
      rw [ENNReal.ofReal_add (mul_nonneg ha (Nat.cast_nonneg _)) (by positivity),
        ENNReal.ofReal_mul ha]
      rw [ENNReal.ofReal_natCast]
      simp only [Nat.cast_add, Nat.cast_one]

lemma finite_cap_lost_sales_proved (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      (lostSales c (cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω t) (ω.1 t) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((mean P - r) +
        (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) := by
  have hr : 0 ≤ r := feasible.1
  have hz : 0 ≤ z := feasible.2.2.1
  have hS : 0 ≤ ((c.L : ℝ) + 1) * r + z := by positivity
  have h := lost_average_bound_of_inventory_bound P c
    (Real.toNNReal (((c.L : ℝ) + 1) * r + z)) (Real.toNNReal r) z hz
    (by simpa only [Real.coe_toNNReal r hr] using feasible.2.1)
    (by rw [Real.coe_toNNReal _ hS, Real.coe_toNNReal r hr])
    (by simpa only [Real.coe_toNNReal r hr] using feasible.2.2.2.1)
    (finite_cap_inventory_lintegral P c r z feasible)
  simpa only [Real.coe_toNNReal r hr] using h

end CappedBaseStockBounds

open CappedBaseStock


theorem solution (P : DemandLaw) (c : Parameters) (r z : ℝ)
    (feasible : CertificateFeasible P c r z) :
    averageCost P (fun t ω =>
      (lostSales c (cbsRun c (Real.toNNReal (((c.L : ℝ) + 1) * r + z))
        (Real.toNNReal r) ω t) (ω.1 t) : ℝ≥0∞)) ≤
      ENNReal.ofReal ((mean P - r) +
        (z + (c.L : ℝ) * (mean P - r)) / ((c.L : ℝ) + 1)) := by
  exact CappedBaseStockBounds.finite_cap_lost_sales_proved P c r z feasible

