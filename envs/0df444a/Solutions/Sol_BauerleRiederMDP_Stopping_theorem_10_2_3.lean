-- Prove2me | solution 1 for BauerleRiederMDP.Stopping.theorem_10_2_3
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:29:13.019675+00:00
-- url     : https://prove2.me/submissions/7c27b6de-49e0-4575-834a-056ae33a39d6

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim
import Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_2

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

namespace MDPS1023

variable {E : Type*} [MeasurableSpace E]

lemma erealIntegral_mono {α : Type*} [MeasurableSpace α] (μ : Measure α) {v w : α → EReal}
    (h : ∀ x, v x ≤ w x) : erealIntegral μ v ≤ erealIntegral μ w := by
  unfold erealIntegral
  refine add_le_add (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal (sup_le_sup_right (h x) _))) ?_
  exact EReal.neg_le_neg_iff.2 (EReal.coe_ennreal_le_coe_ennreal_iff.2
    (lintegral_mono fun x => EReal.toENNReal_le_toENNReal
      (sup_le_sup_right (EReal.neg_le_neg_iff.2 (h x)) _)))

lemma measurable_erealIntegral (Q : E → Measure E) (hQ : Measurable Q) {v : E → EReal}
    (hv : Measurable v) : Measurable fun x => erealIntegral (Q x) v := by
  unfold erealIntegral
  have h1 : Measurable fun y => (v y ⊔ 0).toENNReal := (hv.sup measurable_const).ereal_toENNReal
  have h2 : Measurable fun y => ((-v y) ⊔ 0).toENNReal :=
    ((continuous_neg.measurable.comp hv).sup measurable_const).ereal_toENNReal
  have k1 := (Measure.measurable_lintegral h1).comp hQ
  have k2 := (Measure.measurable_lintegral h2).comp hQ
  exact (measurable_coe_ennreal_ereal.comp k1).add
    (continuous_neg.measurable.comp (measurable_coe_ennreal_ereal.comp k2))

lemma beta_nonneg (P : StationaryProblem E) : (0 : EReal) ≤ (P.beta : EReal) := by
  exact_mod_cast P.beta_mem.1.le

lemma T_mono (P : StationaryProblem E) {v w : E → EReal} (h : ∀ x, v x ≤ w x) (x : E) :
    P.T v x ≤ P.T w x := by
  unfold StationaryProblem.T
  exact max_le_max le_rfl (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (erealIntegral_mono _ h) (beta_nonneg P)))

lemma g_le_T (P : StationaryProblem E) (v : E → EReal) (x : E) : (P.g x : EReal) ≤ P.T v x :=
  le_max_left _ _

lemma J_succ_mono (P : StationaryProblem E) (n : ℕ) (x : E) : P.J n x ≤ P.J (n + 1) x := by
  induction n generalizing x with
  | zero => exact g_le_T P _ x
  | succ n ih => exact T_mono P ih x

lemma J_mono (P : StationaryProblem E) (x : E) : Monotone fun n => P.J n x :=
  monotone_nat_of_le_succ fun n => J_succ_mono P n x

lemma g_le_J (P : StationaryProblem E) (n : ℕ) (x : E) : (P.g x : EReal) ≤ P.J n x :=
  J_mono P x (Nat.zero_le n)

lemma J_le_Jlim (P : StationaryProblem E) (n : ℕ) (x : E) : P.J n x ≤ P.Jlim x :=
  le_iSup (fun n => P.J n x) n

lemma d_anti (P : StationaryProblem E) (x : E) : Antitone fun n => P.d n x := by
  intro m n hmn
  unfold StationaryProblem.d
  refine EReal.sub_le_sub le_rfl ?_
  exact mul_le_mul_of_nonneg_left (erealIntegral_mono _ fun y => J_mono P y (by omega))
    (beta_nonneg P)

lemma J_measurable (P : StationaryProblem E) (n : ℕ) : Measurable (P.J n) := by
  induction n with
  | zero => exact measurable_coe_real_ereal.comp P.g_meas
  | succ n ih =>
    change Measurable fun x => max (P.g x : EReal)
      ((P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J n))
    exact (measurable_coe_real_ereal.comp P.g_meas).max
      ((measurable_coe_real_ereal.comp P.c_meas).add
        ((measurable_erealIntegral P.QX P.QX_meas ih).const_mul _))

lemma sub_nonneg_iff (g c : ℝ) (y : EReal) :
    0 ≤ (g : EReal) - (c : EReal) - y ↔ (c : EReal) + y ≤ g := by
  induction y using EReal.rec with
  | bot => simp [← EReal.coe_sub]
  | top => simp
  | coe y =>
    rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_nonneg, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma mem_stopSet_succ (P : StationaryProblem E) (n : ℕ) (x : E) :
    x ∈ P.stopSet (n + 1) ↔ 0 ≤ P.d (n + 1) x := by
  unfold StationaryProblem.stopSet StationaryProblem.d
  simp only [Set.mem_ofPred_eq, Nat.add_sub_cancel]
  rw [sub_nonneg_iff]
  change max _ _ = _ ↔ _
  constructor
  · intro h; rw [← h]; exact le_max_right _ _
  · intro h; exact max_eq_left h

lemma hitTime_le_iff (S : Set E) (w : ℕ → E) (n : ℕ) :
    hitTime S w ≤ (n : ℕ∞) ↔ ∃ k ≤ n, w k ∈ S := by
  unfold hitTime
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : ((n + 1 : ℕ) : ℕ∞) ≤ sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S}) := by
      refine le_sInf ?_
      rintro _ ⟨k, hk, rfl⟩
      have : ¬ k ≤ n := fun hkn => hc k hkn hk
      show ((n + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞)
      exact_mod_cast (by omega : n + 1 ≤ k)
    have := this.trans h
    have : n + 1 ≤ n := by exact_mod_cast this
    omega
  · rintro ⟨k, hk, hS⟩
    have hmem : (k : ℕ∞) ∈ (fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | w k ∈ S} := ⟨k, hS, rfl⟩
    exact (sInf_le hmem).trans (by exact_mod_cast hk)

lemma isStopTime_hitTime {S : Set E} (hS : MeasurableSet S) : IsStopTime (hitTime S) := by
  intro n
  have : {w : ℕ → E | hitTime S w ≤ (n : ℕ∞)} =
      (fun w : ℕ → E => fun i : Fin (n + 1) => w i) ⁻¹'
        (⋃ k : Fin (n + 1), {f : Fin (n + 1) → E | f k ∈ S}) := by
    ext w
    simp only [Set.mem_ofPred_eq, hitTime_le_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨k, hk, h⟩; exact ⟨⟨k, by omega⟩, h⟩
    · rintro ⟨k, h⟩; exact ⟨k, by omega, h⟩
  rw [this]
  exact MeasurableSet.preimage (MeasurableSet.iUnion fun k => measurable_pi_apply k hS)
    (comap_measurable _)

end MDPS1023

open MDPS1023 in
open BauerleRiederMDP.Stopping in
theorem solution {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr) :
    (∃ d : E → EReal,
      (∀ x : E, Tendsto (fun n => P.d n x) atTop (𝓝 (d x))) ∧
      ({x : E | 0 ≤ d x} = ⋂ n : ℕ, P.stopSet n) ∧
      ({x : E | 0 ≤ d x} = {x : E | P.Jlim x = (P.g x : EReal)}) ∧
      P.IsMaximizer {x : E | 0 ≤ d x} P.Jlim) ∧
    ((∀ x : E, P.T (P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)}) x ≤
        P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x) →
      (∀ x : E, Pr x {w | P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)} w = ⊤} = 0) →
      (∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x = P.Vstar Pr x) ∧
      (AssumptionBLim P Pr →
        P.IsOptimal Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) ∧
        ∀ x : E, P.Gf Pr {y : E | P.Jlim y = (P.g y : EReal)} x =
          P.EReward Pr (P.ruleTime {y : E | P.Jlim y = (P.g y : EReal)}) x)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_10_2_2 P Pr hPr hB
  set S := {y : E | P.Jlim y = (P.g y : EReal)} with hSdef
  -- characterisation of S
  have hJS : ∀ x, x ∈ S ↔ ∀ n, P.J n x = (P.g x : EReal) := by
    intro x
    constructor
    · intro h n
      exact le_antisymm ((J_le_Jlim P n x).trans (le_of_eq h)) (g_le_J P n x)
    · intro h
      exact le_antisymm (iSup_le fun n => le_of_eq (h n)) (h4 x)
  have hSmeas : MeasurableSet S := by
    have hJm : Measurable P.Jlim := Measurable.iSup fun n => J_measurable P n
    exact measurableSet_eq_fun hJm (measurable_coe_real_ereal.comp P.g_meas)
  have hdS : ∀ x, 0 ≤ ⨅ n, P.d n x ↔ x ∈ S := by
    intro x
    rw [le_iInf_iff, hJS]
    constructor
    · intro h n
      cases n with
      | zero => rfl
      | succ n => exact (mem_stopSet_succ P n x).2 (h (n + 1))
    · intro h n
      cases n with
      | zero => exact (mem_stopSet_succ P 0 x).1 (h 1)
      | succ n => exact (mem_stopSet_succ P n x).1 (h (n + 1))
  have hSeq : {x : E | 0 ≤ ⨅ n, P.d n x} = S := Set.ext hdS
  refine ⟨⟨fun x => ⨅ n, P.d n x, fun x => tendsto_atTop_iInf (d_anti P x), ?_, hSeq, ?_⟩, ?_⟩
  · rw [hSeq]; ext x
    rw [hJS, Set.mem_iInter]; rfl
  · rw [hSeq]
    refine ⟨hSmeas, fun x => ?_⟩
    unfold StationaryProblem.Tf
    by_cases hx : x ∈ S
    · rw [if_pos hx, ← h2 x]; exact hx.symm
    · rw [if_neg hx]
      unfold StationaryProblem.T
      refine (max_eq_right ?_).symm
      rw [← hdS] at hx
      push Not at hx
      obtain ⟨n, hn⟩ := iInf_lt_iff.1 hx
      have hlt : ¬ (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J (n - 1))
          ≤ (P.g x : EReal) := by
        rw [← sub_nonneg_iff]; exact not_le.2 hn
      push Not at hlt
      exact hlt.le.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (erealIntegral_mono _ fun y => J_le_Jlim P _ y) (beta_nonneg P)))
  · intro hT _hfin
    have hGfeq : ∀ x, P.Gf Pr S x = P.Vstar Pr x := by
      intro x
      rw [(h1 x).1]
      apply le_antisymm
      · rw [← (h1 x).2]
        unfold StationaryProblem.G StationaryProblem.Gf
        exact le_iSup₂_of_le (P.ruleTime S) (isStopTime_hitTime hSmeas) le_rfl
      · refine h5 _ ?_ (fun y => (g_le_T P _ y).trans (hT y)) x
        intro y
        exact (le_max_right _ _).trans (hT y)
    refine ⟨hGfeq, fun hBL => ?_⟩
    have hE : ∀ x, P.Gf Pr S x = P.EReward Pr (P.ruleTime S) x := by
      intro x
      exact (hBL.2 x _ (isStopTime_hitTime hSmeas) (_hfin x)).liminf_eq
    refine ⟨⟨isStopTime_hitTime hSmeas, _hfin, fun x => by rw [← hE, hGfeq]⟩, hE⟩
