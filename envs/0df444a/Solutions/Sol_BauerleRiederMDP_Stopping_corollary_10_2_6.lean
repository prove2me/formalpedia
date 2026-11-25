-- Prove2me | solution 1 for BauerleRiederMDP.Stopping.corollary_10_2_6
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-25T20:56:34.825574+00:00
-- url     : https://prove2.me/submissions/4f0981d2-4408-4b2b-9edc-0132d93fecba

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Stationary
import Definitions.Def_BauerleRiederMDP_Stopping_AssumptionBLim
import Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_2_2
import Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_1_3

open MeasureTheory Filter Topology
open MDPFinance.OptimalStopping

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace MDPS1026

variable {E : Type*} [MeasurableSpace E]

/-! ### Generic `EReal` / `erealIntegral` facts -/

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

lemma pos_toENNReal (e : EReal) : (e ⊔ 0).toENNReal = e.toENNReal := by
  rcases le_total e 0 with h | h
  · rw [sup_eq_right.2 h, EReal.toENNReal_of_nonpos h]; simp
  · rw [sup_eq_left.2 h]

lemma erealIntegral_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    erealIntegral μ v = ((∫⁻ x, (v x).toENNReal ∂μ : ENNReal) : EReal) +
      -((∫⁻ x, (-v x).toENNReal ∂μ : ENNReal) : EReal) := by
  simp only [erealIntegral, pos_toENNReal]

lemma erealIntegral_const_mul {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal)
    {a : ℝ} (ha : 0 < a) :
    erealIntegral μ (fun w => (a : EReal) * v w) = (a : EReal) * erealIntegral μ v := by
  have hpos : ∀ e : EReal, ((a : EReal) * e).toENNReal = ENNReal.ofReal a * e.toENNReal := by
    intro e; rw [EReal.toENNReal_mul (by exact_mod_cast ha.le), EReal.real_coe_toENNReal]
  rw [erealIntegral_eq, erealIntegral_eq]
  simp only [← mul_neg, hpos]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left ha.le,
    EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast ha.le) (EReal.coe_ne_top a), mul_neg]

lemma max_pow_le {b : ℝ} (h0 : 0 ≤ b) (h1 : b ≤ 1) (k j : ℕ) (r : ℝ) :
    max (b ^ (k + j) * r) 0 ≤ b ^ j * max r 0 := by
  calc max (b ^ (k + j) * r) 0 = b ^ (k + j) * max r 0 := by
        rw [mul_max_of_nonneg _ _ (pow_nonneg h0 _), mul_zero]
    _ ≤ b ^ j * max r 0 :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h0 h1 (Nat.le_add_left j k))
          (le_max_right _ _)

lemma ereal_toReal_eq (x : ENNReal) (hx : x ≠ ⊤) : (x : EReal) = ((x.toReal : ℝ) : EReal) := by
  lift x to NNReal using hx
  simp only [ENNReal.coe_toReal]
  exact EReal.coe_nnreal_eq_coe_real x

lemma pos_part (r : ℝ) : (((r : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal r := by
  rcases le_total r 0 with h | h
  · rw [sup_of_le_right (by exact_mod_cast h), ENNReal.ofReal_of_nonpos h]; simp
  · rw [sup_of_le_left (by exact_mod_cast h)]; simp

lemma neg_part (r : ℝ) : ((-(r : EReal)) ⊔ 0).toENNReal = ENNReal.ofReal (-r) := by
  rw [← EReal.coe_neg]; exact pos_part (-r)

lemma erealIntegral_coe {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℝ) :
    erealIntegral μ (fun a => (F a : EReal)) = ((∫⁻ a, ENNReal.ofReal (F a) ∂μ : ENNReal) : EReal)
      + -((∫⁻ a, ENNReal.ofReal (-F a) ∂μ : ENNReal) : EReal) := by
  simp only [erealIntegral, pos_part, neg_part]

lemma erealIntegral_of_integrable {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℝ)
    (hF : Integrable F μ) :
    erealIntegral μ (fun a => (F a : EReal)) = ((∫ a, F a ∂μ : ℝ) : EReal) := by
  have h2 : ∫⁻ a, ENNReal.ofReal (-F a) ∂μ ≠ ⊤ := hF.neg.lintegral_lt_top.ne
  rw [erealIntegral_coe, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hF,
    ereal_toReal_eq _ hF.lintegral_lt_top.ne, ereal_toReal_eq _ h2]
  rw [← EReal.coe_neg, ← EReal.coe_add, sub_eq_add_neg]

lemma ofReal_abs (r : ℝ) : ENNReal.ofReal |r| = ENNReal.ofReal r + ENNReal.ofReal (-r) := by
  rcases le_total r 0 with h | h
  · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (show -r ≤ 0 by linarith), add_zero]

lemma integrable_of_erealIntegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℝ)
    (hF : Measurable F) (h1 : erealIntegral μ (fun a => (F a : EReal)) ≠ ⊤)
    (h2 : erealIntegral μ (fun a => (F a : EReal)) ≠ ⊥) : Integrable F μ := by
  rw [erealIntegral_coe] at h1 h2
  set A := ∫⁻ a, ENNReal.ofReal (F a) ∂μ
  set B := ∫⁻ a, ENNReal.ofReal (-F a) ∂μ
  have hB : B ≠ ⊤ := by
    intro hB; apply h2; rw [hB]; simp
  have hA : A ≠ ⊤ := by
    intro hA; apply h1; rw [hA, ereal_toReal_eq B hB, ← EReal.coe_neg]; simp
  refine ⟨hF.aestronglyMeasurable, (hasFiniteIntegral_iff_norm F).2 ?_⟩
  simp only [Real.norm_eq_abs, ofReal_abs]
  rw [lintegral_add_left hF.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨hA.lt_top, hB.lt_top⟩

lemma erealIntegral_nonneg_coe {α : Type*} [MeasurableSpace α] (μ : Measure α) (F : α → ℝ)
    (hF : ∀ a, 0 ≤ F a) :
    erealIntegral μ (fun a => (F a : EReal)) = ((∫⁻ a, ENNReal.ofReal (F a) ∂μ : ENNReal) : EReal) := by
  rw [erealIntegral_coe]
  have : ∀ a, ENNReal.ofReal (-F a) = 0 := fun a => ENNReal.ofReal_of_nonpos (by linarith [hF a])
  simp [this]

/-! ### Basic facts about the stationary problem -/

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

lemma J_measurable (P : StationaryProblem E) (n : ℕ) : Measurable (P.J n) := by
  induction n with
  | zero => exact measurable_coe_real_ereal.comp P.g_meas
  | succ n ih =>
    change Measurable fun x => max (P.g x : EReal)
      ((P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J n))
    exact (measurable_coe_real_ereal.comp P.g_meas).max
      ((measurable_coe_real_ereal.comp P.c_meas).add
        ((measurable_erealIntegral P.QX P.QX_meas ih).const_mul _))

lemma Jlim_measurable (P : StationaryProblem E) : Measurable P.Jlim :=
  Measurable.iSup fun n => J_measurable P n

/-! ### Hitting times -/

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

lemma hitTime_mem {S : Set E} {w : ℕ → E} {m : ℕ} (h : hitTime S w = (m : ℕ∞)) : w m ∈ S := by
  obtain ⟨k, hk, hS⟩ := (hitTime_le_iff S w m).1 h.le
  have : hitTime S w ≤ (k : ℕ∞) := (hitTime_le_iff S w k).2 ⟨k, le_rfl, hS⟩
  rw [h] at this
  have : m ≤ k := by exact_mod_cast this
  have : k = m := by omega
  rwa [this] at hS

lemma meas_hitTime_le {S : Set E} (hS : MeasurableSet S) (k : ℕ) :
    MeasurableSet {w : ℕ → E | hitTime S w ≤ (k : ℕ∞)} :=
  Measurable.comap_le (measurable_pi_lambda _ fun i => measurable_pi_apply _) _
    (isStopTime_hitTime hS k)

lemma measurable_hitTime {S : Set E} (hS : MeasurableSet S) : Measurable (hitTime S) := by
  refine ENat.measurable_iff.2 fun n => ?_
  cases n with
  | zero =>
    have : hitTime S ⁻¹' {((0 : ℕ) : ℕ∞)} = {w | hitTime S w ≤ ((0 : ℕ) : ℕ∞)} := by
      ext w; simp
    rw [this]; exact meas_hitTime_le hS 0
  | succ n =>
    have : hitTime S ⁻¹' {((n + 1 : ℕ) : ℕ∞)} =
        {w | hitTime S w ≤ ((n + 1 : ℕ) : ℕ∞)} \ {w | hitTime S w ≤ (n : ℕ∞)} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_diff, Set.mem_setOf_eq]
      generalize hitTime S w = t
      induction t using ENat.recTopCoe with
      | top =>
        refine iff_of_false (fun h => ENat.top_ne_coe (n + 1) h) ?_
        simp only [top_le_iff, not_and, not_not]
        intro h; exact (ENat.coe_ne_top _ h).elim
      | coe t => norm_cast; omega
    rw [this]; exact (meas_hitTime_le hS _).diff (meas_hitTime_le hS _)

/-- `τ ∧ n` as a natural number. -/
noncomputable def tN (S : Set E) (n : ℕ) (w : ℕ → E) : ℕ := (min (hitTime S w) (n : ℕ∞)).toNat

lemma truncTime_eq (P : StationaryProblem E) (S : Set E) (n : ℕ) (w : ℕ → E) :
    truncTime (P.ruleTime S) n w = (tN S n w : ℕ∞) := by
  unfold tN truncTime StationaryProblem.ruleTime
  rw [ENat.coe_toNat]
  exact ne_top_of_le_ne_top (ENat.coe_ne_top n) (min_le_right _ _)

lemma tN_le (S : Set E) (n : ℕ) (w : ℕ → E) : tN S n w ≤ n := by
  unfold tN
  have := min_le_right (hitTime S w) (n : ℕ∞)
  generalize min (hitTime S w) (n : ℕ∞) = t at this
  induction t using ENat.recTopCoe with
  | top => simp
  | coe t => simpa using this

lemma tN_lt {S : Set E} {n : ℕ} {w : ℕ → E} (h : tN S n w < n) : hitTime S w = (tN S n w : ℕ∞) := by
  unfold tN at *
  rcases le_total (hitTime S w) (n : ℕ∞) with h' | h'
  · rw [min_eq_left h', ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top n) h')]
  · rw [min_eq_right h'] at h; simp at h

lemma tN_of_lt {S : Set E} {n : ℕ} {w : ℕ → E} (h : (n : ℕ∞) < hitTime S w) : tN S n w = n := by
  unfold tN; rw [min_eq_right h.le]; simp

lemma measurable_tN {S : Set E} (hS : MeasurableSet S) (n : ℕ) : Measurable (tN S n) :=
  (Measurable.of_discrete (f := fun t : ℕ∞ => (min t (n : ℕ∞)).toNat)).comp (measurable_hitTime hS)

lemma measurable_comp_nat {f : ℕ → (ℕ → E) → ℝ} (hf : ∀ k, Measurable (f k))
    {N : (ℕ → E) → ℕ} (hN : Measurable N) : Measurable fun w => f (N w) w := by
  have : Measurable (fun p : (ℕ → E) × ℕ => f p.2 p.1) :=
    measurable_from_prod_countable_left (fun y => hf y)
  exact this.comp (measurable_id.prodMk hN)

lemma reward_trunc (P : StationaryProblem E) (S : Set E) (n : ℕ) (w : ℕ → E) :
    P.reward (truncTime (P.ruleTime S) n) w =
      (∑ k ∈ Finset.range (tN S n w), P.beta ^ k * P.c (w k)) +
        P.beta ^ (tN S n w) * P.g (w (tN S n w)) := by
  unfold StationaryProblem.reward
  rw [truncTime_eq]

lemma isStopTime_trunc {S : Set E} (hS : MeasurableSet S) (n : ℕ) :
    IsStopTime (truncTime (hitTime S) n) := by
  intro k
  by_cases hk : n ≤ k
  · have : {w : ℕ → E | truncTime (hitTime S) n w ≤ (k : ℕ∞)} = Set.univ := by
      ext w; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (min_le_right _ _).trans (by exact_mod_cast hk)
    rw [this]; exact MeasurableSet.univ
  · have : {w : ℕ → E | truncTime (hitTime S) n w ≤ (k : ℕ∞)} = {w | hitTime S w ≤ (k : ℕ∞)} := by
      ext w; simp only [Set.mem_setOf_eq, truncTime, min_le_iff]
      constructor
      · rintro (h | h)
        · exact h
        · exfalso; exact hk (by exact_mod_cast h)
      · exact Or.inl
    rw [this]; exact isStopTime_hitTime hS k


/-! ### n-step kernels and the drift bound -/

noncomputable def kap (P : StationaryProblem E) : ProbabilityTheory.Kernel E E := ⟨P.QX, P.QX_meas⟩

noncomputable def Kp (P : StationaryProblem E) : ℕ → ProbabilityTheory.Kernel E E
  | 0 => ProbabilityTheory.Kernel.id
  | m + 1 => ProbabilityTheory.Kernel.comp (Kp P m) (kap P)

lemma cyl_marg (P : StationaryProblem E) (A : Set E) (hA : MeasurableSet A) :
    ∀ m (y : E), P.cyl (m + 1) (fun i => if i = m then A else Set.univ) y = Kp P (m + 1) y A := by
  intro m
  induction m with
  | zero =>
    intro y
    simp only [StationaryProblem.cyl, Kp, if_pos, setLIntegral_one]
    rw [ProbabilityTheory.Kernel.id_comp]; rfl
  | succ m ih =>
    intro y
    have h1 : P.cyl (m + 1 + 1) (fun i => if i = m + 1 then A else Set.univ) y =
        ∫⁻ z, P.cyl (m + 1) (fun i => if i = m then A else Set.univ) z ∂(P.QX y) := by
      simp only [StationaryProblem.cyl, Nat.add_right_cancel_iff]
      simp
    rw [h1]
    simp only [ih]
    rw [show Kp P (m + 1 + 1) = (Kp P (m + 1)).comp (kap P) from rfl,
      ProbabilityTheory.Kernel.comp_apply' _ _ _ hA]; rfl

lemma map_marg (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (m : ℕ) (x : E) : (Pr x).map (fun w => w m) = Kp P m x := by
  ext A hA
  rw [Measure.map_apply (measurable_pi_apply m) hA]
  cases m with
  | zero =>
    have : (fun w : ℕ → E => w 0) ⁻¹' A = {w | ∀ i ≤ 0, w i ∈ (fun _ : ℕ => A) i} := by
      ext w; simp
    rw [this, hPr.2 x 0 _ fun _ => hA]
    simp only [StationaryProblem.cyl, Kp, ProbabilityTheory.Kernel.id_apply,
      Measure.dirac_apply' _ hA]
    rfl
  | succ m =>
    have : (fun w : ℕ → E => w (m + 1)) ⁻¹' A =
        {w | ∀ i ≤ m + 1, w i ∈ (fun i : ℕ => if i = m + 1 then A else Set.univ) i} := by
      ext w; simp only [Set.mem_preimage, Set.mem_setOf_eq]
      constructor
      · intro h i _; split_ifs with hi
        · rw [hi]; exact h
        · trivial
      · intro h; simpa using h (m + 1) le_rfl
    rw [this, hPr.2 x (m + 1) _ fun i => by split_ifs; exacts [hA, MeasurableSet.univ]]
    simp only [show ((0 : ℕ) = m + 1) = False from by simp, if_false, Set.indicator_univ]
    simp only [Nat.add_right_cancel_iff]
    exact cyl_marg P A hA m x

lemma Kp_bound (P : StationaryProblem E) (B : P.BoundingFunction) :
    ∀ (m : ℕ) (y : E), ∫⁻ z, ENNReal.ofReal (B.b z) ∂(Kp P m y) ≤
      ENNReal.ofReal (max B.alpha 0 ^ m * B.b y) := by
  intro m
  induction m with
  | zero =>
    intro y
    simp only [Kp, ProbabilityTheory.Kernel.id_apply, pow_zero, one_mul]
    exact (lintegral_dirac' y B.b_meas.ennreal_ofReal).le
  | succ m ih =>
    intro y
    rw [show Kp P (m + 1) = (Kp P m).comp (kap P) from rfl,
      ProbabilityTheory.Kernel.lintegral_comp _ _ _ B.b_meas.ennreal_ofReal]
    calc ∫⁻ z, ∫⁻ u, ENNReal.ofReal (B.b u) ∂(Kp P m z) ∂(kap P y)
        ≤ ∫⁻ z, ENNReal.ofReal (max B.alpha 0 ^ m) * ENNReal.ofReal (B.b z) ∂(P.QX y) := by
          refine lintegral_mono fun z => (ih z).trans ?_
          rw [ENNReal.ofReal_mul (pow_nonneg (le_max_right _ _) _)]
      _ = ENNReal.ofReal (max B.alpha 0 ^ m) * ∫⁻ z, ENNReal.ofReal (B.b z) ∂(P.QX y) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (max B.alpha 0 ^ m) * ENNReal.ofReal (max B.alpha 0 * B.b y) := by
          gcongr
          refine (B.drift y).trans (ENNReal.ofReal_le_ofReal ?_)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (B.b_nonneg y)
      _ = ENNReal.ofReal (max B.alpha 0 ^ (m + 1) * B.b y) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg (le_max_right _ _) _), pow_succ, mul_assoc]

lemma lint_b (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (B : P.BoundingFunction) (m : ℕ) (x : E) :
    ∫⁻ w, ENNReal.ofReal (B.b (w m)) ∂(Pr x) ≤ ENNReal.ofReal (max B.alpha 0 ^ m * B.b x) := by
  calc ∫⁻ w, ENNReal.ofReal (B.b (w m)) ∂(Pr x)
      = ∫⁻ z, ENNReal.ofReal (B.b z) ∂((Pr x).map (fun w => w m)) :=
        (lintegral_map B.b_meas.ennreal_ofReal (measurable_pi_apply m)).symm
    _ = ∫⁻ z, ENNReal.ofReal (B.b z) ∂(Kp P m x) := by rw [map_marg P hPr m x]
    _ ≤ _ := Kp_bound P B m x


/-! ### The auxiliary finite-horizon problem -/

open Classical in
noncomputable def Qp (P : StationaryProblem E) (S : Set E) (hS : MeasurableSet S) (j : E → ℝ)
    (hj : Measurable j) (n : ℕ) : StoppingProblem E n where
  QX := fun _ => P.QX
  QX_prob := fun _ x => P.QX_prob x
  QX_meas := fun _ => P.QX_meas
  c := fun k x => P.beta ^ k * P.c x
  c_meas := fun _ => P.c_meas.const_mul _
  g := fun k x => if k < n then P.beta ^ k * (if x ∈ S then P.g x else P.g x - 1)
    else P.beta ^ n * j x
  g_meas := fun k => by
    by_cases hk : k < n
    · simp only [hk, if_true]
      exact (Measurable.ite hS P.g_meas (P.g_meas.sub_const 1)).const_mul _
    · simp only [hk, if_false]; exact hj.const_mul _

section Aux
variable (P : StationaryProblem E) (S : Set E) (hS : MeasurableSet S) (j : E → ℝ)
  (hj : Measurable j) (n : ℕ)

lemma Qp_cyl (m : ℕ) : ∀ (t : ℕ) (B : ℕ → Set E) (y : E), (Qp P S hS j hj n).cyl t m B y = P.cyl m B y := by
  induction m with
  | zero => intro t B y; rfl
  | succ m ih => intro t B y; simp only [StoppingProblem.cyl, StationaryProblem.cyl, ih]; rfl

lemma Qp_pathLaw {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr) :
    (Qp P S hS j hj n).IsPathLaw (fun _ => Pr) := by
  refine ⟨fun _ x => hPr.1 x, fun k x m B hB => ?_⟩
  rw [hPr.2 x m B hB]
  simp only [Qp_cyl]

/-- `M_n := Σ_{k<τ∧n} β^k c(X_k) + β^{τ∧n} j(X_{τ∧n})`. -/
noncomputable def Mf (w : ℕ → E) : ℝ :=
  (∑ k ∈ Finset.range (tN S n w), P.beta ^ k * P.c (w k)) + P.beta ^ (tN S n w) * j (w (tN S n w))

include hS hj in
lemma measurable_Mf : Measurable (Mf P S j n) := by
  have := measurable_comp_nat (E := E)
    (f := fun m w => (∑ k ∈ Finset.range m, P.beta ^ k * P.c (w k)) + P.beta ^ m * j (w m))
    (fun m => (Finset.measurable_sum _ fun k _ =>
      (P.c_meas.comp (measurable_pi_apply k)).const_mul _).add
      ((hj.comp (measurable_pi_apply m)).const_mul _)) (measurable_tN hS n)
  exact this

lemma min_sInf_le (A B : Set ℕ) (h : ∀ k ∈ B, k < n → k ∈ A) :
    min (sInf ((fun k : ℕ => (k : ℕ∞)) '' A)) (n : ℕ∞) ≤
      min (sInf ((fun k : ℕ => (k : ℕ∞)) '' B)) (n : ℕ∞) := by
  refine le_min (le_sInf ?_) (min_le_right _ _)
  rintro _ ⟨k, hk, rfl⟩
  by_cases hkn : k < n
  · exact (min_le_left _ _).trans (sInf_le ⟨k, h k hk hkn, rfl⟩)
  · exact (min_le_right _ _).trans (show ((n : ℕ) : ℕ∞) ≤ (k : ℕ∞) by exact_mod_cast not_lt.1 hkn)

lemma capped_eq (Sk : ℕ → Set E) (hSk : ∀ k < n, Sk k = S) (w : ℕ → E) :
    hitTimeCapped Sk n w = truncTime (hitTime S) n w := by
  unfold hitTimeCapped truncTime hitTime
  refine le_antisymm (min_sInf_le n _ _ fun k hk hkn => ?_) (min_sInf_le n _ _ fun k hk hkn => ?_)
  · show w k ∈ Sk k; rw [hSk k hkn]; exact hk
  · have : w k ∈ Sk k := hk
    rwa [hSk k hkn] at this

variable {P S hS j hj n}

lemma T_step (hjS : ∀ x ∈ S, j x = P.g x)
    (hjN : ∀ x ∉ S, (j x : EReal) = (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)))
    (hS2 : ∀ x ∈ S, (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) ≤ P.g x)
    (hjg : ∀ x, P.g x ≤ j x) (k : ℕ) (hk : k < n) (x : E) :
    (Qp P S hS j hj n).T k (fun y => ((P.beta ^ (k + 1) * j y : ℝ) : EReal)) x =
      ((P.beta ^ k * j x : ℝ) : EReal) := by
  have hb := P.beta_mem.1
  unfold StoppingProblem.T
  simp only [Qp, hk, if_true]
  set I := erealIntegral (P.QX x) (fun y => (j y : EReal))
  have hI : erealIntegral (P.QX x) (fun y => ((P.beta ^ (k + 1) * j y : ℝ) : EReal)) =
      ((P.beta ^ (k + 1) : ℝ) : EReal) * I := by
    simp only [EReal.coe_mul]
    exact erealIntegral_const_mul _ _ (pow_pos hb _)
  have hsplit : ((P.beta ^ k * P.c x : ℝ) : EReal) + ((P.beta ^ (k + 1) : ℝ) : EReal) * I =
      ((P.beta ^ k : ℝ) : EReal) * ((P.c x : EReal) + (P.beta : EReal) * I) := by
    rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast (pow_pos hb k).le)
      (EReal.coe_ne_top _), ← mul_assoc, pow_succ, EReal.coe_mul, EReal.coe_mul]
  rw [hI, hsplit]
  have hk0 : (0 : EReal) ≤ ((P.beta ^ k : ℝ) : EReal) := by exact_mod_cast (pow_pos hb k).le
  by_cases hx : x ∈ S
  · simp only [hx, if_true]
    rw [max_eq_left, hjS x hx]
    calc ((P.beta ^ k : ℝ) : EReal) * ((P.c x : EReal) + (P.beta : EReal) * I)
        ≤ ((P.beta ^ k : ℝ) : EReal) * (P.g x : EReal) := mul_le_mul_of_nonneg_left (hS2 x hx) hk0
      _ = _ := by rw [← EReal.coe_mul]
  · simp only [hx, if_false]
    rw [← hjN x hx, ← EReal.coe_mul, max_eq_right]
    exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (by linarith [hjg x])
      (pow_pos hb k).le)


include hS hj in
/-- Key identity, obtained from Theorem 10.1.3 applied to `Qp`: `𝔼_x[M_n] = j(x)`. -/
lemma EM {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (hjS : ∀ x ∈ S, j x = P.g x)
    (hjN : ∀ x ∉ S, (j x : EReal) = (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)))
    (hS2 : ∀ x ∈ S, (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) ≤ P.g x)
    (hjg : ∀ x, P.g x ≤ j x)
    (hjint : ∀ x m, ∫⁻ w, ENNReal.ofReal (max (j (w m)) 0) ∂(Pr x) ≠ ⊤) (x : E) :
    erealIntegral (Pr x) (fun w => (Mf P S j n w : EReal)) = j x := by
  have h0b := P.beta_mem.1.le
  have h1b := P.beta_mem.2
  have hQ := Qp_pathLaw P S hS j hj n hPr
  have hBN : (Qp P S hS j hj n).AssumptionBN (fun _ => Pr) := by
    intro t _ x
    obtain ⟨C1, hC1, hb1⟩ := hB.1 x
    refine ⟨C1 + ∑ i ∈ Finset.range (n + 1), ∫⁻ w, ENNReal.ofReal (max (j (w i)) 0) ∂(Pr x),
      ENNReal.add_lt_top.2 ⟨hC1, ENNReal.sum_lt_top.2 fun i _ => (hjint x i).lt_top⟩,
      fun τ hτ hle => ?_⟩
    have hfin : Pr x {w | τ w = ⊤} = 0 := by
      have : {w | τ w = ⊤} = ∅ := by
        ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h; have := hle w; rw [h] at this; exact ENat.coe_ne_top _ (top_le_iff.1 this)
      rw [this, measure_empty]
    have hmeasj : ∀ i, Measurable fun w : ℕ → E => ENNReal.ofReal (max (j (w i)) 0) :=
      fun i => ((hj.comp (measurable_pi_apply i)).max measurable_const).ennreal_ofReal
    calc _ ≤ ∫⁻ w, (ENNReal.ofReal ((∑ k ∈ Finset.range ((τ w).toNat),
            P.beta ^ k * max (P.c (w k)) 0)
          + P.beta ^ (τ w).toNat * max (P.g (w (τ w).toNat)) 0) +
          ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (max (j (w i)) 0)) ∂(Pr x) := by
          refine lintegral_mono fun w => ?_
          have hm : (τ w).toNat ≤ n := by
            have h1 := hle w
            have h2 : τ w ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h1
            rw [← ENat.coe_toNat h2] at h1
            have : (τ w).toNat ≤ n - t := by exact_mod_cast h1
            omega
          set m := (τ w).toNat
          have hs : (∑ k ∈ Finset.range m, max ((Qp P S hS j hj n).c (t + k) (w k)) 0) ≤
              ∑ k ∈ Finset.range m, P.beta ^ k * max (P.c (w k)) 0 :=
            Finset.sum_le_sum fun k _ => max_pow_le h0b h1b t k _
          have hg : max ((Qp P S hS j hj n).g (t + m) (w m)) 0 ≤
              P.beta ^ m * max (P.g (w m)) 0 + max (j (w m)) 0 := by
            have hgm : 0 ≤ P.beta ^ m * max (P.g (w m)) 0 :=
              mul_nonneg (pow_nonneg h0b _) (le_max_right _ _)
            simp only [Qp]
            split_ifs with h3 h4
            · linarith [max_pow_le h0b h1b t m (P.g (w m)), le_max_right (j (w m)) 0]
            · have := max_pow_le h0b h1b t m (P.g (w m) - 1)
              have : P.beta ^ m * max (P.g (w m) - 1) 0 ≤ P.beta ^ m * max (P.g (w m)) 0 :=
                mul_le_mul_of_nonneg_left (max_le_max (by linarith) le_rfl) (pow_nonneg h0b _)
              linarith [le_max_right (j (w m)) 0]
            · have := max_pow_le h0b h1b n 0 (j (w m))
              simp only [add_zero, pow_zero, one_mul] at this
              linarith
          calc ENNReal.ofReal ((∑ k ∈ Finset.range m, max ((Qp P S hS j hj n).c (t + k) (w k)) 0)
                + max ((Qp P S hS j hj n).g (t + m) (w m)) 0)
              ≤ ENNReal.ofReal (((∑ k ∈ Finset.range m, P.beta ^ k * max (P.c (w k)) 0)
                + P.beta ^ m * max (P.g (w m)) 0) + max (j (w m)) 0) :=
                ENNReal.ofReal_le_ofReal (by linarith)
            _ ≤ _ + ENNReal.ofReal (max (j (w m)) 0) := ENNReal.ofReal_add_le
            _ ≤ _ := add_le_add le_rfl (Finset.single_le_sum
                (f := fun i => ENNReal.ofReal (max (j (w i)) 0)) (fun i _ => bot_le)
                (Finset.mem_range.2 (show m < n + 1 by omega)))
      _ = _ := by
          rw [lintegral_add_right _ (Finset.measurable_sum _ fun i _ => hmeasj i),
            lintegral_finset_sum _ fun i _ => hmeasj i]
      _ ≤ _ := add_le_add (hb1 τ hτ hfin) le_rfl
  obtain ⟨⟨hVN, hVs⟩, -, -, hE⟩ := theorem_10_1_3 (Qp P S hS j hj n) (fun _ => Pr) hQ hBN
  have hV : ∀ i, i ≤ n → ∀ y, (Qp P S hS j hj n).Vn (fun _ => Pr) (n - i) y =
      ((P.beta ^ (n - i) * j y : ℝ) : EReal) := by
    intro i
    induction i with
    | zero => intro _ y; rw [Nat.sub_zero, hVN y]; simp [Qp]
    | succ i ih =>
      intro hi y
      have hk : n - (i + 1) < n := by omega
      rw [hVs _ hk y]
      have h' : n - (i + 1) + 1 = n - i := by omega
      have e : (Qp P S hS j hj n).Vn (fun _ => Pr) (n - (i + 1) + 1) =
          fun y => ((P.beta ^ (n - (i + 1) + 1) * j y : ℝ) : EReal) := by
        funext y; rw [h']; exact ih (by omega) y
      rw [e]; exact T_step hjS hjN hS2 hjg _ hk y
  have hSk : ∀ k < n, {y | (Qp P S hS j hj n).Vn (fun _ => Pr) k y =
      (((Qp P S hS j hj n).g k y : ℝ) : EReal)} = S := by
    intro k hk; ext y
    have := hV (n - k) (by omega) y
    rw [show n - (n - k) = k by omega] at this
    have hb := pow_pos P.beta_mem.1 k
    rw [Set.mem_setOf_eq, this]
    simp only [Qp, hk, if_true, EReal.coe_eq_coe_iff]
    by_cases hy : y ∈ S
    · simp only [hy, if_true, iff_true]; rw [hjS y hy]
    · simp only [hy, if_false, iff_false]; intro h
      have := mul_left_cancel₀ hb.ne' h; linarith [hjg y]
  have hE' := hE x
  have h0 := hV n le_rfl x
  rw [Nat.sub_self, pow_zero, one_mul] at h0
  rw [h0] at hE'
  rw [← hE']
  unfold StoppingProblem.EReward
  congr 1; funext w
  congr 1
  unfold StoppingProblem.rewardFrom
  rw [capped_eq S n _ hSk w,
    show truncTime (hitTime S) n w = (tN S n w : ℕ∞) from truncTime_eq P S n w]
  simp only [Qp, zero_add, Mf]
  split_ifs with h3 h4
  · rw [hjS _ h4]
  · exact absurd (hitTime_mem (tN_lt h3)) h4
  · have : tN S n w = n := le_antisymm (tN_le S n w) (not_lt.1 h3)
    rw [this]

end Aux

/-- `β^n D_n` is the gap between `M_n` and `R_{τ∧n}`. -/
noncomputable def Dn (P : StationaryProblem E) (S : Set E) (j : E → ℝ) (n : ℕ) (w : ℕ → E) : ℝ :=
  if (n : ℕ∞) < hitTime S w then j (w n) - P.g (w n) else 0

lemma ER_eq (P : StationaryProblem E) (S : Set E) (hS : MeasurableSet S) (j : E → ℝ)
    (hj : Measurable j) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (hjS : ∀ x ∈ S, j x = P.g x)
    (hjN : ∀ x ∉ S, (j x : EReal) = (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)))
    (hS2 : ∀ x ∈ S, (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) ≤ P.g x)
    (hjg : ∀ x, P.g x ≤ j x)
    (hjint : ∀ x m, ∫⁻ w, ENNReal.ofReal (max (j (w m)) 0) ∂(Pr x) ≠ ⊤)
    (hD : ∀ x m, ∫⁻ w, ENNReal.ofReal (j (w m) - P.g (w m)) ∂(Pr x) ≠ ⊤) (n : ℕ) (x : E) :
    Integrable (Dn P S j n) (Pr x) ∧ 0 ≤ ∫ w, Dn P S j n w ∂(Pr x) ∧
      P.EReward Pr (truncTime (P.ruleTime S) n) x =
        ((j x - P.beta ^ n * ∫ w, Dn P S j n w ∂(Pr x) : ℝ) : EReal) := by
  have hM := EM (P := P) (hS := hS) (hj := hj) (n := n) hPr hB hjS hjN hS2 hjg hjint x
  have hMm := measurable_Mf P S hS j hj n
  have hMint : Integrable (Mf P S j n) (Pr x) :=
    integrable_of_erealIntegral _ _ hMm (by rw [hM]; exact EReal.coe_ne_top _)
      (by rw [hM]; exact EReal.coe_ne_bot _)
  have hMval : ∫ w, Mf P S j n w ∂(Pr x) = j x := by
    have := erealIntegral_of_integrable _ _ hMint
    rw [hM] at this; exact_mod_cast this.symm
  have hset : MeasurableSet {w : ℕ → E | (n : ℕ∞) < hitTime S w} := by
    have := (meas_hitTime_le hS n).compl
    simpa only [Set.compl_setOf, not_le] using this
  have hgn : Measurable fun w : ℕ → E => j (w n) - P.g (w n) :=
    (hj.comp (measurable_pi_apply n)).sub (P.g_meas.comp (measurable_pi_apply n))
  have hDm : Measurable (Dn P S j n) := by
    unfold Dn
    exact Measurable.ite hset hgn measurable_const
  have hD0 : ∀ w, 0 ≤ Dn P S j n w := fun w => by
    unfold Dn; split_ifs
    · linarith [hjg (w n)]
    · exact le_rfl
  have hDle : ∀ w, Dn P S j n w ≤ j (w n) - P.g (w n) := fun w => by
    unfold Dn; split_ifs
    · exact le_rfl
    · linarith [hjg (w n)]
  have hDbint : Integrable (fun w => j (w n) - P.g (w n)) (Pr x) := by
    refine ⟨hgn.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w => by
      show (0 : ℝ) ≤ j (w n) - P.g (w n); linarith [hjg (w n)])]
    exact (hD x n).lt_top
  have hDint : Integrable (Dn P S j n) (Pr x) :=
    hDbint.mono' hDm.aestronglyMeasurable (Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 w)]; exact hDle w)
  refine ⟨hDint, integral_nonneg hD0, ?_⟩
  have hR : ∀ w, P.reward (truncTime (P.ruleTime S) n) w =
      Mf P S j n w - P.beta ^ n * Dn P S j n w := by
    intro w
    rw [reward_trunc]
    unfold Mf Dn
    split_ifs with h
    · rw [tN_of_lt h]; ring
    · push Not at h
      have ht : hitTime S w = (tN S n w : ℕ∞) := by
        unfold tN; rw [min_eq_left h, ENat.coe_toNat (ne_top_of_le_ne_top (ENat.coe_ne_top n) h)]
      rw [hjS _ (hitTime_mem ht)]; ring
  unfold StationaryProblem.EReward
  simp only [hR]
  rw [erealIntegral_of_integrable _ (fun w => Mf P S j n w - P.beta ^ n * Dn P S j n w)
      (hMint.sub (hDint.const_mul _)),
    integral_sub hMint (hDint.const_mul _), integral_const_mul, hMval]

lemma Gf_eq_of (P : StationaryProblem E) (Pr : E → Measure (ℕ → E)) (S : Set E) (j : E → ℝ)
    (x : E) (e : ℕ → ℝ)
    (hER : ∀ n, P.EReward Pr (truncTime (P.ruleTime S) n) x = ((j x - e n : ℝ) : EReal))
    (he : Tendsto e atTop (𝓝 0)) : P.Gf Pr S x = (j x : EReal) := by
  unfold StationaryProblem.Gf
  have h1 : Tendsto (fun n => j x - e n) atTop (𝓝 (j x)) := by
    simpa using (tendsto_const_nhds (x := j x)).sub he
  have : Tendsto (fun n => ((j x - e n : ℝ) : EReal)) atTop (𝓝 (j x : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp h1
  rw [show (fun n => P.EReward Pr (truncTime (P.ruleTime S) n) x) =
    fun n => ((j x - e n : ℝ) : EReal) from funext hER]
  exact this.liminf_eq

lemma opt_of (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hSm : MeasurableSet S)
    (hfin : ∀ x, Pr x {w | P.ruleTime S w = ⊤} = 0)
    (hBL : BauerleRiederMDP.Stopping.AssumptionBLim P Pr)
    (hG : ∀ x, P.Gf Pr S x = P.Jlim x) : P.IsOptimal Pr (P.ruleTime S) := by
  obtain ⟨h1, -, -⟩ := theorem_10_2_2 P Pr hPr hB
  refine ⟨isStopTime_hitTime hSm, hfin, fun x => ?_⟩
  rw [(h1 x).1, ← hG x]
  unfold StationaryProblem.Gf
  exact ((hBL.2 x _ (isStopTime_hitTime hSm) (hfin x)).liminf_eq).symm

lemma J_le_K (P : StationaryProblem E) (B : P.BoundingFunction) (hBa : P.beta * B.alpha < 1) :
    ∀ n x, P.J n x ≤ ((B.cr / (1 - P.beta * max B.alpha 0) * B.b x : ℝ) : EReal) := by
  set a' := max B.alpha 0 with ha'
  set K := B.cr / (1 - P.beta * a') with hK
  have hb0 := P.beta_mem.1
  have hq0 : 0 ≤ P.beta * a' := mul_nonneg hb0.le (le_max_right _ _)
  have hq1 : P.beta * a' < 1 := by
    rw [ha', mul_max_of_nonneg _ _ hb0.le, mul_zero]; exact max_lt hBa one_pos
  have hpos : 0 < 1 - P.beta * a' := by linarith
  have hKeq : B.cr + P.beta * a' * K = K := by rw [hK]; field_simp; ring
  have hK0 : 0 ≤ K := div_nonneg B.cr_nonneg hpos.le
  have hcrK : B.cr ≤ K := by nlinarith [mul_nonneg hq0 hK0]
  have hbase : ∀ x, (P.g x : EReal) ≤ ((K * B.b x : ℝ) : EReal) := fun x =>
    EReal.coe_le_coe_iff.2 ((le_abs_self _).trans ((B.g_le x).trans
      (mul_le_mul_of_nonneg_right hcrK (B.b_nonneg x))))
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x
    change max (P.g x : EReal) ((P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (P.J n)) ≤ _
    refine max_le (hbase x) ?_
    have hI : erealIntegral (P.QX x) (P.J n) ≤ ((K * a' * B.b x : ℝ) : EReal) := by
      refine (erealIntegral_mono _ ih).trans ?_
      rw [erealIntegral_nonneg_coe _ _ fun y => mul_nonneg hK0 (B.b_nonneg y)]
      have : ∫⁻ y, ENNReal.ofReal (K * B.b y) ∂(P.QX x) ≤ ENNReal.ofReal (K * a' * B.b x) := by
        calc ∫⁻ y, ENNReal.ofReal (K * B.b y) ∂(P.QX x)
            = ∫⁻ y, ENNReal.ofReal K * ENNReal.ofReal (B.b y) ∂(P.QX x) := by
              congr 1; funext y; rw [ENNReal.ofReal_mul hK0]
          _ = ENNReal.ofReal K * ∫⁻ y, ENNReal.ofReal (B.b y) ∂(P.QX x) :=
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
          _ ≤ ENNReal.ofReal K * ENNReal.ofReal (a' * B.b x) := by
              gcongr
              exact (B.drift x).trans (ENNReal.ofReal_le_ofReal
                (mul_le_mul_of_nonneg_right (le_max_left _ _) (B.b_nonneg x)))
          _ = _ := by rw [← ENNReal.ofReal_mul hK0, mul_assoc]
      calc ((∫⁻ y, ENNReal.ofReal (K * B.b y) ∂(P.QX x) : ENNReal) : EReal)
          ≤ ((ENNReal.ofReal (K * a' * B.b x) : ENNReal) : EReal) :=
            EReal.coe_ennreal_le_coe_ennreal_iff.2 this
        _ = _ := by
            rw [EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg (mul_nonneg hK0
              (le_max_right _ _)) (B.b_nonneg x))]
    calc (P.c x : EReal) + (P.beta : EReal) * erealIntegral (P.QX x) (P.J n)
        ≤ (P.c x : EReal) + (P.beta : EReal) * ((K * a' * B.b x : ℝ) : EReal) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (beta_nonneg P))
      _ = ((P.c x + P.beta * (K * a' * B.b x) : ℝ) : EReal) := by
          simp only [EReal.coe_add, EReal.coe_mul]
      _ ≤ _ := by
          refine EReal.coe_le_coe_iff.2 ?_
          have hc := (le_abs_self (P.c x)).trans (B.c_le x)
          have hb := B.b_nonneg x
          have : K * B.b x = B.cr * B.b x + P.beta * a' * K * B.b x := by
            have := congrArg (· * B.b x) hKeq; linarith
          nlinarith

lemma facts (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hS : P.IsMaximizer S P.Jlim) (j : E → ℝ)
    (hJj : ∀ x, P.Jlim x = (j x : EReal)) :
    (∀ x ∈ S, j x = P.g x) ∧
    (∀ x ∉ S, (j x : EReal) = (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal))) ∧
    (∀ x ∈ S, (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) ≤ P.g x) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_10_2_2 P Pr hPr hB
  have hfix : ∀ x, P.Tf S P.Jlim x = P.Jlim x := fun x => (hS.2 x).trans (h2 x).symm
  have hJfun : P.Jlim = fun y => (j y : EReal) := funext hJj
  have hjS : ∀ x ∈ S, j x = P.g x := fun x hx => by
    have := hfix x; unfold StationaryProblem.Tf at this
    rw [if_pos hx, hJj] at this; exact_mod_cast this.symm
  refine ⟨hjS, fun x hx => ?_, fun x hx => ?_⟩
  · have := hfix x; unfold StationaryProblem.Tf at this
    rw [if_neg hx, hJfun] at this; exact this.symm
  · have e := h2 x; unfold StationaryProblem.T at e
    rw [← hJfun]
    calc _ ≤ max (P.g x : EReal) _ := le_max_right _ _
      _ = P.Jlim x := e.symm
      _ = P.g x := by rw [hJj, hjS x hx]

lemma setupA (P : StationaryProblem E) (B : P.BoundingFunction) (hBa : P.beta * B.alpha < 1) :
    ∃ j : E → ℝ, Measurable j ∧ (∀ x, P.Jlim x = (j x : EReal)) ∧ (∀ x, P.g x ≤ j x) ∧
      ∀ x, j x ≤ B.cr / (1 - P.beta * max B.alpha 0) * B.b x := by
  have hle : ∀ x, P.Jlim x ≤ ((B.cr / (1 - P.beta * max B.alpha 0) * B.b x : ℝ) : EReal) :=
    fun x => iSup_le fun n => J_le_K P B hBa n x
  have hge : ∀ x, (P.g x : EReal) ≤ P.Jlim x := fun x => (g_le_J P 0 x).trans (le_iSup (fun n => P.J n x) 0)
  have hJj : ∀ x, P.Jlim x = ((P.Jlim x).toReal : EReal) := fun x =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hle x))
      (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hge x))).symm
  refine ⟨fun x => (P.Jlim x).toReal, (Jlim_measurable P).ereal_toReal, hJj, fun x => ?_, fun x => ?_⟩
  · have := hge x; rw [hJj x] at this; exact_mod_cast this
  · have := hle x; rw [hJj x] at this; exact_mod_cast this

lemma partA1 (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hS : P.IsMaximizer S P.Jlim)
    (B : P.BoundingFunction) (hBa : P.beta * B.alpha < 1) :
    ∀ x, P.Gf Pr S x = P.Jlim x := by
  obtain ⟨j, hjm, hJj, hjg, hjb⟩ := setupA P B hBa
  obtain ⟨hjS, hjN, hS2⟩ := facts P hPr hB hS j hJj
  set a' := max B.alpha 0 with ha'
  set K := B.cr / (1 - P.beta * a') with hK
  have hb0 := P.beta_mem.1
  have hq0 : 0 ≤ P.beta * a' := mul_nonneg hb0.le (le_max_right _ _)
  have hq1 : P.beta * a' < 1 := by
    rw [ha', mul_max_of_nonneg _ _ hb0.le, mul_zero]; exact max_lt hBa one_pos
  have hK0 : 0 ≤ K := div_nonneg B.cr_nonneg (by linarith)
  have hKc : 0 ≤ K + B.cr := add_nonneg hK0 B.cr_nonneg
  have hlb : ∀ (L : ℝ), 0 ≤ L → ∀ (f : (ℕ → E) → ℝ) x m, (∀ w, f w ≤ L * B.b (w m)) →
      ∫⁻ w, ENNReal.ofReal (f w) ∂(Pr x) ≤ ENNReal.ofReal (L * (a' ^ m * B.b x)) := by
    intro L hL f x m hf
    calc ∫⁻ w, ENNReal.ofReal (f w) ∂(Pr x)
        ≤ ∫⁻ w, ENNReal.ofReal L * ENNReal.ofReal (B.b (w m)) ∂(Pr x) :=
          lintegral_mono fun w => by
            rw [← ENNReal.ofReal_mul hL]; exact ENNReal.ofReal_le_ofReal (hf w)
      _ = ENNReal.ofReal L * ∫⁻ w, ENNReal.ofReal (B.b (w m)) ∂(Pr x) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal L * ENNReal.ofReal (a' ^ m * B.b x) := by
          gcongr; exact lint_b P hPr B m x
      _ = _ := (ENNReal.ofReal_mul hL).symm
  have hjint : ∀ x m, ∫⁻ w, ENNReal.ofReal (max (j (w m)) 0) ∂(Pr x) ≠ ⊤ := fun x m =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hlb K hK0 _ x m fun w => max_le (hjb _) (mul_nonneg hK0 (B.b_nonneg _)))
  have hDb : ∀ y, j y - P.g y ≤ (K + B.cr) * B.b y := fun y => by
    have := neg_le_abs (P.g y); have := B.g_le y; have := hjb y; nlinarith
  have hD : ∀ x m, ∫⁻ w, ENNReal.ofReal (j (w m) - P.g (w m)) ∂(Pr x) ≠ ⊤ := fun x m =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlb _ hKc _ x m fun w => hDb _)
  intro x
  haveI := hPr.1 x
  rw [hJj]
  have hER := fun n => ER_eq P S hS.1 j hjm hPr hB hjS hjN hS2 hjg hjint hD n x
  refine Gf_eq_of P Pr S j x (fun n => P.beta ^ n * ∫ w, Dn P S j n w ∂(Pr x))
    (fun n => (hER n).2.2) ?_
  have hT0 := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul ((K + B.cr) * B.b x)
  rw [mul_zero] at hT0
  refine squeeze_zero (fun n => mul_nonneg (pow_nonneg hb0.le n) (hER n).2.1) (fun n => ?_) hT0
  have hDn : ∀ w, Dn P S j n w ≤ (K + B.cr) * B.b (w n) := fun w => by
    unfold Dn; split_ifs
    · exact hDb _
    · exact mul_nonneg hKc (B.b_nonneg _)
  have hD0 : ∀ w, 0 ≤ Dn P S j n w := fun w => by
    unfold Dn; split_ifs
    · linarith [hjg (w n)]
    · exact le_rfl
  have hint : ∫ w, Dn P S j n w ∂(Pr x) ≤ (K + B.cr) * (a' ^ n * B.b x) := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w =>
      show (0 : (ℕ → E) → ℝ) w ≤ Dn P S j n w from hD0 w) (hER n).1.aestronglyMeasurable]
    have := hlb _ hKc _ x n hDn
    calc _ ≤ (ENNReal.ofReal ((K + B.cr) * (a' ^ n * B.b x))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top this
      _ = _ := ENNReal.toReal_ofReal (mul_nonneg hKc
          (mul_nonneg (pow_nonneg (le_max_right _ _) _) (B.b_nonneg x)))
  calc P.beta ^ n * ∫ w, Dn P S j n w ∂(Pr x)
      ≤ P.beta ^ n * ((K + B.cr) * (a' ^ n * B.b x)) :=
        mul_le_mul_of_nonneg_left hint (pow_nonneg hb0.le n)
    _ = (K + B.cr) * B.b x * (P.beta * a') ^ n := by rw [mul_pow]; ring

lemma partA2 (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hS : P.IsMaximizer S P.Jlim)
    (B : P.BoundingFunction) (hBa : P.beta * B.alpha < 1)
    (hfin : ∀ x, Pr x {w | P.ruleTime S w = ⊤} = 0) : P.IsOptimal Pr (P.ruleTime S) := by
  obtain ⟨h1, -, -⟩ := theorem_10_2_2 P Pr hPr hB
  have hG := partA1 P hPr hB hS B hBa
  refine ⟨isStopTime_hitTime hS.1, hfin, fun x => ?_⟩
  haveI := hPr.1 x
  rw [(h1 x).1, ← hG x]
  set a' := max B.alpha 0 with ha'
  have hb0 := P.beta_mem.1
  have hq0 : 0 ≤ P.beta * a' := mul_nonneg hb0.le (le_max_right _ _)
  have hq1 : P.beta * a' < 1 := by
    rw [ha', mul_max_of_nonneg _ _ hb0.le, mul_zero]; exact max_lt hBa one_pos
  have hkm : ∀ k, Measurable fun w : ℕ → E => ENNReal.ofReal (P.beta ^ k * B.b (w k)) :=
    fun k => ((B.b_meas.comp (measurable_pi_apply k)).const_mul _).ennreal_ofReal
  set Φ : (ℕ → E) → ENNReal := fun w => ∑' k, ENNReal.ofReal (P.beta ^ k * B.b (w k)) with hΦ
  have hΦm : Measurable Φ := Measurable.ennreal_tsum hkm
  have hΦint : ∫⁻ w, Φ w ∂(Pr x) ≠ ⊤ := by
    rw [hΦ, lintegral_tsum fun k => (hkm k).aemeasurable]
    refine ne_top_of_le_ne_top (b := ∑' k, ENNReal.ofReal (B.b x) * ENNReal.ofReal (P.beta * a') ^ k)
      ?_ (ENNReal.tsum_le_tsum fun k => ?_)
    · rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.2 ?_)
      rw [ne_eq, tsub_eq_zero_iff_le, not_le]; exact ENNReal.ofReal_lt_one.2 hq1
    · calc ∫⁻ w, ENNReal.ofReal (P.beta ^ k * B.b (w k)) ∂(Pr x)
          = ∫⁻ w, ENNReal.ofReal (P.beta ^ k) * ENNReal.ofReal (B.b (w k)) ∂(Pr x) := by
            congr 1; funext w; rw [ENNReal.ofReal_mul (pow_nonneg hb0.le _)]
        _ = ENNReal.ofReal (P.beta ^ k) * ∫⁻ w, ENNReal.ofReal (B.b (w k)) ∂(Pr x) :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal (P.beta ^ k) * ENNReal.ofReal (a' ^ k * B.b x) := by
            gcongr; exact lint_b P hPr B k x
        _ = _ := by
            rw [← ENNReal.ofReal_mul (pow_nonneg hb0.le _), ← ENNReal.ofReal_pow hq0,
              ← ENNReal.ofReal_mul (B.b_nonneg x)]
            congr 1; rw [mul_pow]; ring
  have hpart : ∀ w, Φ w ≠ ⊤ → ∀ m, (∑ k ∈ Finset.range m, P.beta ^ k * B.b (w k)) ≤ (Φ w).toReal ∧
      P.beta ^ m * B.b (w m) ≤ (Φ w).toReal := by
    intro w hw m
    have hnn : ∀ k, 0 ≤ P.beta ^ k * B.b (w k) := fun k =>
      mul_nonneg (pow_nonneg hb0.le _) (B.b_nonneg _)
    constructor
    · rw [← ENNReal.ofReal_le_iff_le_toReal hw, ENNReal.ofReal_sum_of_nonneg fun k _ => hnn k]
      exact ENNReal.sum_le_tsum _
    · rw [← ENNReal.ofReal_le_iff_le_toReal hw]
      exact ENNReal.le_tsum (f := fun k => ENNReal.ofReal (P.beta ^ k * B.b (w k))) m
  have hbd : ∀ (τ' : (ℕ → E) → ℕ∞) w, Φ w ≠ ⊤ → |P.reward τ' w| ≤ 2 * B.cr * (Φ w).toReal := by
    intro τ' w hw
    have hΦ0 : 0 ≤ (Φ w).toReal := ENNReal.toReal_nonneg
    unfold StationaryProblem.reward
    generalize τ' w = t
    induction t using ENat.recTopCoe with
    | top =>
      show |(0 : ℝ)| ≤ _
      rw [abs_zero]; exact mul_nonneg (mul_nonneg zero_le_two B.cr_nonneg) hΦ0
    | coe m =>
      show |(∑ k ∈ Finset.range m, P.beta ^ k * P.c (w k)) + P.beta ^ m * P.g (w m)| ≤ _
      obtain ⟨hs1, hs2⟩ := hpart w hw m
      have e1 : |∑ k ∈ Finset.range m, P.beta ^ k * P.c (w k)| ≤
          B.cr * ∑ k ∈ Finset.range m, P.beta ^ k * B.b (w k) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, abs_of_nonneg (pow_nonneg hb0.le _)]
        calc _ ≤ P.beta ^ k * (B.cr * B.b (w k)) :=
              mul_le_mul_of_nonneg_left (B.c_le _) (pow_nonneg hb0.le _)
          _ = _ := by ring
      have e2 : |P.beta ^ m * P.g (w m)| ≤ B.cr * (P.beta ^ m * B.b (w m)) := by
        rw [abs_mul, abs_of_nonneg (pow_nonneg hb0.le _)]
        calc _ ≤ P.beta ^ m * (B.cr * B.b (w m)) :=
              mul_le_mul_of_nonneg_left (B.g_le _) (pow_nonneg hb0.le _)
          _ = _ := by ring
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ B.cr * (Φ w).toReal + B.cr * (Φ w).toReal :=
            add_le_add (e1.trans (mul_le_mul_of_nonneg_left hs1 B.cr_nonneg))
              (e2.trans (mul_le_mul_of_nonneg_left hs2 B.cr_nonneg))
        _ = _ := by ring
  have hae : ∀ᵐ w ∂(Pr x), Φ w ≠ ⊤ :=
    (ae_lt_top' hΦm.aemeasurable hΦint).mono fun w h => h.ne
  have hdom_int : Integrable (fun w => 2 * B.cr * (Φ w).toReal) (Pr x) :=
    (integrable_toReal_of_lintegral_ne_top hΦm.aemeasurable hΦint).const_mul _
  have hRm : ∀ n, AEStronglyMeasurable
      (fun w => P.reward (truncTime (P.ruleTime S) n) w) (Pr x) := fun n => by
    have : Measurable fun w => P.reward (truncTime (P.ruleTime S) n) w := by
      simp only [reward_trunc]
      exact measurable_comp_nat (E := E)
        (f := fun m w => (∑ k ∈ Finset.range m, P.beta ^ k * P.c (w k)) + P.beta ^ m * P.g (w m))
        (fun m => (Finset.measurable_sum _ fun k _ =>
          (P.c_meas.comp (measurable_pi_apply k)).const_mul _).add
          ((P.g_meas.comp (measurable_pi_apply m)).const_mul _)) (measurable_tN hS.1 n)
    exact this.aestronglyMeasurable
  have hfinae : ∀ᵐ w ∂(Pr x), P.ruleTime S w ≠ ⊤ := by
    rw [ae_iff]; simp only [ne_eq, not_not]; exact hfin x
  have hlim : ∀ᵐ w ∂(Pr x), Tendsto (fun n => P.reward (truncTime (P.ruleTime S) n) w) atTop
      (𝓝 (P.reward (P.ruleTime S) w)) := by
    filter_upwards [hfinae] with w hw
    refine tendsto_atTop_of_eventually_const (i₀ := (P.ruleTime S w).toNat) fun n hn => ?_
    have : truncTime (P.ruleTime S) n w = P.ruleTime S w := by
      unfold truncTime; refine min_eq_left ?_
      rw [← ENat.coe_toNat hw]; exact_mod_cast hn
    unfold StationaryProblem.reward; rw [this]
  have hbound : ∀ n, ∀ᵐ w ∂(Pr x), ‖P.reward (truncTime (P.ruleTime S) n) w‖ ≤
      2 * B.cr * (Φ w).toReal := fun n => by
    filter_upwards [hae] with w hw; rw [Real.norm_eq_abs]; exact hbd _ w hw
  have hT := tendsto_integral_of_dominated_convergence _ hRm hdom_int hbound hlim
  have hRτint : Integrable (fun w => P.reward (P.ruleTime S) w) (Pr x) :=
    hdom_int.mono' (aestronglyMeasurable_of_tendsto_ae _ hRm hlim) (by
      filter_upwards [hae] with w hw; rw [Real.norm_eq_abs]; exact hbd _ w hw)
  unfold StationaryProblem.Gf StationaryProblem.EReward
  rw [erealIntegral_of_integrable _ (fun w => P.reward (P.ruleTime S) w) hRτint]
  have hE : ∀ n, erealIntegral (Pr x) (fun w => (P.reward (truncTime (P.ruleTime S) n) w : EReal))
      = ((∫ w, P.reward (truncTime (P.ruleTime S) n) w ∂(Pr x) : ℝ) : EReal) := fun n =>
    erealIntegral_of_integrable _ (fun w => P.reward (truncTime (P.ruleTime S) n) w)
      (hdom_int.mono' (hRm n) (hbound n))
  simp only [hE]
  exact (((continuous_coe_real_ereal.tendsto _).comp hT).liminf_eq).symm

lemma partB (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hS : P.IsMaximizer S P.Jlim)
    (hc : ∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) (hb1 : P.beta = 1)
    (hG : ∀ x : E, P.Gf Pr S x = P.Jlim x) : ∀ x, Pr x {w | P.ruleTime S w = ⊤} = 0 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_10_2_2 P Pr hPr hB
  obtain ⟨s, hs0, hcs⟩ := hc
  intro x
  haveI := hPr.1 x
  by_contra hp
  set T := {w : ℕ → E | P.ruleTime S w = ⊤} with hT
  set p := (Pr x T).toReal with hpdef
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  obtain ⟨C1, hC1, hbB⟩ := hB.1 x
  have hTm : MeasurableSet T := measurable_hitTime hS.1 (measurableSet_singleton ⊤)
  have hE : ∀ n : ℕ, P.EReward Pr (truncTime (P.ruleTime S) n) x ≤
      ((s * n * p + C1.toReal : ℝ) : EReal) := by
    intro n
    set G : (ℕ → E) → ℝ := fun w => max (P.g (w (tN S n w))) 0 with hGdef
    have hGm : Measurable G := measurable_comp_nat (E := E)
      (f := fun m w => max (P.g (w m)) 0)
      (fun m => (P.g_meas.comp (measurable_pi_apply m)).max measurable_const) (measurable_tN hS.1 n)
    have hfin0 : Pr x {w | truncTime (hitTime S) n w = ⊤} = 0 := by
      have : {w : ℕ → E | truncTime (hitTime S) n w = ⊤} = ∅ := by
        ext w; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [show truncTime (hitTime S) n w = _ from truncTime_eq P S n w]
        exact ENat.coe_ne_top _
      rw [this, measure_empty]
    have hGl : ∫⁻ w, ENNReal.ofReal (G w) ∂(Pr x) ≤ C1 := by
      refine le_trans (lintegral_mono fun w => ?_) (hbB _ (isStopTime_trunc hS.1 n) hfin0)
      have ht : (truncTime (hitTime S) n w).toNat = tN S n w := by
        rw [show truncTime (hitTime S) n w = _ from truncTime_eq P S n w]; simp
      rw [ht, hb1, one_pow, one_mul]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 0 ≤ ∑ k ∈ Finset.range (tN S n w), (1 : ℝ) ^ k * max (P.c (w k)) 0 :=
        Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg zero_le_one _) (le_max_right _ _)
      simp only [hGdef]; linarith
    have hGint : Integrable G (Pr x) := ⟨hGm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun w =>
        show (0 : ℝ) ≤ G w from le_max_right _ _)).2 (lt_of_le_of_lt hGl hC1)⟩
    have hUint : Integrable (fun w => T.indicator (fun _ => s * n) w + G w) (Pr x) :=
      ((integrable_const _).indicator hTm).add hGint
    have hbound : ∀ w, P.reward (truncTime (P.ruleTime S) n) w ≤
        T.indicator (fun _ => s * n) w + G w := by
      intro w
      rw [reward_trunc, hb1]
      simp only [one_pow, one_mul]
      have hsum : ∑ k ∈ Finset.range (tN S n w), P.c (w k) ≤ (tN S n w) * s := by
        calc _ ≤ ∑ k ∈ Finset.range (tN S n w), s := Finset.sum_le_sum fun k _ => hcs (w k)
          _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hgG : P.g (w (tN S n w)) ≤ G w := le_max_left _ _
      by_cases hw : w ∈ T
      · rw [Set.indicator_of_mem hw]
        have hw' : hitTime S w = ⊤ := hw
        rw [tN_of_lt (by rw [hw']; exact ENat.coe_lt_top n)] at hsum hgG ⊢
        linarith
      · rw [Set.indicator_of_notMem hw]
        have : (tN S n w : ℝ) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hs0.le
        linarith
    unfold StationaryProblem.EReward
    refine le_trans (erealIntegral_mono _ fun w => EReal.coe_le_coe_iff.2 (hbound w)) ?_
    rw [erealIntegral_of_integrable _ (fun w => T.indicator (fun _ => s * n) w + G w) hUint,
      EReal.coe_le_coe_iff, integral_add ((integrable_const _).indicator hTm) hGint,
      integral_indicator_const _ hTm]
    have hGi : ∫ w, G w ∂(Pr x) ≤ C1.toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w =>
        show (0 : (ℕ → E) → ℝ) w ≤ G w from le_max_right _ _) hGm.aestronglyMeasurable]
      exact ENNReal.toReal_mono hC1.ne hGl
    simp only [smul_eq_mul, measureReal_def, ← hpdef]
    nlinarith
  have hlim : Tendsto (fun n : ℕ => ((s * n * p + C1.toReal : ℝ) : EReal)) atTop (𝓝 ⊥) := by
    rw [EReal.tendsto_nhds_bot_iff_real]; intro r
    have hneg : s * p < 0 := mul_neg_of_neg_of_pos hs0 hp0
    have : Tendsto (fun n : ℕ => s * p * (n : ℝ) + C1.toReal) atTop atBot :=
      tendsto_atBot_add_const_right _ _ (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hneg)
    filter_upwards [this.eventually (eventually_lt_atBot r)] with n hn
    exact EReal.coe_lt_coe_iff.2 (by linarith [show s * n * p = s * p * n by ring])
  have hGf : P.Gf Pr S x ≤ ⊥ := by
    unfold StationaryProblem.Gf
    calc liminf (fun n : ℕ => P.EReward Pr (truncTime (P.ruleTime S) n) x) atTop
        ≤ liminf (fun n : ℕ => ((s * n * p + C1.toReal : ℝ) : EReal)) atTop :=
          liminf_le_liminf (Eventually.of_forall fun n => hE n)
      _ = ⊥ := hlim.liminf_eq
  rw [hG x] at hGf
  exact EReal.coe_ne_bot (P.g x) (le_bot_iff.1 ((h4 x).trans hGf))

lemma partC (P : StationaryProblem E) {Pr : E → Measure (ℕ → E)} (hPr : P.IsPathLaw Pr)
    (hB : P.AssumptionB Pr) {S : Set E} (hS : P.IsMaximizer S P.Jlim)
    (hC : ∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal))
    (hfin : ∀ x, Pr x {w | P.ruleTime S w = ⊤} = 0) : ∀ x, P.Gf Pr S x = P.Jlim x := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := theorem_10_2_2 P Pr hPr hB
  obtain ⟨C, hC⟩ := hC
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right C 0
  have hfix : ∀ x, P.Tf S P.Jlim x = P.Jlim x := fun x => (hS.2 x).trans (h2 x).symm
  have hfinJ : ∀ x, P.Jlim x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (EReal.coe_ne_top (P.g x + C)) (by rw [EReal.coe_add]; exact hC x)
  have hbotJ : ∀ x, P.Jlim x ≠ ⊥ := fun x => ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (h4 x)
  set j := fun x => (P.Jlim x).toReal with hjdef
  have hJj : ∀ x, P.Jlim x = (j x : EReal) := fun x => (EReal.coe_toReal (hfinJ x) (hbotJ x)).symm
  have hjm : Measurable j := (Jlim_measurable P).ereal_toReal
  have hJfun : P.Jlim = fun y => (j y : EReal) := funext hJj
  have hjg : ∀ x, P.g x ≤ j x := fun x => EReal.coe_le_coe_iff.1 (by rw [← hJj]; exact h4 x)
  have hjC : ∀ x, j x ≤ P.g x + C' := fun x => by
    have := hC x
    rw [hJj, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    linarith [le_max_left C 0]
  have hjS : ∀ x ∈ S, j x = P.g x := fun x hx => by
    have := hfix x; unfold StationaryProblem.Tf at this
    rw [if_pos hx, hJj] at this; exact_mod_cast this.symm
  have hjN : ∀ x ∉ S, (j x : EReal) = (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) := fun x hx => by
    have := hfix x; unfold StationaryProblem.Tf at this
    rw [if_neg hx, hJfun] at this; exact this.symm
  have hS2 : ∀ x ∈ S, (P.c x : EReal) + (P.beta : EReal) *
      erealIntegral (P.QX x) (fun y => (j y : EReal)) ≤ P.g x := fun x hx => by
    have e := h2 x; unfold StationaryProblem.T at e
    rw [← hJfun]
    calc _ ≤ max (P.g x : EReal) _ := le_max_right _ _
      _ = P.Jlim x := e.symm
      _ = P.g x := by rw [hJj, hjS x hx]
  have hgint : ∀ x m, ∫⁻ w, ENNReal.ofReal (max (P.g (w m)) 0) ∂(Pr x) ≠ ⊤ := by
    intro x m
    obtain ⟨C1, hC1, hb1⟩ := hB.1 x
    have hst : IsStopTime (fun _ : ℕ → E => (m : ℕ∞)) := fun k => MeasurableSet.const _
    have := hb1 _ hst (by simp)
    simp only [ENat.toNat_coe] at this
    have hle : ∫⁻ w, ENNReal.ofReal (P.beta ^ m) * ENNReal.ofReal (max (P.g (w m)) 0) ∂(Pr x)
        ≤ C1 := by
      refine le_trans (lintegral_mono fun w => ?_) this
      rw [← ENNReal.ofReal_mul (pow_nonneg P.beta_mem.1.le _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 0 ≤ ∑ k ∈ Finset.range m, P.beta ^ k * max (P.c (w k)) 0 :=
        Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg P.beta_mem.1.le _) (le_max_right _ _)
      linarith
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hle
    rcases ENNReal.mul_lt_top_iff.1 (lt_of_le_of_lt hle hC1) with ⟨_, hb⟩ | ha | hb
    · exact hb.ne
    · exact absurd (ENNReal.ofReal_eq_zero.1 ha) (not_le.2 (pow_pos P.beta_mem.1 m))
    · rw [hb]; exact ENNReal.zero_ne_top
  have hjint : ∀ x m, ∫⁻ w, ENNReal.ofReal (max (j (w m)) 0) ∂(Pr x) ≠ ⊤ := by
    intro x m
    haveI := hPr.1 x
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hgint x m, ENNReal.ofReal_ne_top (r := C')⟩) ?_
    calc _ ≤ ∫⁻ w, (ENNReal.ofReal (max (P.g (w m)) 0) + ENNReal.ofReal C') ∂(Pr x) :=
          lintegral_mono fun w => by
            rw [← ENNReal.ofReal_add (le_max_right _ _) hC'0]
            refine ENNReal.ofReal_le_ofReal (max_le ?_ (add_nonneg (le_max_right _ _) hC'0))
            linarith [hjC (w m), le_max_left (P.g (w m)) 0]
      _ = _ := by rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  have hD : ∀ x m, ∫⁻ w, ENNReal.ofReal (j (w m) - P.g (w m)) ∂(Pr x) ≠ ⊤ := by
    intro x m; haveI := hPr.1 x
    refine ne_top_of_le_ne_top (b := ∫⁻ _w, ENNReal.ofReal C' ∂(Pr x)) ?_
      (lintegral_mono fun w => ENNReal.ofReal_le_ofReal (by linarith [hjC (w m)]))
    rw [lintegral_const, measure_univ, mul_one]; exact ENNReal.ofReal_ne_top
  intro x
  haveI := hPr.1 x
  rw [hJj]
  have hER := fun n => ER_eq P S hS.1 j hjm hPr hB hjS hjN hS2 hjg hjint hD n x
  refine Gf_eq_of P Pr S j x (fun n => P.beta ^ n * ∫ w, Dn P S j n w ∂(Pr x))
    (fun n => (hER n).2.2) ?_
  set A : ℕ → Set (ℕ → E) := fun n => {w | (n : ℕ∞) < hitTime S w} with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n => by
    have := (meas_hitTime_le hS.1 n).compl
    simpa only [hA, Set.compl_setOf, not_le] using this
  have hAanti : Antitone A := fun a b hab w hw =>
    lt_of_le_of_lt (show ((a : ℕ) : ℕ∞) ≤ (b : ℕ∞) by exact_mod_cast hab) hw
  have hAint : ⋂ n, A n = {w | P.ruleTime S w = ⊤} := by
    ext w
    simp only [Set.mem_iInter, Set.mem_setOf_eq, hA, StationaryProblem.ruleTime]
    generalize hitTime S w = t
    induction t using ENat.recTopCoe with
    | top => simp
    | coe t =>
      simp only [ENat.coe_ne_top, iff_false, not_forall, not_lt]
      exact ⟨t, le_rfl⟩
  have hlim : Tendsto (fun n => (Pr x (A n)).toReal) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := Pr x) (fun n => (hAm n).nullMeasurableSet)
      hAanti ⟨0, measure_ne_top _ _⟩
    rw [hAint, hfin x] at this
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
    rw [ENNReal.toReal_zero] at h
    exact h
  refine squeeze_zero (fun n => mul_nonneg (pow_nonneg P.beta_mem.1.le n) (hER n).2.1)
    (fun n => ?_) (by simpa using hlim.const_mul C')
  have hDle : ∀ w, Dn P S j n w ≤ (A n).indicator (fun _ => C') w := by
    intro w; unfold Dn
    split_ifs with h
    · simp only [Set.indicator, hA, Set.mem_setOf_eq, h, if_true]; linarith [hjC (w n)]
    · simp only [Set.indicator, hA, Set.mem_setOf_eq, h, if_false]; exact le_rfl
  calc P.beta ^ n * ∫ w, Dn P S j n w ∂(Pr x) ≤ 1 * ∫ w, Dn P S j n w ∂(Pr x) :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ P.beta_mem.1.le P.beta_mem.2) (hER n).2.1
    _ ≤ ∫ w, (A n).indicator (fun _ => C') w ∂(Pr x) := by
        rw [one_mul]
        exact integral_mono (hER n).1 ((integrable_const C').indicator (hAm n)) hDle
    _ = C' * (Pr x (A n)).toReal := by
        rw [integral_indicator_const _ (hAm n)]; simp [measureReal_def, mul_comm]

end MDPS1026

open MDPS1026 in
open BauerleRiederMDP.Stopping in
theorem solution {E : Type*} [MeasurableSpace E] (P : StationaryProblem E)
    (Pr : E → Measure (ℕ → E)) (hPr : P.IsPathLaw Pr) (hB : P.AssumptionB Pr)
    (S : Set E) (hS : P.IsMaximizer S P.Jlim) :
    (∀ B : P.BoundingFunction, P.beta * B.alpha < 1 →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      ((∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ s : ℝ, s < 0 ∧ ∀ x : E, P.c x ≤ s) → P.beta = 1 → (∀ x : E, P.Gf Pr S x = P.Jlim x) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) ∧
      (AssumptionBLim P Pr → P.IsOptimal Pr (P.ruleTime S))) ∧
    ((∃ C : ℝ, ∀ x : E, P.Jlim x ≤ (P.g x : EReal) + (C : EReal)) →
      (∀ x : E, Pr x {w | P.ruleTime S w = ⊤} = 0) →
      (∀ x : E, P.Gf Pr S x = P.Jlim x) ∧
      (AssumptionBLim P Pr → P.IsOptimal Pr (P.ruleTime S))) := by
  refine ⟨fun B hBa => ⟨partA1 P hPr hB hS B hBa, partA2 P hPr hB hS B hBa⟩,
    fun hc hb1 hG => ?_, fun hC hfin => ?_⟩
  · have hfin := partB P hPr hB hS hc hb1 hG
    exact ⟨hfin, fun hBL => opt_of P hPr hB hS.1 hfin hBL hG⟩
  · have hG := partC P hPr hB hS hC hfin
    exact ⟨hG, fun hBL => opt_of P hPr hB hS.1 hfin hBL hG⟩
