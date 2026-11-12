-- Prove2me | solution 1 for FormalizedScopeReach.equal_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-15T19:16:23.528906+00:00
-- url     : https://prove2.me/submissions/c79acf0d-9de9-4133-be07-8569ec593822

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Definitions.Def_FormalizedScopeReach_REACH
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.SplitIfs
import Definitions.Def_FormalizedScopeReach_SCOPE
import Definitions.Def_FormalizedScopeReach_Trials
import Definitions.Def_FormalizedScopeReach_Times
import Mathlib.Data.Nat.Find

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable

variable {V : Type}

lemma hazard_nonneg (M : Model V) (h : List V) : 0 ≤ hazard M h :=
  ENNReal.toReal_nonneg

lemma hazard_le_one (M : Model V) (h : List V) : hazard M h ≤ 1 := by
  simpa [hazard] using ENNReal.toReal_mono ENNReal.one_ne_top ((M.next h).coe_le_one M.outcome)

lemma reachScore_nonneg (M : Model V) (x : Timeline V) : 0 ≤ reachScore M x := by
  simp only [reachScore, sub_nonneg]
  exact Finset.prod_le_one (fun i _ => sub_nonneg.mpr (hazard_le_one M _))
    (fun i _ => sub_le_self _ (hazard_nonneg M _))

lemma reachScore_le_one (M : Model V) (x : Timeline V) : reachScore M x ≤ 1 := by
  simp only [reachScore, sub_le_self_iff]
  exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hazard_le_one M _))

lemma step_survival (M : Model V) (h : List V) (a : V) (ha : a ≠ M.outcome) :
    avoidingStepMass M h a * (1 - M.next h M.outcome) = M.next h a := by
  classical
  simp only [avoidingStepMass, if_neg ha]
  by_cases hp : M.next h M.outcome = 1
  · have hz : M.next h a = 0 := ((M.next h).apply_eq_zero_iff a).mpr (by
      rw [((M.next h).apply_eq_one_iff M.outcome).mp hp]
      simpa using ha)
    simp [hp, hz]
  · exact ENNReal.div_mul_cancel (ne_of_gt (tsub_pos_iff_lt.mpr (lt_of_le_of_ne ((M.next h).coe_le_one M.outcome) hp)))
      (ne_of_lt (lt_of_le_of_lt tsub_le_self ENNReal.one_lt_top))

lemma ofReal_survival (M : Model V) (x : Timeline V) :
    ENNReal.ofReal (1 - reachScore M x) =
      ∏ i : Fin x.length, (1 - M.next (x.take i.val) M.outcome) := by
  simp only [reachScore, sub_sub_cancel]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (hazard_le_one M _))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [hazard, ENNReal.ofReal_sub 1 (by positivity : 0 ≤ ((M.next (x.take i.val)) M.outcome).toReal)]
  simp [(M.next _).apply_ne_top]

/-- Appendix C: the avoiding-path factors cancel against all-failure Bernoulli factors. -/
lemma path_survival (M : Model V) (x : Timeline V) :
    avoidingPathMass M x * ENNReal.ofReal (1 - reachScore M x) =
      if M.outcome ∉ x then pathMass M x else 0 := by
  classical
  rw [ofReal_survival]
  by_cases ht : terminal M x <;> by_cases ho : M.outcome ∉ x
  · simp only [avoidingPathMass, pathMass, ht, ho, not_false_eq_true, and_self, ite_true]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact step_survival M _ _ (fun he => ho (he ▸ List.get_mem x i))
  · simp [avoidingPathMass, pathMass, ht, ho]
  · simp [avoidingPathMass, pathMass, ht, ho]
  · simp [avoidingPathMass, pathMass, ht, ho]

/-- Sum the probability-preserving correspondence between the complementary events. -/
lemma lintegral_survival (M : Model V) :
    (∫⁻ x, ENNReal.ofReal (1 - reachScore M x) ∂(avoidingLaw M)) =
      originalLaw M {x | M.outcome ∉ x} := by
  classical
  rw [avoidingLaw, lintegral_sum_measure, originalLaw, Measure.sum_apply _ (by trivial)]
  apply tsum_congr
  intro x
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    Measure.smul_apply, Measure.dirac_apply' x (show MeasurableSet {y : Timeline V | M.outcome ∉ y} from trivial)]
  rw [path_survival]
  by_cases h : M.outcome ∉ x <;> simp [h]

lemma reachScore_memLp [Countable V] (M : Model V) (μ : Measure (Timeline V))
    [IsFiniteMeasure μ] : MemLp (reachScore M) 2 μ :=
  memLp_of_bounded (ae_of_all _ (fun x => ⟨reachScore_nonneg M x, reachScore_le_one M x⟩))
    (measurable_of_countable _).aestronglyMeasurable 2

lemma reachScore_integral [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)] :
    (∫ x, reachScore M x ∂(avoidingLaw M)) = eventProbability M := by
  have hi := (reachScore_memLp M (avoidingLaw M)).integrable (by norm_num)
  have hs := (integrable_const (1 : ℝ)).sub hi
  have he := integral_eq_lintegral_of_nonneg_ae
    (ae_of_all (avoidingLaw M) (fun x => sub_nonneg.mpr (reachScore_le_one M x)))
    hs.aestronglyMeasurable
  rw [lintegral_survival, integral_sub (integrable_const _) hi] at he
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at he
  have hc : originalLaw M {x | M.outcome ∉ x} =
      1 - originalLaw M {x | M.outcome ∈ x} := by
    exact prob_compl_eq_one_sub (show MeasurableSet {x : Timeline V | M.outcome ∈ x} from trivial)
  rw [hc, ENNReal.toReal_sub_of_le (prob_le_one) ENNReal.one_ne_top] at he
  simp only [ENNReal.toReal_one] at he
  exact sub_right_inj.mp he

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable
variable {V : Type}

def listSplit : List V ≃ Unit ⊕ (V × List V) where
  toFun | [] => Sum.inl Unit.unit | a :: x => Sum.inr (a, x)
  invFun | Sum.inl _ => [] | Sum.inr (a, x) => a :: x
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x with
    | inl x => cases x; rfl
    | inr x => cases x; rfl

lemma tsum_list (f : List V → ℝ≥0∞) :
    ∑' x, f x = f [] + ∑' a, ∑' x, f (a :: x) := by
  rw [← listSplit.symm.tsum_eq]
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton]
  rw [ENNReal.tsum_prod']
  rfl

/-- The original sampling law continued from a fixed history. -/
def futureMass (M : Model V) : List V → List V → ℝ≥0∞
  | h, [] => if running M h then 0 else 1
  | h, a :: x => if running M h then M.next h a * futureMass M (h ++ [a]) x else 0

def futureTotal (M : Model V) (h : List V) : ℝ≥0∞ :=
  ∑' x, futureMass M h x

def cutTotal (M : Model V) (n : ℕ) (h : List V) : ℝ≥0∞ :=
  ∑' x, if x.length ≤ n then futureMass M h x else 0

lemma cutTotal_zero (M : Model V) (h : List V) :
    cutTotal M 0 h = if running M h then 0 else 1 := by
  rw [cutTotal, tsum_list]
  simp [futureMass]

lemma cutTotal_succ (M : Model V) (n : ℕ) (h : List V) :
    cutTotal M (n + 1) h = if running M h then
      ∑' a, M.next h a * cutTotal M n (h ++ [a]) else 1 := by
  rw [cutTotal, tsum_list]
  by_cases ha : running M h
  · simp only [List.length_nil, Nat.zero_le, ite_true, futureMass, ha,
      List.length_cons, Nat.add_le_add_iff_right, zero_add]
    congr 1
    ext a
    rw [cutTotal, ← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro x
    split_ifs <;> simp
  · simp [futureMass, ha]

lemma cutTotal_le_one (M : Model V) (n : ℕ) (h : List V) : cutTotal M n h ≤ 1 := by
  induction n generalizing h with
  | zero => rw [cutTotal_zero]; split_ifs <;> simp
  | succ n ih =>
    rw [cutTotal_succ]
    split_ifs
    · calc
        _ ≤ ∑' a, M.next h a * 1 := ENNReal.tsum_le_tsum (fun a => mul_le_mul' le_rfl (ih _))
        _ = 1 := by simp
    · rfl

lemma futureTotal_le_one (M : Model V) (h : List V) : futureTotal M h ≤ 1 := by
  rw [futureTotal, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro s
  have hle : ∑ x ∈ s, futureMass M h x ≤ cutTotal M (s.sup List.length) h := by
    calc
      _ = ∑ x ∈ s, if x.length ≤ s.sup List.length then futureMass M h x else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [if_pos (Finset.le_sup hx)]
      _ ≤ _ := ENNReal.sum_le_tsum s
  exact hle.trans (cutTotal_le_one M _ h)

lemma futureTotal_eq (M : Model V) (h : List V) :
    futureTotal M h = if running M h then
      ∑' a, M.next h a * futureTotal M (h ++ [a]) else 1 := by
  rw [futureTotal, tsum_list]
  by_cases ha : running M h <;> simp [futureMass, ha, ENNReal.tsum_mul_left, futureTotal]

/-- Almost-sure termination passes to every child with positive conditional probability. -/
lemma normalized_child (M : Model V) (h : List V)
    (hn : futureTotal M h = 1) (ha : running M h) (a : V) (hp : M.next h a ≠ 0) :
    futureTotal M (h ++ [a]) = 1 := by
  have he : (∑' a, M.next h a * futureTotal M (h ++ [a])) = 1 := by
    simpa [futureTotal_eq M h, ha] using hn
  have heq : M.next h a * futureTotal M (h ++ [a]) = M.next h a := by
    by_contra hn'
    have hlt := ENNReal.tsum_lt_tsum (by rw [he]; exact ENNReal.one_ne_top)
      (fun b => (mul_le_mul' (le_refl (M.next h b)) (futureTotal_le_one M (h ++ [b]))).trans_eq (mul_one _))
      (lt_of_le_of_ne ((mul_le_mul' (le_refl (M.next h a)) (futureTotal_le_one M (h ++ [a]))).trans_eq (mul_one _)) hn')
    simp [he] at hlt
  exact (ENNReal.mul_eq_left hp ((M.next h).apply_ne_top a)).mp heq

lemma futureMass_formula (M : Model V) (h x : List V) :
    futureMass M h x = if (¬ running M (h ++ x)) ∧
      (∀ i : Fin x.length, running M (h ++ x.take i.val)) then
      ∏ i : Fin x.length, M.next (h ++ x.take i.val) (x.get i) else 0 := by
  induction x generalizing h with
  | nil => simp [futureMass]
  | cons a x ih =>
    simp only [futureMass, ih, List.length_cons, Fin.forall_fin_succ,
      Fin.prod_univ_succ, List.take_zero, List.append_nil, List.get_eq_getElem,
      List.getElem_cons_zero, Fin.val_zero, Fin.val_succ, List.take_succ_cons,
      List.getElem_cons_succ, List.append_assoc, List.singleton_append]
    by_cases ha : running M h
    · simp only [ha, true_and, ite_true]
      split_ifs <;> simp_all
    · simp [ha]

lemma futureMass_root (M : Model V) (x : List V) : futureMass M [] x = pathMass M x := by
  rw [futureMass_formula]
  simp only [pathMass, terminal, List.nil_append]
  congr 1
  apply propext
  unfold running
  tauto

lemma normalized_root (M : Model V) [IsProbabilityMeasure (originalLaw M)] :
    futureTotal M [] = 1 := by
  have ht := measure_univ (μ := originalLaw M)
  simpa [originalLaw, Measure.sum_apply, futureTotal, futureMass_root] using ht

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable
variable {V : Type}

/-- Appendix B's hazard, masked before the first outcome and the threshold. -/
def stepReward (M : Model V) : ℕ → List V → List V → ℝ≥0∞
  | _, _, [] => 0
  | 0, h, _ :: _ => if active M h then M.next h M.outcome else 0
  | n+1, h, a :: x => if active M h then stepReward M n (h ++ [a]) x else 0

/-- Indicator that the first outcome occurs at this step of the continuation. -/
def hitReward (M : Model V) : ℕ → List V → List V → ℝ≥0∞
  | _, _, [] => 0
  | 0, h, a :: _ => if active M h ∧ a = M.outcome then 1 else 0
  | n+1, h, a :: x => if active M h then hitReward M n (h ++ [a]) x else 0

def stepExpectation (M : Model V) (n : ℕ) (h : List V) : ℝ≥0∞ :=
  ∑' x, futureMass M h x * stepReward M n h x

def hitByLength (M : Model V) (n : ℕ) (h : List V) : ℝ≥0∞ :=
  ∑' x, futureMass M h x * hitReward M n h x

lemma stepExpectation_zero (M : Model V) (h : List V) :
    stepExpectation M 0 h = if active M h then M.next h M.outcome * futureTotal M h else 0 := by
  rw [stepExpectation, tsum_list, futureTotal_eq]
  by_cases ha : active M h
  · have hr : running M h := ha.1
    simp only [futureMass, stepReward, ha, hr, ite_true, mul_zero, zero_add]
    simp only [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, futureTotal]
    exact mul_comm _ _
  · simp [futureMass, stepReward, ha]

lemma stepExpectation_succ (M : Model V) (n : ℕ) (h : List V) :
    stepExpectation M (n+1) h = if active M h then
      ∑' a, M.next h a * stepExpectation M n (h ++ [a]) else 0 := by
  rw [stepExpectation, tsum_list]
  by_cases ha : active M h
  · have hr : running M h := ha.1
    simp [futureMass, stepReward, ha, hr, mul_assoc, ENNReal.tsum_mul_left, stepExpectation]
  · simp [futureMass, stepReward, ha]

lemma hitByLength_zero (M : Model V) (h : List V) :
    hitByLength M 0 h = if active M h then
      M.next h M.outcome * futureTotal M (h ++ [M.outcome]) else 0 := by
  rw [hitByLength, tsum_list]
  by_cases ha : active M h
  · have hr : running M h := ha.1
    simp only [futureMass, hitReward, ha, hr, ite_true, true_and, mul_zero, zero_add,
      mul_ite, mul_one]
    rw [ENNReal.tsum_comm]
    simp [ENNReal.tsum_mul_left, futureTotal]
  · simp [futureMass, hitReward, ha]

lemma hitByLength_succ (M : Model V) (n : ℕ) (h : List V) :
    hitByLength M (n+1) h = if active M h then
      ∑' a, M.next h a * hitByLength M n (h ++ [a]) else 0 := by
  rw [hitByLength, tsum_list]
  by_cases ha : active M h
  · have hr : running M h := ha.1
    simp [futureMass, hitReward, ha, hr, mul_assoc, ENNReal.tsum_mul_left, hitByLength]
  · simp [futureMass, hitReward, ha]

lemma stepExpectation_eq_hitByLength (M : Model V) (n : ℕ) (h : List V)
    (hn : futureTotal M h = 1) : stepExpectation M n h = hitByLength M n h := by
  induction n generalizing h with
  | zero =>
    rw [stepExpectation_zero, hitByLength_zero]
    split_ifs with ha
    · by_cases hp : M.next h M.outcome = 0
      · simp [hp]
      · rw [hn, normalized_child M h hn ha.1 M.outcome hp]
    · rfl
  | succ n ih =>
    rw [stepExpectation_succ, hitByLength_succ]
    split_ifs with ha
    · apply tsum_congr
      intro a
      by_cases hp : M.next h a = 0
      · simp [hp]
      · rw [ih _ (normalized_child M h hn ha.1 a hp)]
    · rfl

lemma stepReward_after_outcome (M : Model V) (h x : List V) (ho : M.outcome ∈ h) (n : ℕ) :
    stepReward M n h x = 0 := by
  cases x <;> cases n <;> simp [stepReward, active, ho]

lemma hitReward_after_outcome (M : Model V) (h x : List V) (ho : M.outcome ∈ h) (n : ℕ) :
    hitReward M n h x = 0 := by
  cases x <;> cases n <;> simp [hitReward, active, ho]

lemma stepReward_good (M : Model V) (h x : List V)
    (hp : ∀ i : Fin x.length, running M (h ++ x.take i.val)) (n : ℕ) :
    stepReward M n h x = if n < x.length then
      if M.outcome ∉ h ++ x.take n then M.next (h ++ x.take n) M.outcome else 0 else 0 := by
  induction x generalizing h n with
  | nil => simp [stepReward]
  | cons a x ih =>
    have hr : running M h := by simpa using hp 0
    have hc : ∀ i : Fin x.length, running M ((h ++ [a]) ++ x.take i.val) := by
      intro i
      simpa [List.take_succ_cons, List.append_assoc] using hp i.succ
    by_cases ho : M.outcome ∈ h
    · rw [stepReward_after_outcome M h _ ho]
      simp [List.mem_append, ho]
    · have ha : active M h := ⟨hr, ho⟩
      cases n with
      | zero => simp [stepReward, ha, ho]
      | succ n => simp [stepReward, ha, ih _ hc, List.append_assoc]

lemma sum_reward_good (M : Model V) (h x : List V)
    (hp : ∀ i : Fin x.length, running M (h ++ x.take i.val)) :
    (∑' n, stepReward M n h x) =
      ∑ i : Fin x.length, if M.outcome ∉ h ++ x.take i.val then
        M.next (h ++ x.take i.val) M.outcome else 0 := by
  simp_rw [stepReward_good M h x hp]
  rw [tsum_eq_sum (s := Finset.range x.length) (fun n hn => by
    simp only [Finset.mem_range, not_lt] at hn
    simp [not_lt.mpr hn])]
  simp only [Finset.sum_ite_of_true (fun i hi => Finset.mem_range.mp hi)]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

lemma sum_hit_good (M : Model V) (h x : List V)
    (hp : ∀ i : Fin x.length, running M (h ++ x.take i.val))
    (ho : M.outcome ∉ h) :
    (∑' n, hitReward M n h x) = if M.outcome ∈ x then 1 else 0 := by
  induction x generalizing h with
  | nil => simp [hitReward]
  | cons a x ih =>
    have hr : running M h := by simpa using hp 0
    have ha : active M h := ⟨hr, ho⟩
    have hc : ∀ i : Fin x.length, running M ((h ++ [a]) ++ x.take i.val) := by
      intro i
      simpa [List.take_succ_cons, List.append_assoc] using hp i.succ
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [Finset.sum_range_one, Nat.zero_add, hitReward, ha, true_and, ite_true]
    by_cases he : a = M.outcome
    · subst a
      simp [hitReward_after_outcome M (h ++ [M.outcome]) x (by simp), List.mem_cons]
    · have hon : M.outcome ∉ h ++ [a] := by simpa [List.mem_append, eq_comm] using And.intro ho he
      rw [ih _ hc hon]
      simp [he, eq_comm]

lemma scopeScore_nonneg (M : Model V) (x : Timeline V) : 0 ≤ scopeScore M x := by
  unfold scopeScore
  exact Finset.sum_nonneg (fun i _ => by split_ifs <;> first | exact hazard_nonneg M _ | rfl)

lemma weighted_reward_root (M : Model V) (x : Timeline V) :
    futureMass M [] x * (∑' n, stepReward M n [] x) =
      pathMass M x * ENNReal.ofReal (scopeScore M x) := by
  rw [futureMass_root]
  by_cases ht : terminal M x
  · have hp := ht.2
    rw [sum_reward_good M [] x (by simpa using hp)]
    congr 1
    unfold scopeScore
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      split_ifs <;> first | exact hazard_nonneg M _ | rfl)]
    apply Finset.sum_congr rfl
    intro i hi
    have hr : ¬ M.stop (x.take i.val) := hp i
    by_cases ho : M.outcome ∈ x.take i.val <;>
      simp [active, hr, ho, hazard, (M.next _).apply_ne_top]
  · simp [pathMass, ht]

lemma weighted_hit_root (M : Model V) (x : Timeline V) :
    futureMass M [] x * (∑' n, hitReward M n [] x) =
      if M.outcome ∈ x then pathMass M x else 0 := by
  rw [futureMass_root]
  by_cases ht : terminal M x
  · rw [sum_hit_good M [] x (by simpa using ht.2) (by simp)]
    split_ifs <;> simp
  · simp [pathMass, ht]

/-- Tonelli exchanges nonnegative sums over unbounded time and terminal paths. -/
lemma scopeScore_lintegral (M : Model V) [IsProbabilityMeasure (originalLaw M)] :
    (∫⁻ x, ENNReal.ofReal (scopeScore M x) ∂originalLaw M) =
      originalLaw M {x | M.outcome ∈ x} := by
  have he := congrArg (fun f : ℕ → ℝ≥0∞ => ∑' n, f n)
    (funext (fun n => stepExpectation_eq_hitByLength M n [] (normalized_root M)))
  simp only [stepExpectation, hitByLength] at he
  rw [ENNReal.tsum_comm] at he
  conv_rhs at he => rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, weighted_reward_root, weighted_hit_root] at he
  rw [originalLaw, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
  rw [he, Measure.sum_apply _ (by trivial)]
  apply tsum_congr
  intro x
  simp only [Measure.smul_apply, Measure.dirac_apply' x
    (show MeasurableSet {y : Timeline V | M.outcome ∈ y} from trivial)]
  by_cases ho : M.outcome ∈ x <;> simp [ho]

lemma scopeScore_integrable [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] : Integrable (scopeScore M) (originalLaw M) := by
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (scopeScore_nonneg M)), scopeScore_lintegral]
  exact measure_lt_top _ _

lemma scopeScore_integral [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] :
    (∫ x, scopeScore M x ∂originalLaw M) = eventProbability M := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (scopeScore_nonneg M))
    (scopeScore_integrable M).aestronglyMeasurable, scopeScore_lintegral]
  rfl

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
namespace FormalizedScopeReach
variable {V : Type}

def sampleMean (f : Timeline V → ℝ) (n : ℕ) (xs : Fin n → Timeline V) : ℝ :=
  (∑ i, f (xs i)) / (n : ℝ)

lemma sampleMean_integrable {μ : Measure (Timeline V)} [IsProbabilityMeasure μ]
    {f : Timeline V → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (sampleMean f n) (iidLaw μ n) := by
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hf)).div_const _

lemma sampleMean_integral {μ : Measure (Timeline V)} [IsProbabilityMeasure μ]
    {f : Timeline V → ℝ} (hf : Integrable f μ) (n : ℕ) (hn : 0 < n) :
    (∫ xs, sampleMean f n xs ∂iidLaw μ n) = ∫ x, f x ∂μ := by
  unfold sampleMean iidLaw
  rw [integral_div, integral_finsetSum]
  · simp only [integral_comp_eval (μ := fun _ : Fin n => μ) hf.aestronglyMeasurable, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · intro i hi
    exact (measurePreserving_eval (fun _ : Fin n => μ) i).integrable_comp_of_integrable hf

lemma sampleMean_memLp {μ : Measure (Timeline V)} [IsProbabilityMeasure μ]
    {f : Timeline V → ℝ} (hf : MemLp f 2 μ) (n : ℕ) :
    MemLp (sampleMean f n) 2 (iidLaw μ n) := by
  have h := memLp_finsetSum Finset.univ (fun i _ =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => μ) i))
  change MemLp (fun xs => (∑ i, f (xs i)) / (n : ℝ)) 2 (Measure.pi (fun _ : Fin n => μ))
  simpa only [div_eq_mul_inv, mul_comm, Function.comp_def, Function.eval] using h.const_mul (n : ℝ)⁻¹

lemma sampleMean_variance {μ : Measure (Timeline V)} [IsProbabilityMeasure μ]
    {f : Timeline V → ℝ} (hf : MemLp f 2 μ) (n : ℕ) (hn : 0 < n) :
    variance (sampleMean f n) (iidLaw μ n) = variance f μ / (n : ℝ) := by
  have he : sampleMean f n = fun xs => (n : ℝ)⁻¹ * (∑ i : Fin n, fun ys => f (ys i)) xs := by
    ext xs
    simp [sampleMean, div_eq_mul_inv, mul_comm]
  rw [he, iidLaw, variance_const_mul, variance_sum_pi (fun _ => hf)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma monteCarloScore_memLp [Countable V] (M : Model V) (μ : Measure (Timeline V))
    [IsFiniteMeasure μ] : MemLp (monteCarloScore M) 2 μ := by
  apply memLp_of_bounded (a := 0) (b := 1) _ (measurable_of_countable _).aestronglyMeasurable 2
  exact ae_of_all _ (fun x => by
    classical
    simp only [monteCarloScore]
    split_ifs <;> norm_num)

lemma monteCarloScore_integral (M : Model V) :
    (∫ x, monteCarloScore M x ∂originalLaw M) = eventProbability M := by
  classical
  simpa [monteCarloScore, eventProbability, Set.indicator, Measure.real] using integral_indicator_one (μ := originalLaw M) (show MeasurableSet {x : Timeline V | M.outcome ∈ x} from trivial)

lemma monteCarloScore_variance [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] :
    variance (monteCarloScore M) (originalLaw M) =
      (1 - eventProbability M) * eventProbability M := by
  rw [variance_eq_sub (monteCarloScore_memLp M (originalLaw M))]
  have hs : monteCarloScore M ^ 2 = monteCarloScore M := by
    ext x
    classical
    simp [monteCarloScore]
  rw [hs, monteCarloScore_integral]
  ring

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable
variable {V : Type}

lemma trialSuccess_eq (x : Timeline V) (c : Fin x.length → Bool) :
    trialSuccess x c = if ∃ i, c i = true then 1 else 0 := by
  simp only [trialSuccess]
  by_cases hc : c = (fun _ => false)
  · simp [hc]
  · have hh : ∃ i, c i = true := by
      by_contra hn
      apply hc
      funext i
      simpa using (not_exists.mp hn i)
    simp [hc, hh]

/-- Appendix C, equations (8)--(10): the all-failure mass is the survival product. -/
lemma trialLaw_allFail (M : Model V) (x : Timeline V) :
    trialLaw M x {fun _ => false} = ENNReal.ofReal (1 - reachScore M x) := by
  rw [trialLaw, Measure.pi_singleton]
  rw [reachScore, sub_sub_cancel,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => sub_nonneg.mpr (hazard_le_one M _))]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [bernoulliMeasure_def, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  simp [unitInterval.symm, ENNReal.ofReal]
  ext
  simp [unitInterval.toNNReal, Real.toNNReal_of_nonneg (sub_nonneg.mpr (hazard_le_one M _))]
  rfl

lemma trialSuccess_memLp (M : Model V) (x : Timeline V) :
    MemLp (trialSuccess x) 2 (trialLaw M x) := by
  apply memLp_of_bounded (a := 0) (b := 1) _ (measurable_of_countable _).aestronglyMeasurable 2
  exact ae_of_all _ (fun c => by simp only [trialSuccess]; split_ifs <;> norm_num)

/-- Appendix C's map x ↦ (x, all-false) preserves the mass of complementary events. -/
lemma complementary_path_mass (M : Model V) (x : Timeline V) :
    avoidingPathMass M x * trialLaw M x {fun _ => false} =
      if M.outcome ∉ x then pathMass M x else 0 := by
  rw [trialLaw_allFail, path_survival]

/-- Section 4.3: E[1_B | outcome-free timeline x] is the REACH score. -/
lemma trialSuccess_mean (M : Model V) (x : Timeline V) :
    (∫ c, trialSuccess x c ∂trialLaw M x) = reachScore M x := by
  have hi : (∫ c, trialSuccess x c ∂trialLaw M x) =
      ((trialLaw M x) {c | c ≠ (fun _ => false)}).toReal := by
    change (∫ c, trialSuccess x c ∂trialLaw M x) =
      ((trialLaw M x) {fun _ => false}ᶜ).toReal
    simpa [trialSuccess, Set.indicator, Measure.real] using
      integral_indicator_one (μ := trialLaw M x)
        (measurableSet_singleton (fun _ : Fin x.length => false)).compl
  rw [hi]
  have hc : trialLaw M x {c | c ≠ (fun _ => false)} =
      1 - trialLaw M x {fun _ => false} :=
    prob_compl_eq_one_sub (measurableSet_singleton _)
  rw [hc, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, trialLaw_allFail]
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (reachScore_le_one M x))]
  simp

lemma trialSuccess_variance (M : Model V) (x : Timeline V) :
    variance (trialSuccess x) (trialLaw M x) = reachScore M x * (1 - reachScore M x) := by
  rw [variance_eq_sub (trialSuccess_memLp M x)]
  have hs : trialSuccess x ^ 2 = trialSuccess x := by
    ext c
    simp [trialSuccess]
  rw [hs, trialSuccess_mean]
  ring

/-- Section 4.3: the tower rule, evaluated through the explicit conditional trial laws. -/
lemma reach_tower_rule [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)] :
    (∫ x, ∫ c, trialSuccess x c ∂trialLaw M x ∂avoidingLaw M) = eventProbability M := by
  simp only [trialSuccess_mean, reachScore_integral]

/-- Section 4.4, equation (1), before division by the number of samples.
This is total variance with the conditional Bernoulli moments evaluated explicitly. -/
lemma reach_total_variance [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)] :
    variance (monteCarloScore M) (originalLaw M) =
      variance (reachScore M) (avoidingLaw M) +
        ∫ x, variance (trialSuccess x) (trialLaw M x) ∂avoidingLaw M := by
  have hr := reachScore_memLp M (avoidingLaw M)
  have hi := hr.integrable (by norm_num)
  have hs : Integrable (fun x => reachScore M x ^ 2) (avoidingLaw M) := hr.integrable_sq
  simp_rw [trialSuccess_variance]
  have he : (fun x => reachScore M x * (1 - reachScore M x)) =
      fun x => reachScore M x - reachScore M x ^ 2 := by ext x; ring
  rw [he, integral_sub hi hs, variance_eq_sub hr, monteCarloScore_variance, reachScore_integral]
  simp only [Pi.pow_apply]
  ring

lemma reachScore_variance_le_paper [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)] :
    variance (reachScore M) (avoidingLaw M) ≤ variance (monteCarloScore M) (originalLaw M) := by
  rw [reach_total_variance]
  exact le_add_of_nonneg_right (integral_nonneg (fun x => variance_nonneg _ _))

/-- The paper's equation (1), including the sample-count factor. -/
lemma reach_variance_gap [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (n : ℕ) (hn : 0 < n) :
    variance (monteCarloEstimator M n) (iidLaw (originalLaw M) n) -
      variance (reachEstimator M n) (iidLaw (avoidingLaw M) n) =
      (∫ x, variance (trialSuccess x) (trialLaw M x) ∂avoidingLaw M) / (n : ℝ) := by
  change variance (sampleMean (monteCarloScore M) n) _ -
    variance (sampleMean (reachScore M) n) _ = _
  rw [sampleMean_variance (monteCarloScore_memLp M _) n hn,
    sampleMean_variance (reachScore_memLp M _) n hn, reach_total_variance]
  ring

end FormalizedScopeReach


set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable
variable {V : Type}

lemma T_E_eq_length (M : Model V) (x : Timeline V) (ht : terminal M x) :
    T_E M x = (x.length : ℕ∞) := by
  have he : ∃ n : ℕ, n ≤ x.length ∧ M.stop (x.take n) := ⟨x.length, le_rfl, by simpa using ht.1⟩
  simp only [T_E, dif_pos he]
  congr 1
  apply (Nat.find_eq_iff he).mpr
  refine ⟨⟨le_rfl, by simpa using ht.1⟩, ?_⟩
  intro n hn h
  exact ht.2 ⟨n, hn⟩ h.2

lemma originalLaw_terminal (M : Model V) : ∀ᵐ x ∂originalLaw M, terminal M x := by
  rw [ae_iff]
  rw [originalLaw, Measure.sum_apply _ (by trivial)]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' x (show MeasurableSet {y : Timeline V | ¬ terminal M y} from trivial)]
  by_cases ht : terminal M x <;> simp [ht, pathMass]

lemma avoidingLaw_terminal (M : Model V) : ∀ᵐ x ∂avoidingLaw M, terminal M x := by
  rw [ae_iff, avoidingLaw, Measure.sum_apply _ (by trivial)]
  apply ENNReal.tsum_eq_zero.mpr
  intro x
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' x (show MeasurableSet {y : Timeline V | ¬ terminal M y} from trivial)]
  by_cases ht : terminal M x <;> simp [ht, avoidingPathMass]

lemma T_E_finite_original (M : Model V) : ∀ᵐ x ∂originalLaw M, T_E M x < ⊤ := by
  filter_upwards [originalLaw_terminal M] with x hx
  rw [T_E_eq_length M x hx]
  exact WithTop.coe_lt_top _

lemma T_E_finite_avoiding (M : Model V) : ∀ᵐ x ∂avoidingLaw M, T_E M x < ⊤ := by
  filter_upwards [avoidingLaw_terminal M] with x hx
  rw [T_E_eq_length M x hx]
  exact WithTop.coe_lt_top _

lemma before_threshold_iff_mem (M : Model V) (x : Timeline V)
    (ht : terminal M x) (hne : T_O M x ≠ T_E M x) :
    T_O M x < T_E M x ↔ M.outcome ∈ x := by
  rw [T_E_eq_length M x ht] at *
  by_cases ho : M.outcome ∈ x
  · have hi : x.idxOf M.outcome + 1 ≤ x.length := Nat.succ_le_of_lt (List.idxOf_lt_length_iff.mpr ho)
    have hle : T_O M x ≤ (x.length : ℕ∞) := by
      rw [T_O, if_pos ho]
      exact_mod_cast hi
    exact iff_of_true (lt_of_le_of_ne hle hne) ho
  · simp [T_O, ho]

lemma targetProbability_eq (M : Model V)
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) :
    targetProbability M = eventProbability M := by
  unfold targetProbability eventProbability
  congr 1
  apply measure_congr
  filter_upwards [originalLaw_terminal M, hne] with x ht hx
  exact propext (before_threshold_iff_mem M x ht hx)

lemma M₀_eq_monteCarlo_ae [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) (n : ℕ) :
    M₀ M n =ᵐ[iidLaw (originalLaw M) n] monteCarloEstimator M n := by
  have hsingle : (fun x => if T_O M x < T_E M x then (1 : ℝ) else 0) =ᵐ[originalLaw M]
      monteCarloScore M := by
    filter_upwards [originalLaw_terminal M, hne] with x ht hx
    simp only [monteCarloScore, before_threshold_iff_mem M x ht hx]
  have hcoords : ∀ᵐ xs ∂iidLaw (originalLaw M) n, ∀ i, 
      (if T_O M (xs i) < T_E M (xs i) then (1 : ℝ) else 0) = monteCarloScore M (xs i) := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => originalLaw M) i).quasiMeasurePreserving.ae hsingle
  filter_upwards [hcoords] with xs hx
  unfold M₀ monteCarloEstimator
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : T_O M (xs i) < T_E M (xs i) <;> simpa [hb] using hx i

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace FormalizedScopeReach
attribute [local instance] Classical.propDecidable
variable {V : Type}

instance trialListLaw_probability (M : Model V) (x : Timeline V) :
    IsProbabilityMeasure (trialListLaw M x) := by
  unfold trialListLaw
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

instance poolTrialLaw_probability (M : Model V) {n : ℕ} (xs : Fin n → Timeline V) :
    IsProbabilityMeasure (poolTrialLaw M xs) := by unfold poolTrialLaw; infer_instance

instance twoStageLaw_probability [Countable V] (M : Model V)
    [IsProbabilityMeasure (avoidingLaw M)] (n : ℕ) : IsProbabilityMeasure (twoStageLaw M n) := by
  have hw : (∑' xs : Fin n → Timeline V, (iidLaw (avoidingLaw M) n) {xs}) = 1 := by
    have h := congrArg (fun μ : Measure (Fin n → Timeline V) => μ Set.univ)
      (Measure.sum_smul_dirac (iidLaw (avoidingLaw M) n))
    simpa only [Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one] using h
  constructor
  rw [twoStageLaw, Measure.sum_apply _ MeasurableSet.univ]
  calc
    _ = ∑' xs : Fin n → Timeline V, (iidLaw (avoidingLaw M) n) {xs} := by
      apply tsum_congr
      intro xs
      rw [Measure.smul_apply, Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
      simp
    _ = 1 := hw

lemma trialList_mean (M : Model V) (x : Timeline V) :
    (∫ cs, if true ∈ cs then (1 : ℝ) else 0 ∂trialListLaw M x) = reachScore M x := by
  rw [trialListLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simpa only [List.mem_ofFn, trialSuccess_eq] using trialSuccess_mean M x

lemma indicatorList_integrable (M : Model V) (x : Timeline V) :
    Integrable (fun cs : List Bool => if true ∈ cs then (1 : ℝ) else 0) (trialListLaw M x) := by
  apply (memLp_of_bounded (a := 0) (b := 1) _ (measurable_of_countable _).aestronglyMeasurable 1).integrable (by simp)
  exact ae_of_all _ (fun cs => by split_ifs <;> norm_num)

lemma poolTrial_mean (M : Model V) {n : ℕ} (xs : Fin n → Timeline V) :
    (∫ cs, trialMean n (xs, cs) ∂poolTrialLaw M xs) = reachEstimator M n xs := by
  unfold trialMean poolTrialLaw reachEstimator
  rw [integral_div, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_comp_eval (μ := fun j : Fin n => trialListLaw M (xs j)) (i := i)
      (f := fun cs : List Bool => if true ∈ cs then (1 : ℝ) else 0)
      (measurable_of_countable _).aestronglyMeasurable]
    exact trialList_mean M (xs i)
  · intro i hi
    exact integrable_comp_eval (μ := fun j : Fin n => trialListLaw M (xs j)) (i := i)
      (indicatorList_integrable M (xs i))

lemma trialMean_bounds {n : ℕ} (hn : 0 < n)
    (z : (Fin n → Timeline V) × (Fin n → List Bool)) :
    0 ≤ trialMean n z ∧ trialMean n z ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => by split_ifs <;> norm_num)) hn'.le
  · unfold trialMean
    rw [div_le_iff₀ hn']
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (if true ∈ z.2 i then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)

lemma reachEstimator_bounds (M : Model V) {n : ℕ} (hn : 0 < n) (xs : Fin n → Timeline V) :
    0 ≤ reachEstimator M n xs ∧ reachEstimator M n xs ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => reachScore_nonneg M _)) hn'.le
  · unfold reachEstimator
    rw [div_le_iff₀ hn']
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => reachScore_le_one M (xs i))

lemma twoStage_integral [Countable V] (M : Model V)
    [IsProbabilityMeasure (avoidingLaw M)] (n : ℕ)
    (f : (Fin n → Timeline V) × (Fin n → List Bool) → ℝ)
    (hf : Integrable f (twoStageLaw M n)) :
    (∫ z, f z ∂twoStageLaw M n) =
      ∑' xs : Fin n → Timeline V, ((iidLaw (avoidingLaw M) n) {xs}).toReal *
        ∫ cs, f (xs, cs) ∂poolTrialLaw M xs := by
  rw [twoStageLaw, integral_sum_measure hf]
  apply tsum_congr
  intro xs
  rw [integral_smul_measure, integral_map (measurable_of_countable (fun cs : Fin n → List Bool => (xs, cs))).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  rfl

end FormalizedScopeReach


open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
namespace FormalizedScopeReach
variable {V : Type}

lemma twoStage_trialMean_integral [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (n : ℕ) (hn : 0 < n) :
    (∫ z, trialMean n z ∂twoStageLaw M n) = eventProbability M := by
  have hf : Integrable (trialMean (V := V) n) (twoStageLaw M n) := by
    exact (memLp_of_bounded (ae_of_all _ (trialMean_bounds hn))
      (measurable_of_countable _).aestronglyMeasurable 1).integrable (by simp)
  have hi := (reachScore_memLp M (avoidingLaw M)).integrable (by norm_num)
  have hg : Integrable (reachEstimator M n) (iidLaw (avoidingLaw M) n) :=
    sampleMean_integrable hi n
  rw [twoStage_integral M n _ hf]
  simp only [poolTrial_mean]
  calc
    _ = ∫ xs, reachEstimator M n xs ∂iidLaw (avoidingLaw M) n := by
      rw [integral_countable hg]
      rfl
    _ = eventProbability M := (sampleMean_integral hi n hn).trans (reachScore_integral M)

end FormalizedScopeReach

open FormalizedScopeReach

theorem solution {V : Type} [Countable V] (M : Model V)
    [IsProbabilityMeasure (originalLaw M)] [IsProbabilityMeasure (avoidingLaw M)]
    (hne : ∀ᵐ x ∂originalLaw M, T_O M x ≠ T_E M x) :
    originalLaw M {x | T_O M x < T_E M x} =
      twoStageLaw M 1 {z | true ∈ z.2 0} := by
  have he := twoStage_trialMean_integral M 1 (by decide)
  have hb : trialMean (V := V) 1 =
      Set.indicator {z : (Fin 1 → Timeline V) × (Fin 1 → List Bool) | true ∈ z.2 0}
        (fun _ => (1 : ℝ)) := by
    classical
    funext z
    have hconst : ∀ i : Fin 1, z.2 i = z.2 0 := fun i => congrArg z.2 (Subsingleton.elim i 0)
    simp only [trialMean, hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Nat.cast_one, one_smul, div_one, Set.indicator, Set.mem_ofPred_eq]
  rw [hb] at he
  have hi := integral_indicator_one (μ := twoStageLaw M 1)
    (s := {z : (Fin 1 → Timeline V) × (Fin 1 → List Bool) | true ∈ z.2 0})
    (Set.to_countable _ |>.measurableSet)
  have he' : (twoStageLaw M 1).real {z | true ∈ z.2 0} = eventProbability M := by
    calc
      _ = ∫ z, Set.indicator {z : (Fin 1 → Timeline V) × (Fin 1 → List Bool) | true ∈ z.2 0}
          (fun _ => (1 : ℝ)) z ∂twoStageLaw M 1 := by
        rw [← hi]
        apply integral_congr_ae
        exact ae_of_all _ (fun z => rfl)
      _ = eventProbability M := he
  have heq : ((originalLaw M) {x | T_O M x < T_E M x}).toReal =
      ((twoStageLaw M 1) {z | true ∈ z.2 0}).toReal :=
    (targetProbability_eq M hne).trans he'.symm
  calc
    _ = ENNReal.ofReal (((originalLaw M) {x | T_O M x < T_E M x}).toReal) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal heq
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
