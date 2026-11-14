-- Prove2me | solution 1 for BilateralProfit.claim_4_10
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T13:40:27.45212+00:00
-- url     : https://prove2.me/submissions/ecf11c24-17e1-4f69-9126-390a090f90a1

import Definitions.Def_BilateralProfit_QueryRoutine
import Mathlib

namespace BilateralProfit.QTree

open MeasureTheory

variable {Q Out Out' : Type} [DecidableEq Q]

lemma prob_mono_event (obs : Q → ℕ → Measure ℝ) (R : QTree Q Out)
    {E F : Out → Prop} (hEF : ∀ o, E o → F o) (cnt : Q → ℕ) :
    R.prob obs E cnt ≤ R.prob obs F cnt := by
  induction R generalizing cnt with
  | done o =>
      classical
      simp only [prob]
      split_ifs with hE hF <;> simp_all
  | query q k ih =>
      exact lintegral_mono (fun r => ih r _)

lemma prob_le_one_of_allQueries (obs : Q → ℕ → Measure ℝ) (R : QTree Q Out)
    (p : Q → Prop) (hR : R.AllQueries p)
    (hobs : ∀ q, p q → ∀ n, IsProbabilityMeasure (obs q n))
    (E : Out → Prop) (cnt : Q → ℕ) : R.prob obs E cnt ≤ 1 := by
  induction R generalizing cnt with
  | done o =>
      classical
      simp only [prob]
      split_ifs <;> simp
  | query q k ih =>
      let := hobs q hR.1 (cnt q)
      calc
        _ ≤ ∫⁻ _ : ℝ, (1 : ENNReal) ∂obs q (cnt q) :=
          lintegral_mono (fun r => ih r (hR.2 r) _)
        _ = 1 := by simp

lemma prob_true_of_allQueries (obs : Q → ℕ → Measure ℝ) (R : QTree Q Out)
    (p : Q → Prop) (hR : R.AllQueries p)
    (hobs : ∀ q, p q → ∀ n, IsProbabilityMeasure (obs q n))
    (cnt : Q → ℕ) : R.prob obs (fun _ => True) cnt = 1 := by
  induction R generalizing cnt with
  | done o => simp [prob]
  | query q k ih =>
      let := hobs q hR.1 (cnt q)
      simp only [prob, ih _ (hR.2 _)]; simp

def bind (R : QTree Q Out) (f : Out → QTree Q Out') : QTree Q Out' :=
  match R with
  | .done o => f o
  | .query q k => .query q (fun r => bind (k r) f)

lemma allQueries_bind (R : QTree Q Out) (f : Out → QTree Q Out')
    (p : Q → Prop) (hR : R.AllQueries p) (hf : ∀ o, (f o).AllQueries p) :
    (bind R f).AllQueries p := by
  induction R with
  | done o => exact hf o
  | query q k ih => exact ⟨hR.1, fun r => ih r (hR.2 r)⟩

lemma queriesAtMost_mono (R : QTree Q Out) {m n : ℕ}
    (hR : R.QueriesAtMost m) (hmn : m ≤ n) : R.QueriesAtMost n := by
  induction R generalizing m n with
  | done o => trivial
  | query q k ih =>
      cases m with
      | zero => exact False.elim hR
      | succ m =>
          cases n with
          | zero => omega
          | succ n => exact fun r => ih r (hR r) (by omega)

lemma queriesAtMost_bind (R : QTree Q Out) (f : Out → QTree Q Out')
    {m n : ℕ} (hR : R.QueriesAtMost m) (hf : ∀ o, (f o).QueriesAtMost n) :
    (bind R f).QueriesAtMost (m + n) := by
  induction R generalizing m with
  | done o => exact queriesAtMost_mono _ (hf o) (by omega)
  | query q k ih =>
      cases m with
      | zero => exact False.elim hR
      | succ m =>
          simpa only [bind, Nat.succ_add, QueriesAtMost] using fun r => ih r (hR r)

lemma prob_bind_lower (obs : Q → ℕ → Measure ℝ) (R : QTree Q Out)
    (f : Out → QTree Q Out') (F : Out → Prop) (E : Out' → Prop)
    (a : ENNReal)
    (hf : ∀ o, F o → ∀ cnt, a ≤ (f o).prob obs E cnt) (cnt : Q → ℕ) :
    a * R.prob obs F cnt ≤ (bind R f).prob obs E cnt := by
  induction R generalizing cnt with
  | done o =>
      classical
      simp only [bind, prob]
      split_ifs with hF
      · simpa using hf o hF cnt
      · simp
  | query q k ih =>
      exact (lintegral_const_mul_le _ _).trans (lintegral_mono (fun r => ih r _))

/-- Every path on which each response is accurate has a valid output. -/
def Robust (good : Q → ℝ → Prop) (E : Out → Prop) : QTree Q Out → Prop
  | .done o => E o
  | .query q k => ∀ r, good q r → Robust good E (k r)

/-- Replace each high-level response by the output of a low-level query block. -/
def liftBlocks (B : Q → QTree Q ℝ) : QTree Q Out → QTree Q Out
  | .done o => .done o
  | .query q k => bind (B q) (fun r => liftBlocks B (k r))

lemma allQueries_liftBlocks (B : Q → QTree Q ℝ) (R : QTree Q Out)
    (p : Q → Prop) (hR : R.AllQueries p)
    (hB : ∀ q, p q → (B q).AllQueries p) : (liftBlocks B R).AllQueries p := by
  induction R with
  | done o => trivial
  | query q k ih =>
      exact allQueries_bind _ _ _ (hB q hR.1) (fun r => ih r (hR.2 r))

lemma queriesAtMost_liftBlocks (B : Q → QTree Q ℝ) (R : QTree Q Out)
    (p : Q → Prop) (hR : R.AllQueries p) {m n : ℕ}
    (hM : R.QueriesAtMost m) (hB : ∀ q, p q → (B q).QueriesAtMost n) :
    (liftBlocks B R).QueriesAtMost (m * n) := by
  induction R generalizing m with
  | done o => trivial
  | query q k ih =>
      cases m with
      | zero => exact False.elim hM
      | succ m =>
          have h := queriesAtMost_bind (B q) (fun r => liftBlocks B (k r))
            (hB q hR.1) (fun r => ih r (hR.2 r) (hM r))
          simpa only [liftBlocks, Nat.succ_mul, Nat.add_comm] using h

lemma prob_liftBlocks_pow_lower (obs : Q → ℕ → Measure ℝ)
    (B : Q → QTree Q ℝ) (R : QTree Q Out)
    (p : Q → Prop) (good : Q → ℝ → Prop) (E : Out → Prop)
    (hR : R.AllQueries p) (hrobust : R.Robust good E)
    {m : ℕ} (hM : R.QueriesAtMost m) {a : ENNReal} (ha : a ≤ 1)
    (hB : ∀ q, p q → ∀ cnt, a ≤ (B q).prob obs (good q) cnt)
    (cnt : Q → ℕ) : a ^ m ≤ (liftBlocks B R).prob obs E cnt := by
  induction R generalizing m cnt with
  | done o =>
      classical
      change E o at hrobust
      simpa only [liftBlocks, prob, if_pos hrobust] using (pow_le_one₀ (zero_le : 0 ≤ a) ha : a ^ m ≤ 1)
  | query q k ih =>
      cases m with
      | zero => exact False.elim hM
      | succ m =>
          calc
            a ^ (m + 1) = a ^ m * a := pow_succ a m
            _ ≤ a ^ m * (B q).prob obs (good q) cnt := by gcongr; exact hB q hR.1 cnt
            _ ≤ (liftBlocks B (.query q k)).prob obs E cnt := by
                exact prob_bind_lower obs (B q) (fun r => liftBlocks B (k r))
                  (good q) E (a ^ m) (fun r hr c => ih r (hR.2 r) (hrobust r hr) (hM r) c) cnt

lemma prob_liftBlocks_lower (obs : Q → ℕ → Measure ℝ)
    (B : Q → QTree Q ℝ) (R : QTree Q Out)
    (p : Q → Prop) (good : Q → ℝ → Prop) (E : Out → Prop)
    (hR : R.AllQueries p) (hrobust : R.Robust good E)
    {m : ℕ} (hM : R.QueriesAtMost m) {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hB : ∀ q, p q → ∀ cnt, ENNReal.ofReal (1 - η) ≤ (B q).prob obs (good q) cnt)
    (cnt : Q → ℕ) : ENNReal.ofReal (1 - m * η) ≤ (liftBlocks B R).prob obs E cnt := by
  have hreal : (1 : ℝ) - m * η ≤ (1 - η) ^ m := by
    simpa only [mul_neg, sub_eq_add_neg] using one_add_mul_le_pow (a := -η) (by linarith) m
  calc
    _ ≤ ENNReal.ofReal ((1 - η) ^ m) := ENNReal.ofReal_le_ofReal hreal
    _ = (ENNReal.ofReal (1 - η)) ^ m := ENNReal.ofReal_pow (by linarith) _
    _ ≤ _ := prob_liftBlocks_pow_lower obs B R p good E hR hrobust hM
      (by simpa using ENNReal.ofReal_le_ofReal (show 1 - η ≤ (1 : ℝ) by linarith)) hB cnt

lemma prob_bind_done (obs : Q → ℕ → Measure ℝ) (R : QTree Q Out)
    (f : Out → Out') (E : Out' → Prop) (cnt : Q → ℕ) :
    (bind R (fun o => .done (f o))).prob obs E cnt = R.prob obs (fun o => E (f o)) cnt := by
  induction R generalizing cnt with
  | done o => rfl
  | query q k ih => exact lintegral_congr (fun r => ih r _)

/-- Obtain a fixed-length vector of fresh responses to one query. -/
def sampleVec (q : Q) : (n : ℕ) → QTree Q (Fin n → ℝ)
  | 0 => .done (fun i => Fin.elim0 i)
  | n + 1 => .query q (fun r => bind (sampleVec q n) (fun v => .done (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) r v)))

/-- Empirical mean of a fixed number of fresh responses to one query. -/
noncomputable def sampleMeanBlock (q : Q) (n : ℕ) : QTree Q ℝ :=
  bind (sampleVec q n) (fun v => .done ((∑ j, v j) / (n : ℝ)))

lemma queriesAtMost_sampleVec (q : Q) (n : ℕ) : (sampleVec q n).QueriesAtMost n := by
  induction n with
  | zero => trivial
  | succ n ih =>
      intro r
      simpa using queriesAtMost_bind (sampleVec q n) (fun v => .done (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) r v)) ih
        (n := 0) (fun _ => trivial)

lemma allQueries_sampleVec (q : Q) (n : ℕ) (p : Q → Prop) (hq : p q) :
    (sampleVec q n).AllQueries p := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hq, fun _ => allQueries_bind _ _ _ ih (fun _ => trivial)⟩

lemma queriesAtMost_sampleMeanBlock (q : Q) (n : ℕ) :
    (sampleMeanBlock q n).QueriesAtMost n := by
  simpa [sampleMeanBlock] using queriesAtMost_bind (sampleVec q n)
    (fun v => .done ((∑ j, v j) / (n : ℝ))) (queriesAtMost_sampleVec q n)
    (n := 0) (fun _ => trivial)

lemma allQueries_sampleMeanBlock (q : Q) (n : ℕ) (p : Q → Prop) (hq : p q) :
    (sampleMeanBlock q n).AllQueries p :=
  allQueries_bind _ _ _ (allQueries_sampleVec q n p hq) (fun _ => trivial)

lemma measurable_cons {n : ℕ} :
    Measurable (fun x : ℝ × (Fin n → ℝ) => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) x.1 x.2) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero', Fin.zero_succAbove] using
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm.measurable

lemma pi_measure_cons {n : ℕ} (μ : Fin (n + 1) → Measure ℝ)
    [∀ j, SigmaFinite (μ j)] (E : (Fin (n + 1) → ℝ) → Prop)
    (hE : MeasurableSet {v | E v}) :
    Measure.pi μ {v | E v} =
      ∫⁻ r, Measure.pi (fun j : Fin n => μ j.succ) {v | E (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) r v)} ∂μ 0 := by
  have hpres := (measurePreserving_piFinSuccAbove μ 0).symm
  have hp := hpres.measure_preimage hE.nullMeasurableSet
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_zero', Fin.zero_succAbove] at hp
  rw [← hp, Measure.prod_apply (hE.preimage measurable_cons)]
  rfl

lemma prob_sampleVec (obs : Q → ℕ → Measure ℝ) (q : Q)
    (hobs : ∀ j, IsProbabilityMeasure (obs q j)) (n : ℕ)
    (E : (Fin n → ℝ) → Prop) (hE : MeasurableSet {v | E v}) (cnt : Q → ℕ) :
    (sampleVec q n).prob obs E cnt =
      Measure.pi (fun j : Fin n => obs q (cnt q + j)) {v | E v} := by
  induction n generalizing cnt with
  | zero =>
      classical
      rw [Measure.pi_of_empty (fun j : Fin 0 => obs q (cnt q + j)) (fun i => Fin.elim0 i)]
      simp [sampleVec, prob, Measure.dirac_apply' _ hE, Set.indicator_apply]
  | succ n ih =>
      let (j : Fin (n + 1)) : IsProbabilityMeasure (obs q (cnt q + j)) := hobs _
      rw [pi_measure_cons _ _ hE]
      simp only [sampleVec, prob]
      apply lintegral_congr
      intro r
      rw [prob_bind_done, ih (fun v => E (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) r v))
        (hE.preimage (measurable_cons.comp (measurable_const.prodMk measurable_id)))]
      congr 1
      congr 1
      funext j
      simp only [Function.update_self, Fin.val_succ]
      congr 1
      omega

lemma prob_sampleMeanBlock (obs : Q → ℕ → Measure ℝ) (q : Q)
    (hobs : ∀ j, IsProbabilityMeasure (obs q j)) (n : ℕ)
    (m ε : ℝ) (cnt : Q → ℕ) :
    (sampleMeanBlock q n).prob obs (fun r => |r - m| ≤ ε) cnt =
      Measure.pi (fun j : Fin n => obs q (cnt q + j))
        {v | |(∑ j, v j) / (n : ℝ) - m| ≤ ε} := by
  rw [sampleMeanBlock, prob_bind_done]
  apply prob_sampleVec obs q hobs n _ _ cnt
  exact measurableSet_le (by fun_prop) measurable_const

/-- A deterministic bound on cost along paths whose observations satisfy `good`. -/
def GoodCost (good : Q → ℝ → Prop) : QTree Q Out → ℝ → Prop
  | .done _, b => 0 ≤ b
  | .query q k, b => 1 ≤ b ∧ ∀ r, good q r → GoodCost good (k r) (b - 1)

lemma goodCost_nonneg (good : Q → ℝ → Prop) (R : QTree Q Out)
    {b : ℝ} (h : R.GoodCost good b) : 0 ≤ b := by
  cases R with
  | done o => exact h
  | query q k => exact zero_le_one.trans h.1

lemma goodCost_mono (good : Q → ℝ → Prop) (R : QTree Q Out)
    {b c : ℝ} (h : R.GoodCost good b) (hbc : b ≤ c) : R.GoodCost good c := by
  induction R generalizing b c with
  | done o => exact h.trans hbc
  | query q k ih =>
      exact ⟨h.1.trans hbc, fun r hr => ih r (h.2 r hr) (by linarith)⟩

lemma goodCost_bind (good : Q → ℝ → Prop) (R : QTree Q Out)
    (f : Out → QTree Q Out') (F : Out → Prop) {b c : ℝ}
    (hR : R.GoodCost good b) (hrobust : R.Robust good F) (hc : 0 ≤ c)
    (hf : ∀ o, F o → (f o).GoodCost good c) : (bind R f).GoodCost good (b + c) := by
  induction R generalizing b with
  | done o =>
      exact goodCost_mono good _ (hf o hrobust) (by change 0 ≤ b at hR; linarith)
  | query q k ih =>
      refine ⟨by have := hR.1; linarith, fun r hr => ?_⟩
      have h := ih r (hR.2 r hr) (hrobust r hr)
      convert h using 1; ring

/-- A natural-number bound on the number of queries along good-response paths. -/
def GoodQueriesAtMost (good : Q → ℝ → Prop) : QTree Q Out → ℕ → Prop
  | .done _, _ => True
  | .query _ _, 0 => False
  | .query q k, n + 1 => ∀ r, good q r → GoodQueriesAtMost good (k r) n

lemma goodQueriesAtMost_of_goodCost (good : Q → ℝ → Prop) (R : QTree Q Out)
    {b : ℝ} {n : ℕ} (hR : R.GoodCost good b) (hb : b < (n : ℝ) + 1) :
    R.GoodQueriesAtMost good n := by
  induction n generalizing R b with
  | zero =>
      cases R with
      | done o => trivial
      | query q k => have := hR.1; simp only [Nat.cast_zero, zero_add] at hb; linarith
  | succ n ih =>
      cases R with
      | done o => trivial
      | query q k =>
          intro r hr
          apply ih _ (hR.2 r hr)
          simp only [Nat.cast_add, Nat.cast_one] at hb
          linarith

lemma goodQueriesAtMost_floor (good : Q → ℝ → Prop) (R : QTree Q Out)
    {b : ℝ} (hR : R.GoodCost good b) : R.GoodQueriesAtMost good (Nat.floor b) :=
  goodQueriesAtMost_of_goodCost good R hR (Nat.lt_floor_add_one b)

/-- Halt after a prescribed number of high-level queries on every response path. -/
def truncate : ℕ → QTree Q Out → Out → QTree Q Out
  | _, .done o, _ => .done o
  | 0, .query _ _, fallback => .done fallback
  | n + 1, .query q k, fallback => .query q (fun r => truncate n (k r) fallback)

lemma queriesAtMost_truncate (n : ℕ) (R : QTree Q Out) (fallback : Out) :
    (truncate n R fallback).QueriesAtMost n := by
  induction n generalizing R with
  | zero => cases R <;> trivial
  | succ n ih =>
      cases R with
      | done o => trivial
      | query q k => exact fun r => ih (k r)

lemma allQueries_truncate (n : ℕ) (R : QTree Q Out) (fallback : Out)
    (p : Q → Prop) (hR : R.AllQueries p) : (truncate n R fallback).AllQueries p := by
  induction n generalizing R with
  | zero => cases R <;> trivial
  | succ n ih =>
      cases R with
      | done o => trivial
      | query q k => exact ⟨hR.1, fun r => ih _ (hR.2 r)⟩

lemma queriesAtMost_truncate_of_queriesAtMost (n : ℕ) (R : QTree Q Out) (fallback : Out)
    {m : ℕ} (hR : R.QueriesAtMost m) : (truncate n R fallback).QueriesAtMost m := by
  induction n generalizing R m with
  | zero => cases R <;> trivial
  | succ n ih =>
      cases R with
      | done o => trivial
      | query q k =>
          cases m with
          | zero => exact False.elim hR
          | succ m => exact fun r => ih _ (hR r)

lemma robust_truncate (good : Q → ℝ → Prop) (E : Out → Prop)
    (n : ℕ) (R : QTree Q Out) (fallback : Out)
    (hR : R.Robust good E) (hN : R.GoodQueriesAtMost good n) :
    (truncate n R fallback).Robust good E := by
  induction n generalizing R with
  | zero =>
      cases R with
      | done o => exact hR
      | query q k => exact False.elim hN
  | succ n ih =>
      cases R with
      | done o => exact hR
      | query q k => exact fun r hr => ih _ (hR r hr) (hN r hr)

lemma robust_truncate_of_goodCost (good : Q → ℝ → Prop) (E : Out → Prop)
    (R : QTree Q Out) (fallback : Out) {b : ℝ}
    (hR : R.Robust good E) (hB : R.GoodCost good b) :
    (truncate (Nat.floor b) R fallback).Robust good E :=
  robust_truncate good E _ R fallback hR (goodQueriesAtMost_floor good R hB)

end BilateralProfit.QTree

namespace BilateralProfit

open MeasureTheory ProbabilityTheory

/-- The sample mean of `n` observations. -/
noncomputable def sampleMean {Ω : Type*} (n : ℕ) (X : Fin n → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ j, X j ω) / n

/-- The two-sided concentration estimate used in Claim 4.10. The observations need not
have identical distributions. The interval containing them has length four. -/
theorem sampleMean_deviation_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (m c α : ℝ) (hα : 0 ≤ α)
    (hX : ∀ j, AEMeasurable (X j) μ)
    (hind : iIndepFun X μ)
    (hb : ∀ j, ∀ᵐ ω ∂μ, X j ω ∈ Set.Icc c (c + 4))
    (hm : ∀ j, ∫ ω, X j ω ∂μ = m) :
    μ.real {ω | α / 8 < |sampleMean n X ω - m|} ≤
      2 * Real.exp (-(n : ℝ) * α ^ 2 / 512) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsub (j : Fin n) :
      HasSubgaussianMGF (fun ω => X j ω - m) 4 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc (hX j) (hb j)
    norm_num [hm j, Real.nnnorm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at h ⊢
    exact h
  have hind' : iIndepFun (fun j ω => X j ω - m) μ := by
    exact hind.comp (fun _ x => x - m) (fun _ => by fun_prop)
  have hs : HasSubgaussianMGF (fun ω => ∑ j, (X j ω - m)) (n * 4) μ := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hind'
      (s := Finset.univ) (c := fun _ => 4) (fun j _ => hsub j)
  have hε : 0 ≤ (n : ℝ) * α / 8 := by positivity
  have hplus := hs.measure_ge_le hε
  have hminus := hs.neg.measure_ge_le hε
  have hexp : -((n : ℝ) * α / 8) ^ 2 / (2 * ((n : ℝ) * 4)) =
      -(n : ℝ) * α ^ 2 / 512 := by
    field_simp
    ring
  simp only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat, hexp] at hplus hminus
  have hsum (ω : Ω) : (∑ j, (X j ω - m)) =
      (n : ℝ) * (sampleMean n X ω - m) := by
    simp [sampleMean, Finset.sum_sub_distrib]
    field_simp
  have hsubset : {ω | α / 8 < |sampleMean n X ω - m|} ⊆
      {ω | (n : ℝ) * α / 8 ≤ ∑ j, (X j ω - m)} ∪
      {ω | (n : ℝ) * α / 8 ≤ -(∑ j, (X j ω - m))} := by
    intro ω hω
    change α / 8 < |sampleMean n X ω - m| at hω
    rcases (lt_abs.mp hω) with hp | hm'
    · left
      change (n : ℝ) * α / 8 ≤ ∑ j, (X j ω - m)
      rw [hsum]
      nlinarith
    · right
      change (n : ℝ) * α / 8 ≤ -(∑ j, (X j ω - m))
      rw [hsum]
      nlinarith
  calc
    μ.real {ω | α / 8 < |sampleMean n X ω - m|}
      ≤ μ.real ({ω | (n : ℝ) * α / 8 ≤ ∑ j, (X j ω - m)} ∪
          {ω | (n : ℝ) * α / 8 ≤ -(∑ j, (X j ω - m))}) := measureReal_mono hsubset
    _ ≤ μ.real {ω | (n : ℝ) * α / 8 ≤ ∑ j, (X j ω - m)} +
          μ.real {ω | (n : ℝ) * α / 8 ≤ -(∑ j, (X j ω - m))} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512) := by
      simp only [Pi.neg_apply] at hminus
      linarith

/-- The concentration bound on a finite observation tape. This is the product-law
form used when `obs j` is the law of the next unused observation at one query. -/
theorem product_sampleMean_good_probability (n : ℕ) (hn : 0 < n)
    (obs : Fin n → Measure ℝ) [∀ j, IsProbabilityMeasure (obs j)]
    (m c α : ℝ) (hα : 0 ≤ α)
    (hb : ∀ j, obs j (Set.Icc c (c + 4))ᶜ = 0)
    (hm : ∀ j, ∫ r, r ∂(obs j) = m) :
    ENNReal.ofReal (1 - 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512)) ≤
      Measure.pi obs {ω : Fin n → ℝ | |(∑ j, ω j) / (n : ℝ) - m| ≤ α / 8} := by
  have hbounded (j : Fin n) : ∀ᵐ ω ∂Measure.pi obs, ω j ∈ Set.Icc c (c + 4) := by
    apply (measurePreserving_eval obs j).quasiMeasurePreserving.ae
    exact ae_iff.mpr (hb j)
  have hmean (j : Fin n) : ∫ ω : Fin n → ℝ, ω j ∂Measure.pi obs = m := by
    rw [integral_eval, hm]
  have hind : iIndepFun (fun j (ω : Fin n → ℝ) => ω j) (Measure.pi obs) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hbound := sampleMean_deviation_bound (Measure.pi obs) n hn
    (fun j ω => ω j) m c α hα (fun j => (measurable_pi_apply j).aemeasurable)
    hind hbounded hmean
  have hmeas : MeasurableSet
      {ω : Fin n → ℝ | α / 8 < |(∑ j, ω j) / (n : ℝ) - m|} := by
    apply measurableSet_lt measurable_const
    fun_prop
  have heq : {ω : Fin n → ℝ | α / 8 < |(∑ j, ω j) / (n : ℝ) - m|}ᶜ =
      {ω : Fin n → ℝ | |(∑ j, ω j) / (n : ℝ) - m| ≤ α / 8} := by
    ext ω
    simp
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
  change _ ≤ (Measure.pi obs).real _
  rw [← heq, probReal_compl_eq_one_sub hmeas]
  change (Measure.pi obs).real
    {ω : Fin n → ℝ | α / 8 < |(∑ j, ω j) / (n : ℝ) - m|} ≤ _ at hbound
  linarith

/-- The union bound for all first-`n` sample means in a finite collection of streams.
Only independence within each stream is required. -/
theorem finite_sampleMeans_clean_probability {Q Ω : Type*} [Fintype Q]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X : Q → Fin n → Ω → ℝ)
    (m : Q → ℝ) (c α : ℝ) (hα : 0 ≤ α)
    (hX : ∀ q j, Measurable (X q j))
    (hind : ∀ q, iIndepFun (X q) μ)
    (hb : ∀ q j, ∀ᵐ ω ∂μ, X q j ω ∈ Set.Icc c (c + 4))
    (hm : ∀ q j, ∫ ω, X q j ω ∂μ = m q) :
    ENNReal.ofReal (1 - (Fintype.card Q : ℝ) *
      (2 * Real.exp (-(n : ℝ) * α ^ 2 / 512))) ≤
      μ {ω | ∀ q, |sampleMean n (X q) ω - m q| ≤ α / 8} := by
  classical
  let bad : Q → Set Ω := fun q => {ω | α / 8 < |sampleMean n (X q) ω - m q|}
  have hbnd (q : Q) : μ.real (bad q) ≤ 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512) :=
    sampleMean_deviation_bound μ n hn (X q) (m q) c α hα
      (fun j => (hX q j).aemeasurable) (hind q) (hb q) (hm q)
  have hsum : μ.real (⋃ q, bad q) ≤
      (Fintype.card Q : ℝ) * (2 * Real.exp (-(n : ℝ) * α ^ 2 / 512)) := by
    calc
      μ.real (⋃ q, bad q) ≤ ∑ q, μ.real (bad q) := measureReal_iUnion_fintype_le bad
      _ ≤ ∑ _q : Q, 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512) :=
        Finset.sum_le_sum (fun q _ => hbnd q)
      _ = _ := by simp
  have hmeas : MeasurableSet (⋃ q, bad q) := by
    apply MeasurableSet.iUnion
    intro q
    apply measurableSet_lt measurable_const
    dsimp [bad, sampleMean]
    fun_prop
  have heq : (⋃ q, bad q)ᶜ =
      {ω | ∀ q, |sampleMean n (X q) ω - m q| ≤ α / 8} := by
    ext ω
    simp [bad]
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
  change _ ≤ μ.real _
  rw [← heq, probReal_compl_eq_one_sub hmeas]
  linarith

/-- The elementary sample-size calculation accompanying Hoeffding's inequality.
`M` can be any positive upper bound on the number of estimated points. -/
theorem hoeffding_failure_bound_of_sample_size (M α δ : ℝ) (n : ℕ)
    (hM : 0 < M) (hα : 0 < α) (hδ : 0 < δ)
    (hn : 512 * Real.log (2 * M / δ) / α ^ 2 ≤ n) :
    M * (2 * Real.exp (-(n : ℝ) * α ^ 2 / 512)) ≤ δ := by
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hn' := (div_le_iff₀ hα2).mp hn
  have hexp : -(n : ℝ) * α ^ 2 / 512 ≤ -Real.log (2 * M / δ) := by
    linarith
  have he := Real.exp_le_exp.mpr hexp
  rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 2 * M / δ)] at he
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ M * 2)
  calc
    M * (2 * Real.exp (-(n : ℝ) * α ^ 2 / 512))
      ≤ M * 2 * (2 * M / δ)⁻¹ := by nlinarith [hmul]
    _ = δ := by field_simp

/-- The finite clean event has probability at least `1-δ` at the logarithmic sample size.
For an empty family the same conclusion follows directly without observations. -/
theorem finite_sampleMeans_clean_probability_of_sample_size {Q Ω : Type*} [Fintype Q]
    [Nonempty Q] [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X : Q → Fin n → Ω → ℝ)
    (m : Q → ℝ) (c α δ : ℝ) (hα : 0 < α) (hδ : 0 < δ)
    (hsize : 512 * Real.log (2 * Fintype.card Q / δ) / α ^ 2 ≤ n)
    (hX : ∀ q j, Measurable (X q j))
    (hind : ∀ q, iIndepFun (X q) μ)
    (hb : ∀ q j, ∀ᵐ ω ∂μ, X q j ω ∈ Set.Icc c (c + 4))
    (hm : ∀ q j, ∫ ω, X q j ω ∂μ = m q) :
    ENNReal.ofReal (1 - δ) ≤
      μ {ω | ∀ q, |sampleMean n (X q) ω - m q| ≤ α / 8} := by
  have hc : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hfailure := hoeffding_failure_bound_of_sample_size (Fintype.card Q) α δ n
    hc hα hδ hsize
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
    (finite_sampleMeans_clean_probability μ n hn X m c α hα.le hX hind hb hm)

/-- The simultaneous clean event on a full finite tape of observations indexed by a
query and its observation number. No laws are assumed to be identical. -/
theorem fullTape_clean_probability {Q : Type*} [Fintype Q]
    (n : ℕ) (hn : 0 < n) (obs : Q × Fin n → Measure ℝ)
    [∀ p, IsProbabilityMeasure (obs p)] (m : Q → ℝ) (c α : ℝ) (hα : 0 ≤ α)
    (hb : ∀ p, obs p (Set.Icc c (c + 4))ᶜ = 0)
    (hm : ∀ p, ∫ r, r ∂(obs p) = m p.1) :
    ENNReal.ofReal (1 - (Fintype.card Q : ℝ) *
      (2 * Real.exp (-(n : ℝ) * α ^ 2 / 512))) ≤
      Measure.pi obs {tape : Q × Fin n → ℝ |
        ∀ q, |(∑ j, tape (q, j)) / (n : ℝ) - m q| ≤ α / 8} := by
  have hbounded (q : Q) (j : Fin n) :
      ∀ᵐ tape ∂Measure.pi obs, tape (q, j) ∈ Set.Icc c (c + 4) := by
    apply (measurePreserving_eval obs (q, j)).quasiMeasurePreserving.ae
    exact ae_iff.mpr (hb (q, j))
  have hmean (q : Q) (j : Fin n) :
      ∫ tape : Q × Fin n → ℝ, tape (q, j) ∂Measure.pi obs = m q := by
    rw [integral_eval, hm]
  have hind : iIndepFun (fun p (tape : Q × Fin n → ℝ) => tape p) (Measure.pi obs) := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hindq (q : Q) :
      iIndepFun (fun j (tape : Q × Fin n → ℝ) => tape (q, j)) (Measure.pi obs) := by
    exact hind.precomp (show Function.Injective (fun j : Fin n => (q, j)) from
      fun _ _ h => congrArg Prod.snd h)
  exact finite_sampleMeans_clean_probability (Measure.pi obs) n hn
    (fun q j tape => tape (q, j)) m c α hα (fun q j => measurable_pi_apply (q, j))
    hindq hbounded hmean

/-- The finite-product version of the preceding clean-event estimate at the stated
logarithmic sample size. -/
theorem fullTape_clean_probability_of_sample_size {Q : Type*} [Fintype Q] [Nonempty Q]
    (n : ℕ) (hn : 0 < n) (obs : Q × Fin n → Measure ℝ)
    [∀ p, IsProbabilityMeasure (obs p)] (m : Q → ℝ) (c α δ : ℝ)
    (hα : 0 < α) (hδ : 0 < δ)
    (hsize : 512 * Real.log (2 * Fintype.card Q / δ) / α ^ 2 ≤ n)
    (hb : ∀ p, obs p (Set.Icc c (c + 4))ᶜ = 0)
    (hm : ∀ p, ∫ r, r ∂(obs p) = m p.1) :
    ENNReal.ofReal (1 - δ) ≤
      Measure.pi obs {tape : Q × Fin n → ℝ |
        ∀ q, |(∑ j, tape (q, j)) / (n : ℝ) - m q| ≤ α / 8} := by
  have hc : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
  have hfailure := hoeffding_failure_bound_of_sample_size (Fintype.card Q) α δ n
    hc hα hδ hsize
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
    (fullTape_clean_probability n hn obs m c α hα.le hb hm)

/-- The integer sample count used for each directly estimated point. -/
noncomputable def monotoneSampleCount (M α δ : ℝ) : ℕ :=
  ⌈512 * Real.log (2 * M / δ) / α ^ 2⌉₊

/-- Rounding up the sample count changes its bound by at most a factor of two
throughout the parameter range of Claim 4.10. -/
theorem monotoneSampleCount_bounds (M α δ : ℝ) (hM : 1 ≤ M)
    (hα : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < monotoneSampleCount M α δ ∧
    512 * Real.log (2 * M / δ) / α ^ 2 ≤ (monotoneSampleCount M α δ : ℝ) ∧
    (monotoneSampleCount M α δ : ℝ) ≤ 1024 * Real.log (2 * M / δ) / α ^ 2 := by
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hratio : (2 : ℝ) ≤ 2 * M / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hlog : (1 : ℝ) / 2 ≤ Real.log (2 * M / δ) :=
    hlog2.trans (Real.log_le_log (by norm_num) hratio)
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hraw : 1 ≤ 512 * Real.log (2 * M / δ) / α ^ 2 := by
    apply (le_div_iff₀ hα2).mpr
    nlinarith
  refine ⟨?_, Nat.le_ceil _, ?_⟩
  · exact Nat.one_le_ceil_iff.mpr (by linarith)
  · calc
      (monotoneSampleCount M α δ : ℝ)
        ≤ 512 * Real.log (2 * M / δ) / α ^ 2 + 1 := (Nat.ceil_lt_add_one (by linarith)).le
      _ ≤ 2 * (512 * Real.log (2 * M / δ) / α ^ 2) := by linarith
      _ = 1024 * Real.log (2 * M / δ) / α ^ 2 := by ring

/-- A base-two recursion depth can be bounded using natural logarithms. -/
theorem log2_add_one_le_two_log (L : ℕ) (hL : 0 < L) :
    (Nat.log2 L : ℝ) + 1 ≤ 2 * Real.log (2 * L) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hn := Real.log2_le_logb L
  rw [Real.logb] at hn
  have hn' := (le_div_iff₀ hlog2pos).mp hn
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hLr.ne']
  have hn0 : (0 : ℝ) ≤ Nat.log2 L := by positivity
  nlinarith

/-- A version allowing one additional root level. -/
theorem log2_add_two_le_four_log (L : ℕ) (hL : 0 < L) :
    (Nat.log2 L : ℝ) + 2 ≤ 4 * Real.log (2 * L) := by
  have h := log2_add_one_le_two_log L hL
  have hn0 : (0 : ℝ) ≤ Nat.log2 L := by positivity
  linarith

/-- `log2 L + 1` levels suffice for a binary subdivision of at most `L` points. -/
theorem le_two_pow_log2_add_one (n L : ℕ) (hn : n ≤ L) :
    n ≤ 2 ^ (Nat.log2 L + 1) := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) L
  rw [← Nat.log2_eq_log_two] at h
  exact hn.trans h.le

/-- Multiplying the number of potential mean queries by four is absorbed by a
factor of three in the logarithmic sample bound. -/
theorem log_eight_le_three_log_two (M δ : ℝ) (hM : 1 ≤ M)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    Real.log (8 * M / δ) ≤ 3 * Real.log (2 * M / δ) := by
  have hMpos : 0 < M := by linarith
  have hratio : (2 : ℝ) ≤ 2 * M / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hratio
  have hid : 8 * M / δ = (2 : ℝ) ^ 2 * (2 * M / δ) := by ring
  rw [hid, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  norm_num
  linarith

/-- A deterministic cap for the number of sample means, using a known total
variation bound. -/
noncomputable def monotoneMeanCap (G Y : ℕ) (W α : ℝ) : ℕ :=
  ⌊2 * (G : ℝ) + 16 * W * ((Nat.log2 Y : ℝ) + 1) / α⌋₊

/-- Combining the rounded per-mean sample count with the deterministic cap yields
the asymptotic form asserted in Claim 4.10, with an explicit universal constant. -/
theorem monotone_observation_budget_bound (G Y : ℕ) (hG : 0 < G) (hY : 0 < Y)
    (W α δ : ℝ) (hW : 0 ≤ W) (hα : 0 < α) (hα1 : α < 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ((monotoneMeanCap G Y W α * monotoneSampleCount (4 * G * Y) α δ : ℕ) : ℝ) ≤
      98304 * Real.log (2 * G * Y / δ) / α ^ 2 *
        (G + W / α * Real.log (2 * Y)) := by
  have hGr : (1 : ℝ) ≤ G := by exact_mod_cast hG
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hGY : (1 : ℝ) ≤ (G : ℝ) * Y := by nlinarith
  have hM : (1 : ℝ) ≤ 4 * G * Y := by nlinarith
  have hlogY : 0 ≤ Real.log (2 * Y) := Real.log_nonneg (by nlinarith)
  have hratio : (1 : ℝ) ≤ 2 * G * Y / δ := by
    apply (le_div_iff₀ hδ).mpr
    nlinarith
  have hlog : 0 ≤ Real.log (2 * G * Y / δ) := Real.log_nonneg hratio
  have hα2 : 0 < α ^ 2 := sq_pos_of_pos hα
  have hraw : 0 ≤ 2 * (G : ℝ) + 16 * W * ((Nat.log2 Y : ℝ) + 1) / α := by
    positivity
  have hcap : (monotoneMeanCap G Y W α : ℝ) ≤
      32 * ((G : ℝ) + W / α * Real.log (2 * Y)) := by
    have hf : (monotoneMeanCap G Y W α : ℝ) ≤
        2 * (G : ℝ) + 16 * W * ((Nat.log2 Y : ℝ) + 1) / α := Nat.floor_le hraw
    have hd := log2_add_one_le_two_log Y hY
    have hmul := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 16 * W / α)
    calc
      (monotoneMeanCap G Y W α : ℝ)
        ≤ 2 * (G : ℝ) + 16 * W * ((Nat.log2 Y : ℝ) + 1) / α := hf
      _ ≤ 32 * ((G : ℝ) + W / α * Real.log (2 * Y)) := by
        simp only [div_eq_mul_inv] at hmul ⊢
        nlinarith
  have hn : (monotoneSampleCount (4 * G * Y) α δ : ℝ) ≤
      3072 * Real.log (2 * G * Y / δ) / α ^ 2 := by
    have hs := (monotoneSampleCount_bounds (4 * G * Y) α δ hM hα hα1 hδ hδ1).2.2
    have hl := log_eight_le_three_log_two ((G : ℝ) * Y) δ hGY hδ hδ1
    have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 1024 / α ^ 2)
    have heq₁ : 2 * (4 * (G : ℝ) * Y) / δ = 8 * ((G : ℝ) * Y) / δ := by ring
    have heq₂ : 2 * ((G : ℝ) * Y) / δ = 2 * G * Y / δ := by ring
    rw [heq₁] at hs
    rw [heq₂] at hm
    simp only [div_eq_mul_inv] at hs hm ⊢
    nlinarith
  rw [Nat.cast_mul]
  calc
    (monotoneMeanCap G Y W α : ℝ) * monotoneSampleCount (4 * G * Y) α δ
      ≤ (32 * ((G : ℝ) + W / α * Real.log (2 * Y))) *
          (3072 * Real.log (2 * G * Y / δ) / α ^ 2) :=
        mul_le_mul hcap hn (by positivity) (by positivity)
    _ = _ := by ring

end BilateralProfit

namespace BilateralProfit.QTree

open MeasureTheory

variable {Q Out : Type} [DecidableEq Q]

/-- The empirical-mean query block has Hoeffding's success probability at every
initial query counter, including when the observation laws vary with that counter. -/
theorem sampleMeanBlock_good_probability (obs : Q → ℕ → Measure ℝ)
    (q : Q) (hobs : ∀ j, IsProbabilityMeasure (obs q j))
    (n : ℕ) (hn : 0 < n) (m c α : ℝ) (hα : 0 ≤ α)
    (hb : ∀ j, obs q j (Set.Icc c (c + 4))ᶜ = 0)
    (hm : ∀ j, ∫ r, r ∂obs q j = m) (cnt : Q → ℕ) :
    ENNReal.ofReal (1 - 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512)) ≤
      (sampleMeanBlock q n).prob obs (fun r => |r - m| ≤ α / 8) cnt := by
  rw [prob_sampleMeanBlock obs q hobs]
  let (j : Fin n) : IsProbabilityMeasure (obs q (cnt q + j)) := hobs _
  exact BilateralProfit.product_sampleMean_good_probability n hn
    (fun j : Fin n => obs q (cnt q + j)) m c α hα (fun j => hb _) (fun j => hm _)

/-- Adaptive repetition of empirical-mean blocks preserves robust correctness
with the stated logarithmic sample size. -/
theorem prob_liftSampleMeans_lower (obs : Q → ℕ → Measure ℝ)
    (R : QTree Q Out) (p : Q → Prop) (g : Q → ℝ) (E : Out → Prop)
    (M n : ℕ) (hM : 0 < M) (hn : 0 < n) (α δ c : ℝ)
    (hα : 0 < α) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hnsize : 512 * Real.log (2 * (M : ℝ) / δ) / α ^ 2 ≤ (n : ℝ))
    (hR : R.AllQueries p) (hcap : R.QueriesAtMost M)
    (hrobust : R.Robust (fun q r => |r - g q| ≤ α / 8) E)
    (hobs : ∀ q, p q → ∀ j, IsProbabilityMeasure (obs q j))
    (hb : ∀ q, p q → ∀ j, obs q j (Set.Icc c (c + 4))ᶜ = 0)
    (hm : ∀ q, p q → ∀ j, ∫ r, r ∂obs q j = g q) (cnt : Q → ℕ) :
    ENNReal.ofReal (1 - δ) ≤
      (liftBlocks (fun q => sampleMeanBlock q n) R).prob obs E cnt := by
  let η : ℝ := 2 * Real.exp (-(n : ℝ) * α ^ 2 / 512)
  have hη0 : 0 ≤ η := by positivity
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have herror : (M : ℝ) * η ≤ δ :=
    BilateralProfit.hoeffding_failure_bound_of_sample_size M α δ n
      (by exact_mod_cast hM) hα hδ hnsize
  have hη1 : η ≤ 1 := by nlinarith
  calc
    ENNReal.ofReal (1 - δ) ≤ ENNReal.ofReal (1 - (M : ℝ) * η) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ _ := prob_liftBlocks_lower obs (fun q => sampleMeanBlock q n) R p
      (fun q r => |r - g q| ≤ α / 8) E hR hrobust hcap hη0 hη1
      (fun q hq cts => sampleMeanBlock_good_probability obs q (hobs q hq)
        n hn (g q) c α hα.le (hb q hq) (hm q hq) cts) cnt

end BilateralProfit.QTree

namespace BilateralProfit.MonotoneAlgorithm

open QTree

variable {Q : Type} [DecidableEq Q]

/-- A balanced interval estimator, taking its endpoint responses as estimates. -/
noncomputable def interval (α : ℝ) (key : ℕ → Q) :
    ℕ → ℕ → ℕ → QTree Q (ℕ → ℝ)
  | 0, lo, _ => .query (key lo) (fun a => .done (fun _ => a))
  | d + 1, lo, n =>
      if n ≤ 1 then .query (key lo) (fun a => .done (fun _ => a))
      else .query (key lo) (fun a => .query (key (lo + n - 1)) (fun b =>
        if |a - b| ≤ α / 2 then .done (fun _ => a)
        else bind (interval α key d lo (n / 2)) (fun left =>
          bind (interval α key d (lo + n / 2) (n - n / 2)) (fun right =>
            .done (fun t => if t < lo + n / 2 then left t else right t)))))

def osc (f : ℕ → ℝ) (lo n : ℕ) : ℝ := |f (lo + n - 1) - f lo|

lemma osc_nonneg (f : ℕ → ℝ) (lo n : ℕ) : 0 ≤ osc f lo n := abs_nonneg _

lemma between_osc (f : ℕ → ℝ) (hm : Monotone f ∨ Antitone f)
    {lo hi t : ℕ} (hl : lo ≤ t) (ht : t ≤ hi) :
    |f lo - f t| ≤ |f hi - f lo| := by
  rcases hm with hm | hm
  · have h₁ := hm hl
    have h₂ := hm ht
    rw [abs_of_nonpos (sub_nonpos.mpr h₁), abs_of_nonneg (sub_nonneg.mpr (h₁.trans h₂))]
    linarith
  · have h₁ := hm hl
    have h₂ := hm ht
    rw [abs_of_nonneg (sub_nonneg.mpr h₁), abs_of_nonpos (sub_nonpos.mpr (h₂.trans h₁))]
    linarith

lemma osc_split (f : ℕ → ℝ) (hm : Monotone f ∨ Antitone f)
    (lo n : ℕ) (hn : 2 ≤ n) :
    osc f lo (n / 2) + osc f (lo + n / 2) (n - n / 2) ≤ osc f lo n := by
  have hhalf : 0 < n / 2 := Nat.div_pos hn (by decide)
  have hhalf' : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
  have heq : lo + n / 2 + (n - n / 2) - 1 = lo + n - 1 := by omega
  unfold osc
  rw [heq]
  rcases hm with hm | hm
  · have h₁ := hm (show lo ≤ lo + n / 2 - 1 by omega)
    have h₂ := hm (show lo + n / 2 - 1 ≤ lo + n / 2 by omega)
    have h₃ := hm (show lo + n / 2 ≤ lo + n - 1 by omega)
    rw [abs_of_nonneg (sub_nonneg.mpr h₁), abs_of_nonneg (sub_nonneg.mpr h₃),
      abs_of_nonneg (sub_nonneg.mpr (h₁.trans (h₂.trans h₃)))]
    linarith
  · have h₁ := hm (show lo ≤ lo + n / 2 - 1 by omega)
    have h₂ := hm (show lo + n / 2 - 1 ≤ lo + n / 2 by omega)
    have h₃ := hm (show lo + n / 2 ≤ lo + n - 1 by omega)
    rw [abs_of_nonpos (sub_nonpos.mpr h₁), abs_of_nonpos (sub_nonpos.mpr h₃),
      abs_of_nonpos (sub_nonpos.mpr (h₃.trans (h₂.trans h₁)))]
    linarith

omit [DecidableEq Q] in
lemma robust_mono (R : QTree Q (ℕ → ℝ)) (good : Q → ℝ → Prop)
    {E F : (ℕ → ℝ) → Prop} (hR : R.Robust good E) (hEF : ∀ o, E o → F o) :
    R.Robust good F := by
  induction R with
  | done o => exact hEF o hR
  | query q k ih => exact fun r hr => ih r (hR r hr)

omit [DecidableEq Q] in
lemma robust_bind {A B : Type} (R : QTree Q A) (k : A → QTree Q B)
    (good : Q → ℝ → Prop) (E : A → Prop) (F : B → Prop)
    (hR : R.Robust good E) (hk : ∀ o, E o → (k o).Robust good F) :
    (bind R k).Robust good F := by
  induction R with
  | done o => exact hk o hR
  | query q k' ih => exact fun r hr => ih r (hR r hr)

lemma allQueries_interval (α : ℝ) (key : ℕ → Q) (p : Q → Prop)
    (hk : ∀ t, p (key t)) (d lo n : ℕ) : (interval α key d lo n).AllQueries p := by
  induction d generalizing lo n with
  | zero => exact ⟨hk lo, fun _ => trivial⟩
  | succ d ih =>
      simp only [interval]
      split_ifs with hn
      · exact ⟨hk lo, fun _ => trivial⟩
      · refine ⟨hk lo, fun a => ⟨hk _, fun b => ?_⟩⟩
        dsimp only
        split_ifs
        · trivial
        · exact allQueries_bind _ _ _ (ih _ _) (fun _ =>
            allQueries_bind _ _ _ (ih _ _) (fun _ => trivial))

lemma queriesAtMost_interval (α : ℝ) (key : ℕ → Q) (d lo n : ℕ) (hn : 0 < n) :
    (interval α key d lo n).QueriesAtMost (4 * n - 2) := by
  induction d generalizing lo n with
  | zero =>
      apply queriesAtMost_mono _ (m := 1) (by intro a; trivial)
      omega
  | succ d ih =>
      simp only [interval]
      split_ifs with hsmall
      · apply queriesAtMost_mono _ (m := 1) (by intro a; trivial)
        omega
      · have hL : 0 < n / 2 := Nat.div_pos (by omega) (by decide)
        have hR : 0 < n - n / 2 := by have := Nat.div_lt_self hn (show 1 < 2 by decide); omega
        have hcap : 4 * n - 2 = ((4 * (n / 2) - 2) + (4 * (n - n / 2) - 2)) + 2 := by omega
        rw [hcap]
        intro a b
        dsimp only
        split_ifs
        · trivial
        · exact queriesAtMost_bind _ _ (ih _ _ hL) (fun left => by
            simpa using queriesAtMost_bind (interval α key d (lo + n / 2) (n - n / 2))
              (fun right => .done (fun t => if t < lo + n / 2 then left t else right t))
              (ih _ _ hR) (n := 0) (fun _ => trivial))

lemma endpoint_accuracy (α : ℝ) (hα : 0 < α) (f : ℕ → ℝ)
    (hm : Monotone f ∨ Antitone f) (lo n t : ℕ)
    (ht₁ : lo ≤ t) (ht₂ : t < lo + n) (a b : ℝ)
    (ha : |a - f lo| ≤ α / 8) (hb : |b - f (lo + n - 1)| ≤ α / 8)
    (hab : |a - b| ≤ α / 2) : |a - f t| ≤ α := by
  have hv : osc f lo n ≤ 3 * α / 4 := by
    unfold osc
    calc
      _ = |(f (lo + n - 1) - b) + (b - a) + (a - f lo)| := by congr 1; ring
      _ ≤ |f (lo + n - 1) - b| + |b - a| + |a - f lo| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * α / 4 := by rw [abs_sub_comm (f _) b, abs_sub_comm b a]; linarith
  calc
    _ = |(a - f lo) + (f lo - f t)| := by congr 1; ring
    _ ≤ |a - f lo| + |f lo - f t| := abs_add_le _ _
    _ ≤ α := by have := between_osc f hm ht₁ (show t ≤ lo + n - 1 by omega); unfold osc at hv; linarith

lemma split_osc (α : ℝ) (f : ℕ → ℝ) (lo n : ℕ) (a b : ℝ)
    (ha : |a - f lo| ≤ α / 8) (hb : |b - f (lo + n - 1)| ≤ α / 8)
    (hab : ¬ |a - b| ≤ α / 2) : α / 4 < osc f lo n := by
  have htriangle : |a - b| ≤ α / 4 + osc f lo n := by
    calc
      _ = |(a - f lo) + (f lo - f (lo + n - 1)) + (f (lo + n - 1) - b)| := by congr 1; ring
      _ ≤ |a - f lo| + |f lo - f (lo + n - 1)| + |f (lo + n - 1) - b| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ _ := by rw [abs_sub_comm (f lo) (f _), abs_sub_comm (f _) b]; unfold osc; linarith
  linarith

omit [DecidableEq Q] in
lemma robust_interval (α : ℝ) (hα : 0 < α) (key : ℕ → Q) (mean : Q → ℝ)
    (hm : Monotone (mean ∘ key) ∨ Antitone (mean ∘ key))
    (d lo n : ℕ) (hn : 0 < n) (hdepth : n ≤ 2 ^ d) :
    (interval α key d lo n).Robust (fun q a => |a - mean q| ≤ α / 8)
      (fun est => ∀ t, lo ≤ t → t < lo + n → |est t - mean (key t)| ≤ α) := by
  induction d generalizing lo n with
  | zero =>
      intro a ha t ht₁ ht₂
      have ht : t = lo := by simp only [pow_zero] at hdepth; omega
      subst t
      dsimp
      linarith
  | succ d ih =>
      simp only [interval]
      split_ifs with hsmall
      · intro a ha t ht₁ ht₂
        have ht : t = lo := by omega
        subst t
        dsimp
        linarith
      · intro a ha b hb
        dsimp only
        split_ifs with hab
        · exact fun t ht₁ ht₂ => endpoint_accuracy α hα (mean ∘ key) hm lo n t ht₁ ht₂ a b ha hb hab
        · have hL : 0 < n / 2 := Nat.div_pos (by omega) (by decide)
          have hR : 0 < n - n / 2 := by have := Nat.div_lt_self hn (show 1 < 2 by decide); omega
          have hdL : n / 2 ≤ 2 ^ d := by rw [pow_succ] at hdepth; omega
          have hdR : n - n / 2 ≤ 2 ^ d := by rw [pow_succ] at hdepth; omega
          apply robust_bind _ _ _ _ _ (ih lo (n / 2) hL hdL)
          intro left hleft
          apply robust_bind _ _ _ _ _ (ih (lo + n / 2) (n - n / 2) hR hdR)
          intro right hright t ht₁ ht₂
          dsimp
          split_ifs with ht
          · exact hleft t ht₁ ht
          · exact hright t (by omega) (by omega)

omit [DecidableEq Q] in
lemma robust_true {A : Type} (R : QTree Q A) (good : Q → ℝ → Prop) :
    R.Robust good (fun _ => True) := by
  induction R with
  | done _ => trivial
  | query _ k ih => exact fun r _ => ih r

lemma goodCost_interval (α : ℝ) (hα : 0 < α) (key : ℕ → Q) (mean : Q → ℝ)
    (hm : Monotone (mean ∘ key) ∨ Antitone (mean ∘ key))
    (d lo n : ℕ) (hn : 0 < n) :
    (interval α key d lo n).GoodCost (fun q a => |a - mean q| ≤ α / 8)
      (2 + (16 / α) * osc (mean ∘ key) lo n * d) := by
  let good : Q → ℝ → Prop := fun q a => |a - mean q| ≤ α / 8
  have hc : 0 ≤ 16 / α := by positivity
  induction d generalizing lo n with
  | zero =>
      simp only [interval, Nat.cast_zero, mul_zero, add_zero]
      exact ⟨by norm_num, fun _ _ => by norm_num [GoodCost]⟩
  | succ d ih =>
      have hbase : 2 ≤ 2 + (16 / α) * osc (mean ∘ key) lo n * (d + 1 : ℕ) := by
        have := mul_nonneg (mul_nonneg hc (osc_nonneg (mean ∘ key) lo n)) (Nat.cast_nonneg (d + 1))
        linarith
      simp only [interval]
      split_ifs with hsmall
      · refine ⟨by linarith, fun _ _ => ?_⟩
        change 0 ≤ _
        linarith
      · refine ⟨by linarith, fun a ha => ⟨by linarith, fun b hb => ?_⟩⟩
        dsimp only
        split_ifs with hab
        · change 0 ≤ _
          linarith
        · have hL : 0 < n / 2 := Nat.div_pos (by omega) (by decide)
          have hR : 0 < n - n / 2 := by have := Nat.div_lt_self hn (show 1 < 2 by decide); omega
          have ihL := ih lo (n / 2) hL
          have ihR := ih (lo + n / 2) (n - n / 2) hR
          have hbindR (left : ℕ → ℝ) :
              (bind (interval α key d (lo + n / 2) (n - n / 2)) (fun right =>
                .done (fun t => if t < lo + n / 2 then left t else right t))).GoodCost good
                (2 + (16 / α) * osc (mean ∘ key) (lo + n / 2) (n - n / 2) * d) := by
            simpa only [add_zero] using goodCost_bind good _ _ (fun _ => True) ihR
              (robust_true _ good) (c := 0) (by norm_num) (fun _ _ => le_rfl)
          have hbind := goodCost_bind good _ _ (fun _ => True) ihL (robust_true _ good)
            (goodCost_nonneg good _ ihR) (fun left _ => hbindR left)
          apply goodCost_mono good _ hbind
          have hv := osc_nonneg (mean ∘ key) lo n
          have hs := osc_split (mean ∘ key) hm lo n (by omega)
          have hp := split_osc α (mean ∘ key) lo n a b ha hb hab
          have hp' : 4 ≤ (16 / α) * osc (mean ∘ key) lo n := by
            rw [div_mul_eq_mul_div]
            apply (le_div_iff₀ hα).mpr
            linarith
          have hsum := mul_le_mul_of_nonneg_left hs (mul_nonneg hc (Nat.cast_nonneg d))
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith

end BilateralProfit.MonotoneAlgorithm

namespace BilateralProfit.MonotoneEstimation

open Set

variable {Y : Type*} [LinearOrder Y]

/-- A monotone function's variation on an ordered set with endpoints is its oscillation. -/
theorem variation_eq_endpoints (g : Y → ℝ) (s : Set Y) (a b : Y)
    (ha : a ∈ s) (hb : b ∈ s) (hs : ∀ y ∈ s, a ≤ y ∧ y ≤ b)
    (hg : MonotoneOn g s ∨ AntitoneOn g s) :
    eVariationOn g s = ENNReal.ofReal |g b - g a| := by
  have hab : a ≤ b := (hs b hb).1
  rcases hg with hg | hg
  · have hset : s ∩ Icc a b = s := inter_eq_left.mpr hs
    rw [← hset, hg.eVariationOn_eq ha hb, abs_of_nonneg (sub_nonneg.mpr (hg ha hb hab))]
  · have hmono : MonotoneOn (g ∘ OrderDual.ofDual)
        (OrderDual.ofDual ⁻¹' s) := by
      intro x hx y hy hxy
      exact hg hy hx hxy
    have hv := hmono.eVariationOn_eq (a := OrderDual.toDual b)
      (b := OrderDual.toDual a) hb ha
    have hset : OrderDual.ofDual ⁻¹' s ∩
        Icc (OrderDual.toDual b) (OrderDual.toDual a) = OrderDual.ofDual ⁻¹' s := by
      apply inter_eq_left.mpr
      intro y hy
      exact ⟨(hs y hy).2, (hs y hy).1⟩
    rw [hset, eVariationOn.comp_ofDual] at hv
    rw [hv, abs_of_nonpos (sub_nonpos.mpr (hg ha hb hab))]
    congr 1
    simp only [Function.comp_apply, OrderDual.ofDual_toDual]
    ring

theorem finite_variation_eq_oscillation (g : Y → ℝ) (s : Finset Y) (hs : s.Nonempty)
    (hg : MonotoneOn g (s : Set Y) ∨ AntitoneOn g (s : Set Y)) :
    (eVariationOn g (s : Set Y)).toReal = |g (s.max' hs) - g (s.min' hs)| := by
  rw [variation_eq_endpoints g (s : Set Y) (s.min' hs) (s.max' hs)
    (Finset.min'_mem s hs) (Finset.max'_mem s hs)
    (fun y hy => ⟨Finset.min'_le s y hy, Finset.le_max' s y hy⟩) hg]
  exact ENNReal.toReal_ofReal (abs_nonneg _)

theorem finite_variation_ne_top (g : Y → ℝ) (s : Finset Y)
    (hg : MonotoneOn g (s : Set Y) ∨ AntitoneOn g (s : Set Y)) :
    eVariationOn g (s : Set Y) ≠ ⊤ := by
  by_cases hs : s.Nonempty
  · rw [variation_eq_endpoints g (s : Set Y) (s.min' hs) (s.max' hs)
      (Finset.min'_mem s hs) (Finset.max'_mem s hs)
      (fun y hy => ⟨Finset.min'_le s y hy, Finset.le_max' s y hy⟩) hg]
    exact ENNReal.ofReal_ne_top
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hempty]

theorem oscillation_bound (g : Y → ℝ) (s : Set Y) (a b y : Y)
    (ha : a ∈ s) (hb : b ∈ s) (hy : y ∈ s) (hay : a ≤ y) (hyb : y ≤ b)
    (hg : MonotoneOn g s ∨ AntitoneOn g s) :
    |g y - g a| ≤ |g b - g a| := by
  rcases hg with hg | hg
  · rw [abs_of_nonneg (sub_nonneg.mpr (hg ha hy hay)),
      abs_of_nonneg (sub_nonneg.mpr (hg ha hb (hay.trans hyb)))]
    linarith [hg hy hb hyb]
  · rw [abs_of_nonpos (sub_nonpos.mpr (hg ha hy hay)),
      abs_of_nonpos (sub_nonpos.mpr (hg ha hb (hay.trans hyb)))]
    linarith [hg hy hb hyb]

theorem finite_oscillation_bound (g : Y → ℝ) (s : Finset Y) (hs : s.Nonempty)
    (hg : MonotoneOn g (s : Set Y) ∨ AntitoneOn g (s : Set Y))
    (y : Y) (hy : y ∈ s) :
    |g y - g (s.min' hs)| ≤ (eVariationOn g (s : Set Y)).toReal := by
  rw [finite_variation_eq_oscillation g s hs hg]
  exact oscillation_bound g (s : Set Y) (s.min' hs) (s.max' hs) y
    (Finset.min'_mem s hs) (Finset.max'_mem s hs) hy
    (Finset.min'_le s y hy) (Finset.le_max' s y hy) hg

end BilateralProfit.MonotoneEstimation

namespace BilateralProfit.MonotoneFamily

open QTree MonotoneAlgorithm MonotoneEstimation

variable {ι Y : Type} [Fintype ι] [DecidableEq ι] [Fintype Y] [LinearOrder Y]

noncomputable def key (s : Finset Y) (hs : s.Nonempty) (k : ℕ) : Y :=
  s.orderEmbOfFin rfl ⟨min k (s.card - 1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hs.card_pos (by decide))⟩

lemma key_mem (s : Finset Y) (hs : s.Nonempty) (k : ℕ) : key s hs k ∈ s :=
  s.orderEmbOfFin_mem rfl _

lemma key_monotone (s : Finset Y) (hs : s.Nonempty) : Monotone (key s hs) := by
  intro a b hab
  apply (s.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hab

lemma key_zero (s : Finset Y) (hs : s.Nonempty) : key s hs 0 = s.min' hs := by
  simpa [key] using Finset.orderEmbOfFin_zero (s := s) rfl hs.card_pos

lemma key_last (s : Finset Y) (hs : s.Nonempty) : key s hs (s.card - 1) = s.max' hs := by
  simpa [key] using Finset.orderEmbOfFin_last (s := s) rfl hs.card_pos

lemma key_rank (s : Finset Y) (hs : s.Nonempty) (y : Y) (hy : y ∈ s) :
    key s hs ((s.orderIsoOfFin rfl).symm ⟨y, hy⟩ : Fin s.card) = y := by
  let r := (s.orderIsoOfFin rfl).symm ⟨y, hy⟩
  have heq : (⟨min (r : ℕ) (s.card - 1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hs.card_pos (by decide))⟩ : Fin s.card) = r := by
    apply Fin.ext
    exact min_eq_left (by have := r.isLt; omega)
  unfold key
  change s.orderEmbOfFin rfl ⟨min (r : ℕ) (s.card - 1), _⟩ = y
  rw [heq, ← Finset.coe_orderIsoOfFin_apply]
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨y, hy⟩)

noncomputable def single (α : ℝ) (dom : ι → Finset Y) (d : ℕ) (i : ι) :
    QTree (ι × Y) (Y → ℝ) :=
  if hs : (dom i).Nonempty then
    bind (interval α (fun k => (i, key (dom i) hs k)) d 0 (dom i).card) (fun est =>
      .done (fun y => if hy : y ∈ dom i then est ((dom i).orderIsoOfFin rfl |>.symm ⟨y, hy⟩) else 0))
  else .done (fun _ => 0)

noncomputable def familyList (α : ℝ) (dom : ι → Finset Y) (d : ℕ) :
    List ι → QTree (ι × Y) (ι → Y → ℝ)
  | [] => .done (fun _ _ => 0)
  | i :: is => bind (single α dom d i) (fun est =>
      bind (familyList α dom d is) (fun rest => .done (Function.update rest i est)))

noncomputable def family (α : ℝ) (dom : ι → Finset Y) (d : ℕ) :
    QTree (ι × Y) (ι → Y → ℝ) := familyList α dom d Finset.univ.toList

lemma allQueries_single (α : ℝ) (dom : ι → Finset Y) (d : ℕ) (i : ι) :
    (single α dom d i).AllQueries (fun q => q.2 ∈ dom q.1) := by
  unfold single
  split_ifs with hs
  · exact allQueries_bind _ _ _
      (allQueries_interval α (fun k => (i, key (dom i) hs k)) (fun q => q.2 ∈ dom q.1)
        (fun t => key_mem (dom i) hs t) d 0 (dom i).card)
      (fun _ => trivial)
  · trivial

lemma queriesAtMost_single (α : ℝ) (dom : ι → Finset Y) (d : ℕ) (i : ι) :
    (single α dom d i).QueriesAtMost (4 * Fintype.card Y) := by
  unfold single
  split_ifs with hs
  · apply queriesAtMost_mono _ (m := 4 * (dom i).card - 2)
    · simpa only [add_zero] using queriesAtMost_bind _
        (fun est => .done (fun y => if hy : y ∈ dom i then est ((dom i).orderIsoOfFin rfl |>.symm ⟨y, hy⟩) else 0))
        (queriesAtMost_interval α (fun k => (i, key (dom i) hs k)) d 0 (dom i).card hs.card_pos)
        (n := 0) (fun _ => trivial)
    · have := Finset.card_le_univ (s := dom i)
      omega
  · trivial

lemma key_mean_monotone (dom : ι → Finset Y) (g : ι → Y → ℝ) (i : ι)
    (hs : (dom i).Nonempty)
    (hg : MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) :
    Monotone (fun k => g i (key (dom i) hs k)) ∨
      Antitone (fun k => g i (key (dom i) hs k)) := by
  rcases hg with hg | hg
  · left
    intro a b hab
    exact hg (key_mem (dom i) hs a) (key_mem (dom i) hs b) (key_monotone (dom i) hs hab)
  · right
    intro a b hab
    exact hg (key_mem (dom i) hs a) (key_mem (dom i) hs b) (key_monotone (dom i) hs hab)

lemma robust_single (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (hd : Fintype.card Y ≤ 2 ^ d) (i : ι)
    (hg : MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) :
    (single α dom d i).Robust (fun q a => |a - g q.1 q.2| ≤ α / 8)
      (fun est => ∀ y ∈ dom i, |est y - g i y| ≤ α) := by
  unfold single
  split_ifs with hs
  · apply robust_bind _ _ _ _ _ (robust_interval α hα
      (fun k => (i, key (dom i) hs k)) (fun q => g q.1 q.2)
      (key_mean_monotone dom g i hs hg) d 0 (dom i).card hs.card_pos
      ((Finset.card_le_univ (s := dom i)).trans hd))
    intro est hest y hy
    dsimp
    rw [dif_pos hy]
    have h := hest ((dom i).orderIsoOfFin rfl |>.symm ⟨y, hy⟩) (Nat.zero_le _)
      (by simpa using ((dom i).orderIsoOfFin rfl |>.symm ⟨y, hy⟩).isLt)
    simpa only [key_rank (dom i) hs y hy] using h
  · intro y hy
    exact False.elim (hs ⟨y, hy⟩)

lemma goodCost_single (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (i : ι)
    (hg : MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) :
    (single α dom d i).GoodCost (fun q a => |a - g q.1 q.2| ≤ α / 8)
      (2 + (16 / α) * (eVariationOn (g i) ↑(dom i)).toReal * d) := by
  unfold single
  split_ifs with hs
  · have hcost := goodCost_interval α hα (fun k => (i, key (dom i) hs k))
      (fun q => g q.1 q.2) (key_mean_monotone dom g i hs hg) d 0 (dom i).card hs.card_pos
    have heq : osc ((fun q => g q.1 q.2) ∘ (fun k => (i, key (dom i) hs k))) 0 (dom i).card =
        (eVariationOn (g i) ↑(dom i)).toReal := by
      rw [finite_variation_eq_oscillation (g i) (dom i) hs hg]
      simp only [osc, Function.comp_apply, zero_add, key_last, key_zero]
    rw [heq] at hcost
    simpa only [add_zero] using goodCost_bind _ _ _ (fun _ => True) hcost
      (robust_true _ _) (c := 0) (by norm_num) (fun _ _ => le_rfl)
  · change 0 ≤ _
    positivity

lemma allQueries_familyList (α : ℝ) (dom : ι → Finset Y) (d : ℕ) (is : List ι) :
    (familyList α dom d is).AllQueries (fun q => q.2 ∈ dom q.1) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
      exact allQueries_bind _ _ _ (allQueries_single α dom d i)
        (fun _ => allQueries_bind _ _ _ ih (fun _ => trivial))

lemma queriesAtMost_familyList (α : ℝ) (dom : ι → Finset Y) (d : ℕ) (is : List ι) :
    (familyList α dom d is).QueriesAtMost (4 * Fintype.card Y * is.length) := by
  induction is with
  | nil => trivial
  | cons i is ih =>
      have ht (est : Y → ℝ) :
          (bind (familyList α dom d is) (fun rest => .done (Function.update rest i est))).QueriesAtMost
            (4 * Fintype.card Y * is.length) := by
        simpa only [add_zero] using queriesAtMost_bind _
          (fun rest => .done (Function.update rest i est)) ih (n := 0) (fun _ => trivial)
      have h := queriesAtMost_bind _ _ (queriesAtMost_single α dom d i) ht
      simpa only [familyList, List.length_cons, Nat.mul_add, Nat.mul_one, Nat.add_comm] using h

lemma robust_familyList (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (hd : Fintype.card Y ≤ 2 ^ d)
    (hg : ∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) (is : List ι) :
    (familyList α dom d is).Robust (fun q a => |a - g q.1 q.2| ≤ α / 8)
      (fun est => ∀ i ∈ is, ∀ y ∈ dom i, |est i y - g i y| ≤ α) := by
  induction is with
  | nil => intro est h; simp at h
  | cons i is ih =>
      apply robust_bind _ _ _ _ _ (robust_single α hα dom g d hd i (hg i))
      intro est hest
      apply robust_bind _ _ _ _ _ ih
      intro rest hrest j hj y hy
      by_cases hji : j = i
      · subst j
        simpa using hest y hy
      · rw [Function.update_of_ne hji]
        exact hrest j (by simpa only [List.mem_cons, hji, false_or] using hj) y hy

lemma goodCost_familyList (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (hg : ∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) (is : List ι) :
    (familyList α dom d is).GoodCost (fun q a => |a - g q.1 q.2| ≤ α / 8)
      ((is.map (fun i => 2 + (16 / α) * (eVariationOn (g i) ↑(dom i)).toReal * d)).sum) := by
  induction is with
  | nil => exact le_rfl
  | cons i is ih =>
      have ht (est : Y → ℝ) :
          (bind (familyList α dom d is) (fun rest => .done (Function.update rest i est))).GoodCost
            (fun q a => |a - g q.1 q.2| ≤ α / 8)
            ((is.map (fun i => 2 + (16 / α) * (eVariationOn (g i) ↑(dom i)).toReal * d)).sum) := by
        simpa only [add_zero] using goodCost_bind _ _ _ (fun _ => True) ih
          (robust_true _ _) (c := 0) (by norm_num) (fun _ _ => le_rfl)
      exact goodCost_bind _ _ _ (fun _ => True) (goodCost_single α hα dom g d i (hg i))
        (robust_true _ _) (goodCost_nonneg _ _ ih) (fun est _ => ht est)

lemma allQueries_family (α : ℝ) (dom : ι → Finset Y) (d : ℕ) :
    (family α dom d).AllQueries (fun q => q.2 ∈ dom q.1) := allQueries_familyList α dom d _

lemma queriesAtMost_family (α : ℝ) (dom : ι → Finset Y) (d : ℕ) :
    (family α dom d).QueriesAtMost (4 * Fintype.card ι * Fintype.card Y) := by
  unfold family
  convert queriesAtMost_familyList α dom d (Finset.univ.toList : List ι) using 1
  all_goals simp only [Finset.length_toList, Finset.card_univ]
  ring

lemma robust_family (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (hd : Fintype.card Y ≤ 2 ^ d)
    (hg : ∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) :
    (family α dom d).Robust (fun q a => |a - g q.1 q.2| ≤ α / 8)
      (fun est => ∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) := by
  have h := robust_familyList α hα dom g d hd hg Finset.univ.toList
  simpa only [family, Finset.mem_toList, Finset.mem_univ, forall_const] using h

lemma goodCost_family (α : ℝ) (hα : 0 < α) (dom : ι → Finset Y) (g : ι → Y → ℝ)
    (d : ℕ) (hg : ∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i))
    (W : ℝ) (hW : ∑ i, (eVariationOn (g i) ↑(dom i)).toReal ≤ W) :
    (family α dom d).GoodCost (fun q a => |a - g q.1 q.2| ≤ α / 8)
      (2 * Fintype.card ι + 16 * W * d / α) := by
  unfold family
  apply goodCost_mono _ _ (goodCost_familyList α hα dom g d hg Finset.univ.toList)
  simp only [Finset.sum_map_toList, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul, ← Finset.mul_sum]
  have hc : 0 ≤ (16 / α) * (d : ℝ) := by positivity
  have h := mul_le_mul_of_nonneg_left hW hc
  convert add_le_add (le_refl (2 * (Fintype.card ι : ℝ))) h using 1 <;> first | rfl | ring

end BilateralProfit.MonotoneFamily

open BilateralProfit

open MeasureTheory

/-- Claim 4.10 of Brüstle, di Gregorio, Fusco, and Leonardi,
*Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best
Posted-Price Mechanism*, PDF pages 29 and 59–60.

The routine is chosen before the unknown functions and observation laws. The
construction uses disjoint interval halves and fresh endpoint estimates, giving
the same bound with the explicit absolute constant `98304`. -/
theorem solution :
    ∃ C : ℝ, ∀ (ι Y : Type) [Fintype ι] [DecidableEq ι] [Fintype Y] [LinearOrder Y]
      (dom : ι → Finset Y) (W α δ : ℝ), 0 ≤ W → 0 < α → α < 1 → 0 < δ → δ < 1 →
      ∃ (R : QTree (ι × Y) (ι → Y → ℝ)) (N : ℕ),
        (N : ℝ) ≤ C * Real.log (2 * Fintype.card ι * Fintype.card Y / δ) / α ^ 2 *
          (Fintype.card ι + W / α * Real.log (2 * Fintype.card Y)) ∧
        R.QueriesAtMost N ∧ R.AllQueries (fun q => q.2 ∈ dom q.1) ∧
        ∀ g : ι → Y → ℝ, (∀ i, ∀ y ∈ dom i, g i y ∈ Set.Icc (-1 : ℝ) 1) →
          (∀ i, MonotoneOn (g i) ↑(dom i) ∨ AntitoneOn (g i) ↑(dom i)) →
          ∑ i, (eVariationOn (g i) ↑(dom i)).toReal ≤ W →
          ∀ (c : ℝ) (obs : ι × Y → ℕ → Measure ℝ),
            (∀ i, ∀ y ∈ dom i, ∀ n, IsProbabilityMeasure (obs (i, y) n)) →
            (∀ i, ∀ y ∈ dom i, ∀ n, obs (i, y) n (Set.Icc c (c + 4))ᶜ = 0) →
            (∀ i, ∀ y ∈ dom i, ∀ n, ∫ r, r ∂(obs (i, y) n) = g i y) →
            ENNReal.ofReal (1 - δ) ≤
              R.prob obs (fun est => ∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) (fun _ => 0) := by
  refine ⟨98304, ?_⟩
  intro ι Y _ _ _ _ dom W α δ hW hα hα1 hδ hδ1
  classical
  by_cases hempty : Fintype.card ι = 0 ∨ Fintype.card Y = 0
  · refine ⟨.done (fun _ _ => 0), 0, ?_, trivial, trivial, ?_⟩
    · rcases hempty with h | h <;> simp [h]
    · intro g _ _ _ c obs _ _ _
      have hE : ∀ i, ∀ y ∈ dom i, |(0 : ℝ) - g i y| ≤ α := by
        intro i y _
        rcases hempty with h | h
        · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h
          exact isEmptyElim i
        · have : IsEmpty Y := Fintype.card_eq_zero_iff.mp h
          exact isEmptyElim y
      simpa only [QTree.prob, if_pos hE, ENNReal.ofReal_one] using
        (ENNReal.ofReal_le_ofReal (show 1 - δ ≤ (1 : ℝ) by linarith))
  · have hG : 0 < Fintype.card ι := by omega
    have hY : 0 < Fintype.card Y := by omega
    let d := Nat.log2 (Fintype.card Y) + 1
    let M := 4 * Fintype.card ι * Fintype.card Y
    let n := monotoneSampleCount (4 * Fintype.card ι * Fintype.card Y) α δ
    let cap := monotoneMeanCap (Fintype.card ι) (Fintype.card Y) W α
    let base := MonotoneFamily.family α dom d
    let high := QTree.truncate cap base (fun _ _ => 0)
    let low := QTree.liftBlocks (fun q => QTree.sampleMeanBlock q n) high
    have hlegal : base.AllQueries (fun q => q.2 ∈ dom q.1) :=
      MonotoneFamily.allQueries_family α dom d
    have hhighlegal : high.AllQueries (fun q => q.2 ∈ dom q.1) :=
      QTree.allQueries_truncate cap base (fun _ _ => 0) _ hlegal
    have hhighcap : high.QueriesAtMost cap := QTree.queriesAtMost_truncate cap base _
    have hsure : high.QueriesAtMost M :=
      QTree.queriesAtMost_truncate_of_queriesAtMost cap base _
        (MonotoneFamily.queriesAtMost_family α dom d)
    have hM : 0 < M := by dsimp [M]; positivity
    have hMreal : (1 : ℝ) ≤ 4 * Fintype.card ι * Fintype.card Y := by
      exact_mod_cast (show 1 ≤ 4 * Fintype.card ι * Fintype.card Y from hM)
    have hnbounds := monotoneSampleCount_bounds
      (4 * Fintype.card ι * Fintype.card Y) α δ hMreal hα hα1 hδ hδ1
    have hn : 0 < n := hnbounds.1
    refine ⟨low, cap * n, ?_, ?_, ?_, ?_⟩
    · exact monotone_observation_budget_bound (Fintype.card ι) (Fintype.card Y)
        hG hY W α δ hW hα hα1 hδ hδ1
    · exact QTree.queriesAtMost_liftBlocks _ high _ hhighlegal hhighcap
        (fun q _ => QTree.queriesAtMost_sampleMeanBlock q n)
    · exact QTree.allQueries_liftBlocks _ high _ hhighlegal
        (fun q hq => QTree.allQueries_sampleMeanBlock q n _ hq)
    · intro g _ hmono hvar c obs hobs hsupport hmean
      have hdepth : Fintype.card Y ≤ 2 ^ d :=
        le_two_pow_log2_add_one _ _ le_rfl
      have hrobust := MonotoneFamily.robust_family α hα dom g d hdepth hmono
      have hcost := MonotoneFamily.goodCost_family α hα dom g d hmono W hvar
      have hhighrobust : high.Robust (fun q a => |a - g q.1 q.2| ≤ α / 8)
          (fun est => ∀ i, ∀ y ∈ dom i, |est i y - g i y| ≤ α) := by
        apply QTree.robust_truncate_of_goodCost _ _ base (fun _ _ => 0) hrobust
        convert hcost using 1
        simp [d, Nat.cast_add, Nat.cast_one]
      apply QTree.prob_liftSampleMeans_lower obs high (fun q => q.2 ∈ dom q.1)
        (fun q => g q.1 q.2) _ M n hM hn α δ c hα hδ hδ1 _
        hhighlegal hsure hhighrobust
        (fun q hq j => hobs q.1 q.2 hq j)
        (fun q hq j => hsupport q.1 q.2 hq j)
        (fun q hq j => hmean q.1 q.2 hq j)
      simpa [M, n, Nat.cast_mul, Nat.cast_ofNat] using hnbounds.2.1
