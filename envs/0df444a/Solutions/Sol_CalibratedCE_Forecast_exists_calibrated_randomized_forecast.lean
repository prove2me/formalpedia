-- Prove2me | solution 1 for CalibratedCE.Forecast.exists_calibrated_randomized_forecast
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-06T04:59:23.781688+00:00
-- url     : https://prove2.me/submissions/fc126aa6-b1ff-460d-b59b-ad54cc00dce3

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_CalibratedCE_Forecast_CalibScoreH
import Definitions.Def_CalibratedCE_Forecast_HistLaw
import Definitions.Def_CalibratedCE_Forecast_Regret
import Definitions.Def_CalibratedCE_Forecast_FracCalib

set_option autoImplicit false

/- Complete checked body: PMFMean -/
section

open scoped BigOperators

namespace CalibratedCE.ForecastProof

noncomputable def pmfMean {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, (p a).toReal * f a

theorem pmfMean_eq_sum {α : Type*} (p : PMF α) (f : α → ℝ) (s : Finset α)
    (hs : p.support ⊆ s) : pmfMean p f = ∑ a ∈ s, (p a).toReal * f a := by
  apply tsum_eq_sum
  intro a ha
  have hp : p a = 0 := (p.apply_eq_zero_iff a).2 (fun h => ha (hs h))
  simp only [hp, ENNReal.toReal_zero, zero_mul]

theorem pmfMean_pure {α : Type*} (a : α) (f : α → ℝ) :
    pmfMean (PMF.pure a) f = f a := by
  classical
  rw [pmfMean, tsum_eq_single a]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

theorem pmfMean_const {α : Type*} (p : PMF α) (c : ℝ) :
    pmfMean p (fun _ => c) = c := by
  rw [pmfMean, tsum_mul_right]
  have h : ∑' a, (p a).toReal = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a), p.tsum_coe, ENNReal.toReal_one]
  rw [h, one_mul]

theorem pmfMean_congr {α : Type*} (p : PMF α) {f g : α → ℝ}
    (h : ∀ a ∈ p.support, f a = g a) : pmfMean p f = pmfMean p g := by
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(p.apply_eq_zero_iff a).2 ha]
    simp

theorem pmfMean_mono {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f g : α → ℝ} (h : ∀ a ∈ p.support, f a ≤ g a) : pmfMean p f ≤ pmfMean p g := by
  classical
  rw [pmfMean_eq_sum p f hp.toFinset (by simp), pmfMean_eq_sum p g hp.toFinset (by simp)]
  apply Finset.sum_le_sum
  intro a ha
  exact mul_le_mul_of_nonneg_left (h a (by simpa using ha)) ENNReal.toReal_nonneg

theorem pmfMean_nonneg {α : Type*} (p : PMF α) (hp : p.support.Finite)
    {f : α → ℝ} (h : ∀ a ∈ p.support, 0 ≤ f a) : 0 ≤ pmfMean p f := by
  simpa only [pmfMean_const] using pmfMean_mono p hp h

theorem pmfMean_add {α : Type*} (p : PMF α) (hp : p.support.Finite) (f g : α → ℝ) :
    pmfMean p (fun a => f a + g a) = pmfMean p f + pmfMean p g := by
  classical
  simp only [pmfMean_eq_sum p _ hp.toFinset (by simp), mul_add, Finset.sum_add_distrib]

theorem pmfMean_smul {α : Type*} (p : PMF α) (c : ℝ) (f : α → ℝ) :
    pmfMean p (fun a => c * f a) = c * pmfMean p f := by
  unfold pmfMean
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  ring

theorem pmfMean_sum {α ι : Type*} (p : PMF α) (hp : p.support.Finite)
    (s : Finset ι) (f : ι → α → ℝ) :
    pmfMean p (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, pmfMean p (f i) := by
  classical
  simp only [pmfMean_eq_sum p _ hp.toFinset (by simp), Finset.mul_sum]
  exact Finset.sum_comm

theorem pmf_bind_finite {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (q : α → PMF β) (hq : ∀ a, (q a).support.Finite) : (p.bind q).support.Finite := by
  rw [PMF.support_bind]
  exact hp.biUnion (fun a _ => hq a)

theorem pmf_map_finite {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) : (p.map f).support.Finite := by
  rw [PMF.support_map]
  exact hp.image f

theorem pmfMean_bind {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (q : α → PMF β) (hq : ∀ a, (q a).support.Finite) (f : β → ℝ) :
    pmfMean (p.bind q) f = pmfMean p (fun a => pmfMean (q a) f) := by
  classical
  let s := hp.toFinset
  let t := s.biUnion (fun a => (hq a).toFinset)
  have hs : p.support ⊆ s := by simp [s]
  have ht : ∀ a ∈ s, (q a).support ⊆ t := by
    intro a ha b hb
    exact Finset.mem_biUnion.mpr ⟨a, ha, by simpa using hb⟩
  have hbt : (p.bind q).support ⊆ t := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := (PMF.mem_support_bind_iff p q b).mp hb
    exact ht a (hs ha) hab
  have hb : ∀ b, ((p.bind q) b).toReal = ∑ a ∈ s, (p a).toReal * (q a b).toReal := by
    intro b
    rw [PMF.bind_apply, tsum_eq_sum (s := s)]
    · rw [ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (p.apply_ne_top a) ((q a).apply_ne_top b))]
      simp only [ENNReal.toReal_mul]
    · intro a ha
      rw [(p.apply_eq_zero_iff a).2 (fun h => ha (hs h)), zero_mul]
  rw [pmfMean_eq_sum _ _ t hbt, pmfMean_eq_sum p _ s hs]
  simp_rw [hb, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [pmfMean_eq_sum (q a) f t (ht a ha), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem pmfMean_map {α β : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → β) (g : β → ℝ) : pmfMean (p.map f) g = pmfMean p (fun a => g (f a)) := by
  rw [PMF.map, pmfMean_bind p hp _ (fun a => by simp)]
  change pmfMean p (fun a => pmfMean (PMF.pure (f a)) g) = _
  simp only [pmfMean_pure]

theorem pmfMean_sq_le {α : Type*} (p : PMF α) (hp : p.support.Finite) (f : α → ℝ) :
    (pmfMean p f)^2 ≤ pmfMean p (fun a => (f a)^2) := by
  have h := pmfMean_nonneg p hp (f := fun a => (f a - pmfMean p f)^2)
    (fun a _ => sq_nonneg _)
  have he : pmfMean p (fun a => (f a - pmfMean p f)^2) =
      pmfMean p (fun a => (f a)^2) - (pmfMean p f)^2 := by
    calc
      _ = pmfMean p (fun a => (f a)^2 + (-2 * pmfMean p f) * f a + (pmfMean p f)^2) := by
        apply pmfMean_congr; intro a _; ring
      _ = _ := by rw [pmfMean_add _ hp, pmfMean_add _ hp, pmfMean_smul, pmfMean_const]; ring
  rw [he] at h
  linarith


end CalibratedCE.ForecastProof
end

/- Complete checked body: HistoryMeans -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

abbrev History (n : ℕ) := List ((Fin n → ℝ) × Fin n)
abbrev Forecaster (n : ℕ) := History n → PMF (Fin n → ℝ)
abbrev Opponent (n : ℕ) := History n → PMF (Fin n)

def finiteForecaster {n : ℕ} (F : Forecaster n) : Prop :=
  ∀ h, (F h).support.Finite

theorem histLaw_finite {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (hF : finiteForecaster F) (t : ℕ) : (histLaw F A t).support.Finite := by
  induction t with
  | zero => simp [histLaw]
  | succ t ih =>
    exact pmf_bind_finite _ ih _ (fun h => pmf_bind_finite _ (hF h) _
      (fun p => pmf_map_finite _ (Set.toFinite _) _))

theorem histLaw_length {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (t : ℕ) (h : History n) (hh : h ∈ (histLaw F A t).support) : h.length = t := by
  induction t generalizing h with
  | zero => simpa [histLaw] using hh
  | succ t ih =>
    obtain ⟨h₀, hh₀, hs⟩ := (PMF.mem_support_bind_iff _ _ h).mp hh
    obtain ⟨p, _, hs⟩ := (PMF.mem_support_bind_iff _ _ h).mp hs
    obtain ⟨j, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hs
    simp [ih h₀ hh₀]

theorem histLaw_mean_succ {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (hF : finiteForecaster F) (t : ℕ) (f : History n → ℝ) :
    pmfMean (histLaw F A (t+1)) f = pmfMean (histLaw F A t)
      (fun h => pmfMean (F h) (fun p => pmfMean (A h) (fun j => f (h ++ [(p,j)])))) := by
  rw [histLaw, pmfMean_bind _ (histLaw_finite F A hF t) _
    (fun h => pmf_bind_finite _ (hF h) _ (fun p => pmf_map_finite _ (Set.toFinite _) _))]
  apply pmfMean_congr
  intro h _
  rw [pmfMean_bind _ (hF h) _ (fun p => pmf_map_finite _ (Set.toFinite _) _)]
  apply pmfMean_congr
  intro p _
  exact pmfMean_map _ (Set.toFinite _) _ _

theorem histLaw_drift_bound {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (hF : finiteForecaster F) (V : History n → ℝ) (c : ℝ) (hzero : V [] = 0)
    (hstep : ∀ h, pmfMean (F h) (fun p => pmfMean (A h)
      (fun j => V (h ++ [(p,j)]))) ≤ V h + c) (t : ℕ) :
    pmfMean (histLaw F A t) V ≤ c * t := by
  induction t with
  | zero => simp [histLaw, pmfMean_pure, hzero]
  | succ t ih =>
    rw [histLaw_mean_succ F A hF t V]
    calc
      _ ≤ pmfMean (histLaw F A t) (fun h => V h + c) :=
        pmfMean_mono _ (histLaw_finite F A hF t) (fun h _ => hstep h)
      _ = pmfMean (histLaw F A t) V + c := by
        rw [pmfMean_add _ (histLaw_finite F A hF t), pmfMean_const]
      _ ≤ c * ((t+1:ℕ):ℝ) := by push_cast; linarith


end CalibratedCE.ForecastProof
end

/- Complete checked body: EpochSchedule -/
section

open scoped BigOperators Topology
open Filter

namespace CalibratedCE.ForecastProof

def epochStart (b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => epochStart b r + 1 + (r+1) * ∑ j ∈ Finset.range (r+2), b j

lemma epochStart_zero (b : ℕ → ℕ) : epochStart b 0 = 0 := rfl

lemma epochStart_strict (b : ℕ → ℕ) : StrictMono (epochStart b) := by
  apply strictMono_nat_of_lt_succ
  intro r
  simp only [epochStart]
  omega

lemma le_epochStart (b : ℕ → ℕ) (r : ℕ) : r ≤ epochStart b r := by
  induction r with
  | zero => simp [epochStart]
  | succ r ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (epochStart_strict b (Nat.lt_succ_self r)))

lemma epochStart_budget (b : ℕ → ℕ) (r : ℕ) :
    r * (∑ j ∈ Finset.range (r+1), b j) ≤ epochStart b r := by
  cases r with
  | zero => simp [epochStart]
  | succ r =>
    change (r+1) * (∑ j ∈ Finset.range (r+2), b j) ≤
      epochStart b r + 1 + (r+1) * ∑ j ∈ Finset.range (r+2), b j
    omega

def epochIndex (T : ℕ → ℕ) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun r => T r ≤ t) t

lemma le_start_of_strict {T : ℕ → ℕ} (hT : StrictMono T) (r : ℕ) : r ≤ T r := by
  induction r with
  | zero => omega
  | succ r ih =>
    exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hT (Nat.lt_succ_self r)))

lemma epochIndex_lower {T : ℕ → ℕ} (h0 : T 0 = 0) (t : ℕ) :
    T (epochIndex T t) ≤ t := by
  exact Nat.findGreatest_spec (P := fun r => T r ≤ t) (Nat.zero_le t) (by simp [h0])

lemma epochIndex_upper {T : ℕ → ℕ} (hT : StrictMono T) (t : ℕ) :
    t < T (epochIndex T t + 1) := by
  by_contra hn
  have hp : T (epochIndex T t + 1) ≤ t := by omega
  have hi : epochIndex T t + 1 ≤ t := (le_start_of_strict hT _).trans hp
  have hc : epochIndex T t + 1 ≤ epochIndex T t := Nat.le_findGreatest hi hp
  omega

lemma epochIndex_eq {T : ℕ → ℕ} (hT : StrictMono T)
    {r t : ℕ} (hlo : T r ≤ t) (hhi : t < T (r+1)) : epochIndex T t = r := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨(le_start_of_strict hT r).trans hlo, fun _ => hlo, ?_⟩
  intro j hj _ ht
  have hc : T (r+1) ≤ T j := hT.monotone (by omega)
  omega

lemma epochIndex_tendsto {T : ℕ → ℕ} (hT : StrictMono T) :
    Tendsto (epochIndex T) atTop atTop := by
  apply tendsto_atTop.2
  intro r
  filter_upwards [eventually_ge_atTop (T r)] with t ht
  exact Nat.le_findGreatest ((le_start_of_strict hT r).trans ht) ht

def epochLength (T : ℕ → ℕ) (r : ℕ) : ℕ := T (r+1) - T r

lemma epochLength_pos {T : ℕ → ℕ} (hT : StrictMono T) (r : ℕ) :
    0 < epochLength T r := Nat.sub_pos_of_lt (hT (Nat.lt_succ_self r))

lemma epochLength_sum {T : ℕ → ℕ} (hT : Monotone T) (h0 : T 0 = 0) (r : ℕ) :
    ∑ j ∈ Finset.range r, epochLength T j = T r := by
  induction r with
  | zero => simp [h0]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih]
    dsimp [epochLength]
    have hh : T r ≤ T (r+1) := hT (by omega)
    omega

lemma epoch_budget_real (b : ℕ → ℕ) (t : ℕ)
    (hr : 0 < epochIndex (epochStart b) t) :
    (∑ j ∈ Finset.range (epochIndex (epochStart b) t + 1), (b j : ℝ)) /
      (t : ℝ) ≤ 1 / (epochIndex (epochStart b) t : ℝ) := by
  let r := epochIndex (epochStart b) t
  have hlow := epochIndex_lower (epochStart_zero b) t
  have hbudget := epochStart_budget b r
  have hrt : r ≤ t := (le_epochStart b r).trans hlow
  have ht : (0 : ℝ) < t := by exact_mod_cast lt_of_lt_of_le hr hrt
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  apply (div_le_div_iff₀ ht hrR).mpr
  have hb : (r : ℝ) * (∑ j ∈ Finset.range (r+1), (b j : ℝ)) ≤ t := by
    exact_mod_cast hbudget.trans hlow
  simpa only [one_mul, mul_one, mul_comm, r] using hb

end CalibratedCE.ForecastProof

end

/- Complete checked body: EpochPolicy -/
section

open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

noncomputable def epochForecaster {n : ℕ} (T : ℕ → ℕ) (F : ℕ → Forecaster n) : Forecaster n :=
  fun h => F (epochIndex T h.length) (h.drop (T (epochIndex T h.length)))

lemma epochForecaster_finite {n : ℕ} (T : ℕ → ℕ) (F : ℕ → Forecaster n)
    (hF : ∀ r, finiteForecaster (F r)) : finiteForecaster (epochForecaster T F) := by
  intro h
  exact hF (epochIndex T h.length) _

lemma epochForecaster_valid {n : ℕ} (T : ℕ → ℕ) (F : ℕ → Forecaster n)
    (hF : ∀ r h p, p ∈ (F r h).support → IsDist p) :
    ∀ h p, p ∈ (epochForecaster T F h).support → IsDist p := by
  intro h p hp
  exact hF (epochIndex T h.length) _ p hp

lemma epochForecaster_append {n : ℕ} {T : ℕ → ℕ} (hT : StrictMono T)
    (F : ℕ → Forecaster n) (r : ℕ) (h g : History n)
    (hh : h.length = T r) (hg : g.length < epochLength T r) :
    epochForecaster T F (h ++ g) = F r g := by
  have hlo : T r ≤ (h ++ g).length := by simp [hh]
  have hhi : (h ++ g).length < T (r+1) := by
    simp only [List.length_append, hh]
    dsimp [epochLength] at hg
    omega
  have hi := epochIndex_eq hT hlo hhi
  simp only [epochForecaster, hi]
  rw [← hh]
  simp

end CalibratedCE.ForecastProof

end

/- Complete checked body: EpochLimits -/
section

open scoped BigOperators Topology
open Filter

namespace CalibratedCE.ForecastProof

noncomputable def epochAccuracy (r : ℕ) : ℝ := 1 / ((r : ℝ) + 1)

lemma epochAccuracy_pos (r : ℕ) : 0 < epochAccuracy r := by
  unfold epochAccuracy
  positivity

lemma epochAccuracy_le_one (r : ℕ) : epochAccuracy r ≤ 1 := by
  unfold epochAccuracy
  apply (div_le_one₀ (by positivity)).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg r)

lemma epochAccuracy_antitone : Antitone epochAccuracy := by
  intro r s hrs
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hrs 1

lemma epochAccuracy_tendsto : Tendsto epochAccuracy atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def epochWeighted (T : ℕ → ℕ) (t : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (epochIndex T t), epochAccuracy j * (epochLength T j : ℝ)) +
    epochAccuracy (epochIndex T t) * ((t - T (epochIndex T t) : ℕ) : ℝ)

lemma epoch_prefix_bound {T : ℕ → ℕ} (hT : StrictMono T) (h0 : T 0 = 0)
    (J r : ℕ) (hJr : J ≤ r) :
    (∑ j ∈ Finset.range r, epochAccuracy j * (epochLength T j : ℝ)) ≤
      (T J : ℝ) + epochAccuracy J * (T r : ℝ) := by
  induction r, hJr using Nat.le_induction with
  | base =>
    have hs : (∑ j ∈ Finset.range J, epochAccuracy j * (epochLength T j : ℝ)) ≤
        (T J : ℝ) := by
      calc
        _ ≤ ∑ j ∈ Finset.range J, (epochLength T j : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_of_le_one_left (by positivity) (epochAccuracy_le_one j)
        _ = _ := by exact_mod_cast epochLength_sum hT.monotone h0 J
    have hn : 0 ≤ epochAccuracy J * (T J : ℝ) :=
      mul_nonneg (epochAccuracy_pos J).le (by positivity)
    linarith
  | succ r hJr ih =>
    rw [Finset.sum_range_succ]
    have hm : epochAccuracy r * (epochLength T r : ℝ) ≤
        epochAccuracy J * (epochLength T r : ℝ) :=
      mul_le_mul_of_nonneg_right (epochAccuracy_antitone hJr) (by positivity)
    have ht : (T (r+1) : ℝ) = (T r : ℝ) + (epochLength T r : ℝ) := by
      have hn := hT.monotone (Nat.le_succ r)
      dsimp [epochLength]
      rw [Nat.cast_sub hn]
      ring
    rw [ht]
    nlinarith

lemma epochWeighted_bound {T : ℕ → ℕ} (hT : StrictMono T) (h0 : T 0 = 0)
    (J t : ℕ) (hJ : J ≤ epochIndex T t) :
    epochWeighted T t ≤ (T J : ℝ) + epochAccuracy J * (t : ℝ) := by
  have hp := epoch_prefix_bound hT h0 J (epochIndex T t) hJ
  have hm : epochAccuracy (epochIndex T t) * ((t-T (epochIndex T t) : ℕ) : ℝ) ≤
      epochAccuracy J * ((t-T (epochIndex T t) : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right (epochAccuracy_antitone hJ) (by positivity)
  rw [Nat.cast_sub (epochIndex_lower h0 t)] at hm
  unfold epochWeighted
  rw [Nat.cast_sub (epochIndex_lower h0 t)]
  nlinarith

noncomputable def epochError (b : ℕ → ℕ) (t : ℕ) : ℝ :=
  (epochWeighted (epochStart b) t +
    ∑ j ∈ Finset.range (epochIndex (epochStart b) t + 1), (b j : ℝ)) / (t : ℝ)

lemma epochError_nonneg (b : ℕ → ℕ) (t : ℕ) : 0 ≤ epochError b t := by
  unfold epochError epochWeighted
  apply div_nonneg _ (by positivity)
  apply add_nonneg
  · apply add_nonneg
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (epochAccuracy_pos j).le (by positivity))
    · exact mul_nonneg (epochAccuracy_pos _).le (by positivity)
  · positivity

lemma epochError_bound (b : ℕ → ℕ) (J t : ℕ)
    (hJ : J ≤ epochIndex (epochStart b) t)
    (hr : 0 < epochIndex (epochStart b) t) :
    epochError b t ≤ (epochStart b J : ℝ) / (t : ℝ) +
      epochAccuracy J + 1 / (epochIndex (epochStart b) t : ℝ) := by
  have hw := epochWeighted_bound (epochStart_strict b) (epochStart_zero b) J t hJ
  have hb := epoch_budget_real b t hr
  have hrt : epochIndex (epochStart b) t ≤ t := Nat.findGreatest_le t
  have ht : (0 : ℝ) < t := by exact_mod_cast lt_of_lt_of_le hr hrt
  have hwd := div_le_div_of_nonneg_right hw ht.le
  rw [add_div, mul_div_cancel_right₀ _ ht.ne'] at hwd
  unfold epochError
  rw [add_div]
  linarith

theorem epochError_tendsto (b : ℕ → ℕ) : Tendsto (epochError b) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun t => ha.trans_le (epochError_nonneg b t))
  · intro ε hε
    obtain ⟨J, hJ⟩ := (epochAccuracy_tendsto.eventually (gt_mem_nhds (half_pos hε))).exists
    have hi := epochIndex_tendsto (epochStart_strict b)
    have hsmall : Tendsto (fun t : ℕ => (epochStart b J : ℝ) / (t : ℝ) +
        1 / (epochIndex (epochStart b) t : ℝ)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (epochStart b J : ℝ)).add
        (tendsto_one_div_atTop_nhds_zero_nat.comp hi)
    filter_upwards [hsmall.eventually (gt_mem_nhds (half_pos hε)),
      hi.eventually (eventually_ge_atTop J), hi.eventually (eventually_ge_atTop 1)] with t ht hJt hrt
    have hb := epochError_bound b J t hJt hrt
    linarith

end CalibratedCE.ForecastProof

end

/- Complete checked body: EpochRecurrence -/
section

open scoped BigOperators

namespace CalibratedCE.ForecastProof

theorem epoch_recurrence_bound {T : ℕ → ℕ} (hT : StrictMono T) (h0 : T 0 = 0)
    (b : ℕ → ℕ) (E : ℕ → ℝ) (hE0 : E 0 = 0)
    (hstep : ∀ r s, s ≤ epochLength T r →
      E (T r + s) ≤ E (T r) + epochAccuracy r * (s : ℝ) + (b r : ℝ))
    (t : ℕ) : E t ≤ epochWeighted T t +
      ∑ j ∈ Finset.range (epochIndex T t + 1), (b j : ℝ) := by
  have hprefix : ∀ r, E (T r) ≤
      (∑ j ∈ Finset.range r, epochAccuracy j * (epochLength T j : ℝ)) +
        ∑ j ∈ Finset.range r, (b j : ℝ) := by
    intro r
    induction r with
    | zero => simp [h0, hE0]
    | succ r ih =>
      have hs := hstep r (epochLength T r) le_rfl
      have ht : T r + epochLength T r = T (r+1) := by
        dsimp [epochLength]
        have hh : T r ≤ T (r+1) := hT.monotone (by omega)
        omega
      rw [ht] at hs
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      linarith
  let r := epochIndex T t
  have hl : T r ≤ t := epochIndex_lower h0 t
  have hu : t < T (r+1) := epochIndex_upper hT t
  have hs : t - T r ≤ epochLength T r := by
    dsimp [epochLength]
    omega
  have hm := hstep r (t-T r) hs
  rw [Nat.add_sub_of_le hl] at hm
  have hp := hprefix r
  change E t ≤ epochWeighted T t + ∑ j ∈ Finset.range (r+1), (b j : ℝ)
  rw [Finset.sum_range_succ]
  dsimp [epochWeighted, r] at *
  linarith

theorem epoch_recurrence_tendsto (b : ℕ → ℕ) (E : ℕ → ℝ)
    (hE0 : E 0 = 0) (hEn : ∀ t, 0 ≤ E t)
    (hstep : ∀ r s, s ≤ epochLength (epochStart b) r →
      E (epochStart b r + s) ≤ E (epochStart b r) +
        epochAccuracy r * (s : ℝ) + (b r : ℝ)) :
    Filter.Tendsto (fun t : ℕ => E t / (t : ℝ)) Filter.atTop (nhds 0) := by
  apply squeeze_zero
  · intro t
    exact div_nonneg (hEn t) (by positivity)
  · intro t
    exact div_le_div_of_nonneg_right
      (epoch_recurrence_bound (epochStart_strict b) (epochStart_zero b) b E hE0 hstep t)
      (by positivity)
  · exact epochError_tendsto b

end CalibratedCE.ForecastProof

end

/- Complete checked body: ScoreMass -/
section

open scoped BigOperators
open Finset

namespace CalibratedCE.ForecastProof

open CalibratedCE.Forecast

noncomputable def outcomeCount {n : ℕ}
    (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  ((h.filter (fun e => e.1 = p ∧ e.2 = j)).length : ℝ)

noncomputable def discrepancy {n : ℕ}
    (h : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) (j : Fin n) : ℝ :=
  outcomeCount h p j - p j * (NH h p : ℝ)

noncomputable def scoreMass {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) : ℝ :=
  ∑ p ∈ (h.map Prod.fst).toFinset, ∑ j : Fin n, |discrepancy h p j|

lemma outcomeCount_nonneg {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (j : Fin n) : 0 ≤ outcomeCount h p j := by
  unfold outcomeCount
  positivity

lemma outcomeCount_le {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (j : Fin n) : outcomeCount h p j ≤ (NH h p : ℝ) := by
  classical
  have hc : List.countP (fun e => decide (e.1 = p ∧ e.2 = j)) h ≤
      List.countP (fun e => decide (e.1 = p)) h :=
    List.countP_mono_left (by intro e _ he; simp_all)
  simpa only [List.countP_eq_length_filter, outcomeCount, NH] using
    (Nat.cast_le (α := ℝ)).mpr hc

lemma outcomeCount_append {n : ℕ} (h g : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (j : Fin n) :
    outcomeCount (h ++ g) p j = outcomeCount h p j + outcomeCount g p j := by
  classical
  simp [outcomeCount, List.filter_append]

lemma nh_append {n : ℕ} (h g : List ((Fin n → ℝ) × Fin n)) (p : Fin n → ℝ) :
    NH (h ++ g) p = NH h p + NH g p := by
  classical
  simp [NH, List.filter_append]

lemma discrepancy_append {n : ℕ} (h g : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (j : Fin n) :
    discrepancy (h ++ g) p j = discrepancy h p j + discrepancy g p j := by
  rw [discrepancy, outcomeCount_append, nh_append]
  push_cast
  simp only [discrepancy]
  ring

lemma nh_zero_of_not_mem {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (hp : p ∉ (h.map Prod.fst).toFinset) : NH h p = 0 := by
  classical
  have he : h.filter (fun e => e.1 = p) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp only [decide_eq_true_eq]
    intro hep
    apply hp
    simp only [List.mem_toFinset, List.mem_map]
    exact ⟨e, he, hep⟩
  simp [NH, he]

lemma discrepancy_zero_of_not_mem {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (hp : p ∉ (h.map Prod.fst).toFinset) (j : Fin n) :
    discrepancy h p j = 0 := by
  have hz := nh_zero_of_not_mem h p hp
  have hc := outcomeCount_le h p j
  have hn := outcomeCount_nonneg h p j
  rw [hz, Nat.cast_zero] at hc
  simp [discrepancy, hz, le_antisymm hc hn]

lemma scoreMass_nonneg {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) :
    0 ≤ scoreMass h := by
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))

lemma scoreMass_eq_sum {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (s : Finset (Fin n → ℝ)) (hs : (h.map Prod.fst).toFinset ⊆ s) :
    scoreMass h = ∑ p ∈ s, ∑ j : Fin n, |discrepancy h p j| := by
  classical
  apply Finset.sum_subset hs
  intro p _ hp
  simp [discrepancy_zero_of_not_mem h p hp]

lemma scoreMass_append_le {n : ℕ} (h g : List ((Fin n → ℝ) × Fin n)) :
    scoreMass (h ++ g) ≤ scoreMass h + scoreMass g := by
  classical
  let s := (h.map Prod.fst).toFinset ∪ (g.map Prod.fst).toFinset
  rw [scoreMass_eq_sum h s Finset.subset_union_left,
    scoreMass_eq_sum g s Finset.subset_union_right, ← Finset.sum_add_distrib]
  change (∑ p ∈ ((h ++ g).map Prod.fst).toFinset,
    ∑ j : Fin n, |discrepancy (h ++ g) p j|) ≤ _
  simp only [List.map_append, List.toFinset_append]
  apply Finset.sum_le_sum
  intro p _
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun j _ => by
    rw [discrepancy_append]
    exact abs_add_le _ _)

lemma rhoH_mul_nh {n : ℕ} (h : List ((Fin n → ℝ) × Fin n))
    (p : Fin n → ℝ) (j : Fin n) :
    rhoH h p j * (NH h p : ℝ) = outcomeCount h p j := by
  classical
  by_cases hz : NH h p = 0
  · have hc := outcomeCount_le h p j
    have hn := outcomeCount_nonneg h p j
    rw [hz, Nat.cast_zero] at hc
    simp [hz, le_antisymm hc hn]
  · have hr : (NH h p : ℝ) ≠ 0 := by exact_mod_cast hz
    simp only [rhoH, hz, if_false, outcomeCount]
    exact div_mul_cancel₀ _ hr

lemma score_eq_mass_div {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) :
    calibScoreH h = scoreMass h / (h.length : ℝ) := by
  classical
  unfold calibScoreH scoreMass
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [← abs_of_nonneg (show (0 : ℝ) ≤ (NH h p : ℝ) by positivity), ← abs_mul]
  congr 1
  rw [sub_mul, rhoH_mul_nh]
  rfl

lemma scoreMass_nil {n : ℕ} : scoreMass ([] : List ((Fin n → ℝ) × Fin n)) = 0 := by
  simp [scoreMass]

lemma scoreMass_eq_length_mul {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) :
    scoreMass h = (h.length : ℝ) * calibScoreH h := by
  by_cases hz : h = []
  · subst h
    simp [scoreMass_nil]
  · rw [score_eq_mass_div]
    have hn : (h.length : ℝ) ≠ 0 := by
      exact_mod_cast (List.length_eq_zero_iff.not.mpr hz)
    field_simp

end CalibratedCE.ForecastProof

end

/- Complete checked body: HistorySegments -/
section

open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

noncomputable def continueLaw {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (h : History n) : ℕ → PMF (History n)
  | 0 => PMF.pure h
  | s+1 => (continueLaw F A h s).bind (fun g =>
      (F g).bind (fun p => (A g).map (fun j => g ++ [(p,j)])))

theorem continueLaw_finite {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (hF : finiteForecaster F) (h : History n) (s : ℕ) :
    (continueLaw F A h s).support.Finite := by
  induction s with
  | zero => simp [continueLaw]
  | succ s ih => exact pmf_bind_finite _ ih _ (fun g => pmf_bind_finite _ (hF g) _
      (fun p => pmf_map_finite _ (Set.toFinite _) _))

theorem histLaw_add {n : ℕ} (F : Forecaster n) (A : Opponent n) (t s : ℕ) :
    histLaw F A (t+s) = (histLaw F A t).bind (fun h => continueLaw F A h s) := by
  induction s with
  | zero => simp [continueLaw]
  | succ s ih =>
    rw [Nat.add_succ, histLaw, ih, PMF.bind_bind]
    rfl

theorem continueLaw_eq_map {n : ℕ} (F : Forecaster n) (A : Opponent n)
    (h : History n) (s : ℕ) :
    continueLaw F A h s = (histLaw (fun g => F (h ++ g)) (fun g => A (h ++ g)) s).map
      (fun g => h ++ g) := by
  induction s with
  | zero => simp [continueLaw, histLaw, PMF.pure_map]
  | succ s ih =>
    rw [continueLaw, ih, PMF.bind_map, histLaw, PMF.map_bind]
    congr 1
    funext g
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, List.append_assoc]

theorem pmf_bind_congr_support {α β : Type*} (p : PMF α) (f g : α → PMF β)
    (h : ∀ a ∈ p.support, f a = g a) : p.bind f = p.bind g := by
  ext b
  simp only [PMF.bind_apply]
  apply tsum_congr
  intro a
  by_cases ha : a ∈ p.support
  · rw [h a ha]
  · rw [(p.apply_eq_zero_iff a).2 ha]
    simp

theorem histLaw_congr_until {n : ℕ} (F G : Forecaster n) (A : Opponent n) (s : ℕ)
    (hFG : ∀ h : History n, h.length < s → F h = G h) :
    histLaw F A s = histLaw G A s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [histLaw, histLaw, ih (fun h hh => hFG h (Nat.lt_succ_of_lt hh))]
    apply pmf_bind_congr_support
    intro h hh
    rw [hFG h (by rw [histLaw_length G A s h hh]; omega)]

theorem segment_mass_bound {n : ℕ} (F G : Forecaster n) (A : Opponent n)
    (hF : finiteForecaster F) (hG : finiteForecaster G)
    (η B : ℝ) (hbound : ∀ A' : Opponent n, ∀ s,
      pmfMean (histLaw G A' s) scoreMass ≤ η*s+B)
    (t s : ℕ) (hFG : ∀ h : History n, h.length = t → ∀ g : History n,
      g.length < s → F (h ++ g) = G g) :
    pmfMean (histLaw F A (t+s)) scoreMass ≤
      pmfMean (histLaw F A t) scoreMass + η*s+B := by
  rw [histLaw_add, pmfMean_bind _ (histLaw_finite F A hF t) _
    (fun h => continueLaw_finite F A hF h s)]
  have hb : ∀ h ∈ (histLaw F A t).support,
      pmfMean (continueLaw F A h s) scoreMass ≤ scoreMass h + (η*s+B) := by
    intro h hh
    rw [continueLaw_eq_map]
    have he : histLaw (fun g => F (h ++ g)) (fun g => A (h ++ g)) s =
        histLaw G (fun g => A (h ++ g)) s :=
      histLaw_congr_until _ _ _ s (hFG h (histLaw_length F A t h hh))
    rw [he, pmfMean_map _ (histLaw_finite G _ hG s)]
    calc
      _ ≤ pmfMean (histLaw G (fun g => A (h ++ g)) s) (fun g => scoreMass h + scoreMass g) :=
        pmfMean_mono _ (histLaw_finite G _ hG s) (fun g _ => scoreMass_append_le h g)
      _ = scoreMass h + pmfMean (histLaw G (fun g => A (h ++ g)) s) scoreMass := by
        rw [pmfMean_add _ (histLaw_finite G _ hG s), pmfMean_const]
      _ ≤ scoreMass h + (η*s+B) := by linarith [hbound (fun g => A (h ++ g)) s]
  calc
    _ ≤ pmfMean (histLaw F A t) (fun h => scoreMass h + (η*s+B)) :=
      pmfMean_mono _ (histLaw_finite F A hF t) hb
    _ = _ := by rw [pmfMean_add _ (histLaw_finite F A hF t), pmfMean_const]; ring


end CalibratedCE.ForecastProof
end

/- Complete checked body: PMFMarkov -/
section

open scoped BigOperators Topology
open Filter Classical

namespace CalibratedCE.ForecastProof

lemma pmf_outer_le_one {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≤ 1 := by
  calc
    p.toOuterMeasure s ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ s)
    _ = 1 := by rw [PMF.toOuterMeasure_apply]; simp

lemma pmf_outer_ne_top {α : Type*} (p : PMF α) (s : Set α) :
    p.toOuterMeasure s ≠ ⊤ := ne_of_lt ((pmf_outer_le_one p s).trans_lt (by simp))

lemma pmf_outer_toReal {α : Type*} (p : PMF α) (hp : p.support.Finite) (s : Set α) :
    (p.toOuterMeasure s).toReal = pmfMean p (fun a => if a ∈ s then 1 else 0) := by
  classical
  have he : p.toOuterMeasure s = ∑ a ∈ hp.toFinset, s.indicator p a := by
    rw [PMF.toOuterMeasure_apply]
    apply tsum_eq_sum
    intro a ha
    have hpa : p a = 0 := (p.apply_eq_zero_iff a).mpr (by simpa using ha)
    by_cases hs : a ∈ s <;> simp [hs, hpa]
  have hn : ∀ a ∈ hp.toFinset, s.indicator p a ≠ ⊤ := by
    intro a _
    by_cases hs : a ∈ s <;> simp [hs, p.apply_ne_top]
  rw [he, ENNReal.toReal_sum hn, pmfMean_eq_sum p _ hp.toFinset (by simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hs : a ∈ s <;> simp [hs]

lemma pmf_probability_lower {α : Type*} (p : PMF α) (hp : p.support.Finite)
    (f : α → ℝ) (hf : ∀ a ∈ p.support, 0 ≤ f a) (ε : ℝ) (hε : 0 < ε) :
    1 - pmfMean p f / ε ≤ (p.toOuterMeasure {a | f a < ε}).toReal := by
  classical
  rw [pmf_outer_toReal p hp]
  have hm : pmfMean p (fun a => 1 + (-ε⁻¹) * f a) ≤
      pmfMean p (fun a => if a ∈ {a | f a < ε} then 1 else 0) := by
    apply pmfMean_mono p hp
    intro a ha
    have hfa := hf a ha
    have hi : 0 < ε⁻¹ := inv_pos.mpr hε
    by_cases hs : f a < ε
    · simp only [Set.mem_ofPred_eq, hs, if_true]
      nlinarith
    · have hh : ε ≤ f a := le_of_not_gt hs
      have hb : 1 ≤ ε⁻¹ * f a := (le_inv_mul_iff₀ hε).mpr (by simpa using hh)
      simp only [Set.mem_ofPred_eq, hs, if_false]
      nlinarith
  rw [pmfMean_add p hp, pmfMean_const, pmfMean_smul] at hm
  simpa only [div_eq_mul_inv, neg_mul, sub_eq_add_neg, mul_comm] using hm

theorem pmf_probability_tendsto_one {α : Type*} (p : ℕ → PMF α)
    (hp : ∀ t, (p t).support.Finite) (f : α → ℝ)
    (hf : ∀ t a, a ∈ (p t).support → 0 ≤ f a)
    (hm : Tendsto (fun t => pmfMean (p t) f) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun t => (p t).toOuterMeasure {a | f a < ε}) atTop (𝓝 1) := by
  apply (ENNReal.tendsto_toReal_iff (fun t => pmf_outer_ne_top (p t) _) ENNReal.one_ne_top).mp
  have hl : Tendsto (fun t => 1 - pmfMean (p t) f / ε) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub (hm.div_const ε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds
  · intro t
    exact pmf_probability_lower (p t) (hp t) f (hf t) ε hε
  · intro t
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using pmf_outer_le_one (p t) _)

end CalibratedCE.ForecastProof

end

/- Complete checked body: EpochAssembly -/
section

open scoped BigOperators Topology
open Filter CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

theorem calibrated_of_affine_bounds (n : ℕ)
    (hlocal : ∀ η : ℝ, 0 < η → ∃ F : Forecaster n, ∃ B : ℝ,
      finiteForecaster F ∧ (∀ h p, p ∈ (F h).support → IsDist p) ∧
      ∀ A : Opponent n, ∀ t : ℕ, pmfMean (histLaw F A t) scoreMass ≤ η*t+B) :
    ∃ F : Forecaster n,
      (∀ h p, p ∈ (F h).support → IsDist p) ∧
      ∀ A : Opponent n, ∀ ε : ℝ, 0 < ε →
        Tendsto (fun t : ℕ => (histLaw F A t).toOuterMeasure {h | calibScoreH h < ε})
          atTop (𝓝 1) := by
  classical
  choose G B hG hvalid hbound using fun r => hlocal (epochAccuracy r) (epochAccuracy_pos r)
  let b : ℕ → ℕ := fun r => ⌈B r⌉₊
  let T := epochStart b
  let F := epochForecaster T G
  have hF : finiteForecaster F := epochForecaster_finite T G hG
  refine ⟨F, epochForecaster_valid T G hvalid, ?_⟩
  intro A ε hε
  let E : ℕ → ℝ := fun t => pmfMean (histLaw F A t) scoreMass
  have hE0 : E 0 = 0 := by simp [E, histLaw, pmfMean_pure, scoreMass_nil]
  have hEn : ∀ t, 0 ≤ E t := fun t =>
    pmfMean_nonneg _ (histLaw_finite F A hF t) (fun h _ => scoreMass_nonneg h)
  have hstep : ∀ r s, s ≤ epochLength T r →
      E (T r+s) ≤ E (T r) + epochAccuracy r * (s : ℝ) + (b r : ℝ) := by
    intro r s hs
    have hb := segment_mass_bound F (G r) A hF (hG r) (epochAccuracy r) (B r)
      (hbound r) (T r) s (by
        intro h hh g hg
        exact epochForecaster_append (epochStart_strict b) G r h g hh (hg.trans_le hs))
    have hceil : B r ≤ (b r : ℝ) := Nat.le_ceil _
    dsimp [E]
    linarith
  have hmeanMass : Tendsto (fun t : ℕ => E t / (t : ℝ)) atTop (𝓝 0) :=
    epoch_recurrence_tendsto b E hE0 hEn hstep
  have hmeanScore : ∀ t, pmfMean (histLaw F A t) calibScoreH = E t / (t : ℝ) := by
    intro t
    calc
      _ = pmfMean (histLaw F A t) (fun h => (t : ℝ)⁻¹ * scoreMass h) := by
        apply pmfMean_congr
        intro h hh
        rw [score_eq_mass_div, histLaw_length F A t h hh]
        ring
      _ = _ := by rw [pmfMean_smul]; dsimp [E]; ring
  apply pmf_probability_tendsto_one (fun t => histLaw F A t)
    (fun t => histLaw_finite F A hF t) calibScoreH
    (fun _ h _ => by rw [score_eq_mass_div]; exact div_nonneg (scoreMass_nonneg h) (by positivity))
    _ ε hε
  simpa only [hmeanScore] using hmeanMass

end CalibratedCE.ForecastProof

end

/- Complete checked body: AttributedCalibration -/
section

-- BEGIN ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_flow_conservation_solvable.lean
-- Prove2me | solution 1 for CalibratedCE.Forecast.flow_conservation_solvable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:31:15.661104+00:00
-- url     : https://prove2.me/submissions/56ead235-ad63-4851-929d-a84601a1a428


namespace CalibratedCE.Forecast

theorem aux_fcs_kernel (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ) :
    ∃ v : Fin k → ℝ, v ≠ 0 ∧ ∀ i, v i * ∑ j, R i j = ∑ j, v j * R j i := by
  classical
  let A : Matrix (Fin k) (Fin k) ℝ := fun i j => R j i - if i = j then ∑ l, R i l else 0
  have hdet : A.det = 0 := by
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      have := congrFun h ⟨0, hk⟩
      simp at this
    · funext j
      simp [Matrix.vecMul, dotProduct, A, Finset.sum_sub_distrib]
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv0, fun i => ?_⟩
  have := congrFun hv i
  simp [Matrix.mulVec, dotProduct, A, sub_mul, Finset.sum_sub_distrib] at this
  have h2 : ∑ j, R j i * v j = ∑ j, v j * R j i :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  linarith

theorem aux_fcs_abs (k : ℕ) (R : Fin k → Fin k → ℝ) (hR : ∀ i j, 0 ≤ R i j) (v : Fin k → ℝ)
    (hv : ∀ i, v i * ∑ j, R i j = ∑ j, v j * R j i) :
    ∀ i, |v i| * ∑ j, R i j = ∑ j, |v j| * R j i := by
  have hle : ∀ i ∈ Finset.univ, |v i| * ∑ j, R i j ≤ ∑ j, |v j| * R j i := by
    intro i _
    have hs : 0 ≤ ∑ j, R i j := Finset.sum_nonneg (fun j _ => hR i j)
    calc |v i| * ∑ j, R i j = |v i * ∑ j, R i j| := by rw [abs_mul, abs_of_nonneg hs]
      _ = |∑ j, v j * R j i| := by rw [hv i]
      _ ≤ ∑ j, |v j * R j i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |v j| * R j i := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [abs_mul, abs_of_nonneg (hR j i)]
  have heq : ∑ i, |v i| * ∑ j, R i j = ∑ i, ∑ j, |v j| * R j i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
  have := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro i
  exact this i (Finset.mem_univ i)

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem checked_flow_conservation_solvable (k : ℕ) (hk : 0 < k) (R : Fin k → Fin k → ℝ)
    (hR : ∀ i j, 0 ≤ R i j) :
    ∃ w : Fin k → ℝ, IsDist w ∧ ∀ i, w i * ∑ j, R i j = ∑ j, w j * R j i := by
  obtain ⟨v, hv0, hv⟩ := aux_fcs_kernel k hk R
  have habs := aux_fcs_abs k R hR v hv
  set S := ∑ i, |v i| with hS
  have hSpos : 0 < S := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv0 (funext h)
    calc 0 < |v i| := abs_pos.mpr hi
      _ ≤ S := Finset.single_le_sum (f := fun i => |v i|) (fun j _ => abs_nonneg (v j))
          (Finset.mem_univ i)
  refine ⟨fun i => |v i| / S, ⟨fun a => div_nonneg (abs_nonneg _) hSpos.le, ?_⟩, fun i => ?_⟩
  · rw [← Finset.sum_div]; exact div_self hSpos.ne'
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    rw [habs i]
-- END ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_flow_conservation_solvable.lean

-- BEGIN ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_no_regret.lean
-- Prove2me | solution 1 for CalibratedCE.Forecast.no_regret
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:33:04.574359+00:00
-- url     : https://prove2.me/submissions/a665a5c3-6a14-458a-84ee-8e57f41cefe4


namespace CalibratedCE.Forecast

lemma aux_nr_sq (a d : ℝ) : (max 0 (a + d))^2 ≤ (max 0 a + d)^2 := by
  rcases le_or_gt (a + d) 0 with h | h
  · rw [max_eq_left h]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity
  · rw [max_eq_right h.le]
    have h1 : a ≤ max 0 a := le_max_right _ _
    exact pow_le_pow_left₀ h.le (by linarith) 2

lemma aux_nr_Rg_succ {k : ℕ} (L w : ℕ → Fin k → ℝ) (t : ℕ) (i j : Fin k) :
    Rg L w (t+1) i j = max 0 (S L w t i j + w t i * (L t i - L t j)) := by
  simp [Rg, S, Finset.sum_range_succ]

lemma aux_nr_w_le {k : ℕ} (p : Fin k → ℝ) (hp : IsDist p) (i : Fin k) : p i ≤ 1 := by
  rw [← hp.2]
  exact Finset.single_le_sum (fun a _ => hp.1 a) (Finset.mem_univ i)

lemma aux_nr_step (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (t : ℕ) :
    ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (Rg L w t i j)^2 + k := by
  set R := Rg L w t with hR
  set d : Fin k → Fin k → ℝ := fun i j => w t i * (L t i - L t j) with hd
  have h1 : ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (R i j + d i j)^2 := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    rw [aux_nr_Rg_succ]
    exact aux_nr_sq _ _
  have h2 : ∑ i, ∑ j, (R i j + d i j)^2
      = ∑ i, ∑ j, (R i j)^2 + 2 * ∑ i, ∑ j, R i j * d i j + ∑ i, ∑ j, (d i j)^2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have h3 : ∑ i, ∑ j, R i j * d i j = 0 := by
    have e1 : ∀ i, ∑ j, R i j * d i j
        = L t i * (w t i * ∑ j, R i j) - ∑ j, w t i * R i j * L t j := by
      intro i
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; simp only [hd]; ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j => w t i * R i j * L t j)]
    have e2 : ∀ i, L t i * (w t i * ∑ j, R i j) = ∑ j, w t j * R j i * L t i := by
      intro i
      rw [hR, hflow t i, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [e2]
    exact sub_self _
  have h4 : ∑ i, ∑ j, (d i j)^2 ≤ k := by
    have hb : ∀ i j, (d i j)^2 ≤ w t i := by
      intro i j
      have hw0 := (hw t).1 i
      have hw1 := aux_nr_w_le _ (hw t) i
      have := hL t i
      have := hL t j
      simp only [hd]
      rw [mul_pow]
      have e3 : (L t i - L t j)^2 ≤ 1 := by nlinarith
      have e4 : (w t i)^2 ≤ w t i := by nlinarith
      have e5 : 0 ≤ (L t i - L t j)^2 := sq_nonneg _
      nlinarith
    calc ∑ i, ∑ j, (d i j)^2 ≤ ∑ i : Fin k, ∑ _j : Fin k, w t i :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb i j))
      _ = k := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.mul_sum, (hw t).2, mul_one]
  have hk : ∑ i, ∑ j, (Rg L w (t+1) i j)^2 ≤ ∑ i, ∑ j, (R i j)^2 + k := by
    rw [h2, h3] at h1; linarith
  exact hk

lemma aux_nr_pot (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) :
    ∑ i, ∑ j, (Rg L w T i j)^2 ≤ k * T := by
  induction T with
  | zero => simp [Rg, S]
  | succ n ih =>
    have := aux_nr_step k L w hL hw hflow n
    push_cast
    linarith

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem checked_no_regret (k : ℕ) (L w : ℕ → Fin k → ℝ)
    (hL : ∀ t i, 0 ≤ L t i ∧ L t i ≤ 1)
    (hw : ∀ t, IsDist (w t))
    (hflow : ∀ t i, w t i * ∑ j, Rg L w t i j = ∑ j, w t j * Rg L w t j i)
    (T : ℕ) (i j : Fin k) :
    Rg L w T i j ≤ Real.sqrt (2 * k * T) := by
  have hpot := aux_nr_pot k L w hL hw hflow T
  have hsq : (Rg L w T i j)^2 ≤ ∑ i, ∑ j, (Rg L w T i j)^2 := by
    have a1 : (Rg L w T i j)^2 ≤ ∑ j, (Rg L w T i j)^2 :=
      Finset.single_le_sum (f := fun j => (Rg L w T i j)^2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)
    have a2 : ∑ j, (Rg L w T i j)^2 ≤ ∑ i, ∑ j, (Rg L w T i j)^2 :=
      Finset.single_le_sum (f := fun i => ∑ j, (Rg L w T i j)^2)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
    linarith
  have hkT : (0:ℝ) ≤ k * T := by positivity
  have h2 : (Rg L w T i j)^2 ≤ 2 * k * T := by nlinarith
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt h2)
-- END ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_no_regret.lean

-- BEGIN ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_regret_sandwich_fractional_calibration.lean
-- Prove2me | solution 1 for CalibratedCE.Forecast.regret_sandwich_fractional_calibration
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T09:01:13.197948+00:00
-- url     : https://prove2.me/submissions/9da78fce-10b3-4704-91d1-466d03bc9e1b


set_option autoImplicit false

namespace CalibratedCE.Forecast

lemma rsfc_ind_nonneg {n : ℕ} (X : ℕ → Fin n) (t : ℕ) (m : Fin n) : 0 ≤ ind X t m := by
  unfold ind; split_ifs <;> norm_num

lemma rsfc_ind_le_one {n : ℕ} (X : ℕ → Fin n) (t : ℕ) (m : Fin n) : ind X t m ≤ 1 := by
  unfold ind; split_ifs <;> norm_num

lemma rsfc_ind_sum {n : ℕ} (X : ℕ → Fin n) (t : ℕ) : ∑ m, ind X t m = 1 := by
  unfold ind; simp

lemma rsfc_Nw_nonneg {k : ℕ} (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (T : ℕ)
    (i : Fin k) : 0 ≤ Nw w T i :=
  Finset.sum_nonneg (fun t _ => (hw t).1 i)

lemma rsfc_A_eq {k n : ℕ} (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (X : ℕ → Fin n)
    (T : ℕ) (i : Fin k) (m : Fin n) :
    ∑ t ∈ Finset.range T, w t i * ind X t m = Nw w T i * rhoW w X T i m := by
  unfold rhoW
  split_ifs with h
  · rw [mul_zero]
    apply le_antisymm
    · calc ∑ t ∈ Finset.range T, w t i * ind X t m ≤ ∑ t ∈ Finset.range T, w t i :=
            Finset.sum_le_sum (fun t _ => by
              have h1 := (hw t).1 i
              have h2 := rsfc_ind_le_one X t m
              nlinarith)
        _ = 0 := h
    · exact Finset.sum_nonneg (fun t _ => mul_nonneg ((hw t).1 i) (rsfc_ind_nonneg X t m))
  · field_simp

lemma rsfc_S_eq {k n : ℕ} (p : Fin k → Fin n → ℝ) (w : ℕ → Fin k → ℝ)
    (hw : ∀ t, IsDist (w t)) (X : ℕ → Fin n) (T : ℕ) (i j : Fin k) :
    S (sqLoss p X) w T i j = Nw w T i *
      ∑ m, ((rhoW w X T i m - p i m) ^ 2 - (rhoW w X T i m - p j m) ^ 2) := by
  have step1 : S (sqLoss p X) w T i j = ∑ t ∈ Finset.range T, ∑ m,
      (-2 * (p i m - p j m) * (w t i * ind X t m) + (p i m ^ 2 - p j m ^ 2) * w t i) := by
    unfold S sqLoss
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  rw [step1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, rsfc_A_eq w hw X T i m]
  unfold Nw
  ring

end CalibratedCE.Forecast

open CalibratedCE.Forecast in
theorem checked_regret_sandwich_fractional_calibration {k n : ℕ} (hk : 0 < k) (ε : ℝ)
    (p : Fin k → Fin n → ℝ) (hp : ∀ i, IsDist (p i))
    (hgrid : ∀ q : Fin n → ℝ, IsDist q → ∃ i, ∑ j, (q j - p i j) ^ 2 ≤ ε)
    (X : ℕ → Fin n) (w : ℕ → Fin k → ℝ) (hw : ∀ t, IsDist (w t)) (T : ℕ) :
    ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) ≤ C2w p w X T ∧
    C2w p w X T ≤ ε + ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) := by
  have hC : C2w p w X T =
      ∑ i, (Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2) / (T : ℝ) := by
    unfold C2w
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring
  have hle : ∀ i j, Rg (sqLoss p X) w T i j ≤
      Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2 := by
    intro i j
    have hN := rsfc_Nw_nonneg w hw T i
    have hS := rsfc_S_eq p w hw X T i j
    have h1 : 0 ≤ ∑ m, (rhoW w X T i m - p j m) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg _)
    have h2 : 0 ≤ ∑ m, (rhoW w X T i m - p i m) ^ 2 :=
      Finset.sum_nonneg (fun m _ => sq_nonneg _)
    rw [Finset.sum_sub_distrib, mul_sub] at hS
    unfold Rg
    apply max_le (mul_nonneg hN h2)
    rw [hS]
    linarith [mul_nonneg hN h1]
  have hε : 0 ≤ ε := by
    obtain ⟨i, hi⟩ := hgrid (p ⟨0, hk⟩) (hp _)
    exact le_trans (Finset.sum_nonneg (fun m _ => sq_nonneg _)) hi
  have hge : ∀ i, Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2 ≤
      Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
        (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε := by
    intro i
    have hN := rsfc_Nw_nonneg w hw T i
    have hsup : ∀ j, Rg (sqLoss p X) w T i j ≤
        Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
          (fun j => Rg (sqLoss p X) w T i j) :=
      fun j => Finset.le_sup' (fun j => Rg (sqLoss p X) w T i j) (Finset.mem_univ j)
    by_cases h0 : Nw w T i = 0
    · rw [h0, zero_mul, zero_mul, add_zero]
      have h00 : (0:ℝ) ≤ Rg (sqLoss p X) w T i ⟨0, hk⟩ := le_max_left _ _
      exact le_trans h00 (hsup ⟨0, hk⟩)
    · have hdist : IsDist (fun m => rhoW w X T i m) := by
        constructor
        · intro m
          show 0 ≤ rhoW w X T i m
          unfold rhoW
          rw [if_neg h0]
          exact div_nonneg (Finset.sum_nonneg (fun t _ =>
            mul_nonneg ((hw t).1 i) (rsfc_ind_nonneg X t m))) hN
        · show ∑ m, rhoW w X T i m = 1
          unfold rhoW
          simp only [if_neg h0]
          rw [← Finset.sum_div, Finset.sum_comm]
          have hA : ∑ t ∈ Finset.range T, ∑ m, w t i * ind X t m = Nw w T i := by
            unfold Nw
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [← Finset.mul_sum, rsfc_ind_sum, mul_one]
          rw [hA, div_self h0]
      obtain ⟨j, hj⟩ := hgrid _ hdist
      have hS := rsfc_S_eq p w hw X T i j
      rw [Finset.sum_sub_distrib, mul_sub] at hS
      have hR : S (sqLoss p X) w T i j ≤ Rg (sqLoss p X) w T i j := le_max_right _ _
      have h4 := hsup j
      have h3 : Nw w T i * ∑ m, (rhoW w X T i m - p j m) ^ 2 ≤ Nw w T i * ε :=
        mul_le_mul_of_nonneg_left hj hN
      linarith
  constructor
  · rw [hC]
    apply Finset.sum_le_sum
    intro i _
    gcongr
    exact Finset.sup'_le _ _ (fun j _ => hle i j)
  · rw [hC]
    rcases Nat.eq_zero_or_pos T with hT | hT
    · subst hT
      simp [hε]
    · have hTpos : (0:ℝ) < T := Nat.cast_pos.mpr hT
      have hsumN : ∑ i, Nw w T i = (T : ℝ) := by
        unfold Nw
        rw [Finset.sum_comm, Finset.sum_congr rfl (fun t _ => (hw t).2)]
        simp
      have key : ∑ i, (Nw w T i * ∑ m, (rhoW w X T i m - p i m) ^ 2) / (T : ℝ) ≤
          ∑ i, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε) / (T : ℝ) :=
        Finset.sum_le_sum (fun i _ => by gcongr; exact hge i)
      have heq : ∑ i, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            (fun j => Rg (sqLoss p X) w T i j) + Nw w T i * ε) / (T : ℝ) =
          ε + ∑ i : Fin k, (Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩)
            fun j => Rg (sqLoss p X) w T i j) / (T : ℝ) := by
        simp only [add_div, Finset.sum_add_distrib]
        rw [add_comm]
        congr 1
        rw [← Finset.sum_div, ← Finset.sum_mul, hsumN]
        field_simp
      linarith
-- END ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_regret_sandwich_fractional_calibration.lean

-- BEGIN ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_l1_calib_le_sqrt_l2.lean
-- Prove2me | solution 1 for CalibratedCE.Forecast.l1_calib_le_sqrt_l2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T17:53:07.313105+00:00
-- url     : https://prove2.me/submissions/d1a5cc50-adff-4b2d-bfef-38ce832a0c19




namespace CalibratedCE.Forecast

open Classical

lemma NH_sum {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) :
    ∑ p ∈ (h.map Prod.fst).toFinset, (NH h p : ℝ) = h.length := by
  have e : ∀ p, NH h p = (h.map Prod.fst).count p := by
    intro p
    unfold NH
    rw [List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
    have hf : ((fun x => x == p) ∘ Prod.fst) = (fun e : (Fin n → ℝ) × Fin n => decide (e.1 = p)) := by
      funext e
      simp only [Function.comp]
      by_cases he : e.1 = p <;> simp [he]
    rw [hf]
  simp_rw [e]
  rw [← Nat.cast_sum, List.sum_toFinset_count_eq_length, List.length_map]

theorem l1_calib_le_sqrt_l2 {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by
  unfold calibScoreHj calibScore2Hj
  set S := (h.map Prod.fst).toFinset with hS
  have hN := NH_sum h
  rw [← hS] at hN
  set w : (Fin n → ℝ) → ℝ := fun p => (NH h p : ℝ) / (h.length : ℝ) with hw
  set a : (Fin n → ℝ) → ℝ := fun p => |rhoH h p j - p j| with ha
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  have hws : ∑ p ∈ S, w p ≤ 1 := by
    simp only [hw, ← Finset.sum_div]
    rw [hN]
    rcases Nat.eq_zero_or_pos h.length with h0 | hpos
    · rw [h0]; simp
    · rw [div_self (by positivity)]
  have e1 : ∑ p ∈ S, |rhoH h p j - p j| * (NH h p : ℝ) / (h.length : ℝ) =
      ∑ p ∈ S, Real.sqrt (w p) * (a p * Real.sqrt (w p)) := by
    apply Finset.sum_congr rfl; intro p _
    rw [show Real.sqrt (w p) * (a p * Real.sqrt (w p)) = a p * (Real.sqrt (w p) * Real.sqrt (w p))
      by ring, Real.mul_self_sqrt (hw0 p)]
    simp only [ha, hw]; ring
  have e2 : ∑ p ∈ S, (rhoH h p j - p j) ^ 2 * (NH h p : ℝ) / (h.length : ℝ) =
      ∑ p ∈ S, (a p * Real.sqrt (w p)) ^ 2 := by
    apply Finset.sum_congr rfl; intro p _
    rw [mul_pow, Real.sq_sqrt (hw0 p)]
    simp only [ha, hw]; rw [sq_abs]; ring
  rw [e1, e2]
  apply Real.le_sqrt_of_sq_le
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun p => Real.sqrt (w p)) (fun p => a p * Real.sqrt (w p))
  have e3 : ∑ p ∈ S, Real.sqrt (w p) ^ 2 = ∑ p ∈ S, w p :=
    Finset.sum_congr rfl (fun p _ => Real.sq_sqrt (hw0 p))
  rw [e3] at hcs
  have hnn : 0 ≤ ∑ p ∈ S, (a p * Real.sqrt (w p)) ^ 2 := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  nlinarith

end CalibratedCE.Forecast

open CalibratedCE.Forecast

theorem checked_l1_calib_le_sqrt_l2 {n : ℕ} (h : List ((Fin n → ℝ) × Fin n)) (j : Fin n) :
    calibScoreHj h j ≤ Real.sqrt (calibScore2Hj h j) := by
  exact l1_calib_le_sqrt_l2 h j
-- END ATTRIBUTED COMPLETE BODY Sol_CalibratedCE_Forecast_l1_calib_le_sqrt_l2.lean

end

/- Complete checked body: GridPolicy -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

noncomputable def gridLoss {k n : ℕ} (p : Fin k → Fin n → ℝ) (b : Fin n) (i : Fin k) : ℝ :=
  (∑ j : Fin n, ((if b = j then (1:ℝ) else 0) - p i j)^2) / 2

noncomputable def realizedScore {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (h : History n) (i j : Fin k) : ℝ :=
  (h.map (fun e => if e.1 = p i then gridLoss p e.2 i - gridLoss p e.2 j else 0)).sum

noncomputable def realizedRegret {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (h : History n) (i j : Fin k) : ℝ := max 0 (realizedScore p h i j)

noncomputable def gridPotential {k n : ℕ} (p : Fin k → Fin n → ℝ) (h : History n) : ℝ :=
  ∑ i, ∑ j, (realizedRegret p h i j)^2

noncomputable def gridMix {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (h : History n) : Fin k → ℝ :=
  Classical.choose (checked_flow_conservation_solvable k hk (realizedRegret p h)
    (fun _ _ => le_max_left _ _))

theorem gridMix_spec {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ) (h : History n) :
    IsDist (gridMix hk p h) ∧ ∀ i, gridMix hk p h i * ∑ j, realizedRegret p h i j =
      ∑ j, gridMix hk p h j * realizedRegret p h j i :=
  Classical.choose_spec (checked_flow_conservation_solvable k hk (realizedRegret p h)
    (fun _ _ => le_max_left _ _))

noncomputable def gridWeights {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (h : History n) : PMF (Fin k) :=
  PMF.ofFintype (fun i => ENNReal.ofReal (gridMix hk p h i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => (gridMix_spec hk p h).1.1 i),
      (gridMix_spec hk p h).1.2, ENNReal.ofReal_one])

noncomputable def gridForecaster {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ) :
    Forecaster n := fun h => (gridWeights hk p h).map p

theorem gridForecaster_finite {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ) :
    finiteForecaster (gridForecaster hk p) :=
  fun _h => pmf_map_finite _ (Set.toFinite _) _

theorem gridForecaster_valid {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (hp : ∀ i, IsDist (p i)) (h : History n) (v : Fin n → ℝ)
    (hv : v ∈ (gridForecaster hk p h).support) : IsDist v := by
  obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
  exact hp i

theorem gridForecaster_mean {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (h : History n) (f : (Fin n → ℝ) → ℝ) :
    pmfMean (gridForecaster hk p h) f = ∑ i, gridMix hk p h i * f (p i) := by
  rw [gridForecaster, pmfMean_map _ (Set.toFinite _)]
  simp only [pmfMean, tsum_fintype, gridWeights, PMF.ofFintype_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.toReal_ofReal ((gridMix_spec hk p h).1.1 i)]

theorem gridLoss_bounds {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (hp : ∀ i, IsDist (p i)) (b : Fin n) (i : Fin k) :
    0 ≤ gridLoss p b i ∧ gridLoss p b i ≤ 1 := by
  have hs : ∑ j, (p i j)^2 ≤ 1 := by
    calc
      _ ≤ ∑ j, p i j := Finset.sum_le_sum (fun j _ => by
        have h0 := (hp i).1 j
        have h1 := aux_nr_w_le _ (hp i) j
        nlinarith)
      _ = 1 := (hp i).2
  have hsum : (∑ j : Fin n, ((if b = j then (1:ℝ) else 0) - p i j)^2) ≤ 2 := by
    calc
      _ ≤ ∑ j : Fin n, ((if b = j then (1:ℝ) else 0) + (p i j)^2) := by
        apply Finset.sum_le_sum
        intro j _
        have h0 := (hp i).1 j
        split_ifs <;> nlinarith
      _ = 1 + ∑ j, (p i j)^2 := by rw [Finset.sum_add_distrib]; simp
      _ ≤ 2 := by linarith
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (by norm_num)
  · unfold gridLoss
    linarith

theorem realizedScore_append {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (h : History n) (a : Fin k) (b : Fin n) (i j : Fin k) :
    realizedScore p (h ++ [(p a,b)]) i j = realizedScore p h i j +
      if a = i then gridLoss p b i - gridLoss p b j else 0 := by
  simp [realizedScore, hp.eq_iff]

theorem gridPotential_nonneg {k n : ℕ} (p : Fin k → Fin n → ℝ) (h : History n) :
    0 ≤ gridPotential p h :=
  Finset.sum_nonneg (fun _i _ => Finset.sum_nonneg (fun _j _ => sq_nonneg _))

theorem gridPotential_nil {k n : ℕ} (p : Fin k → Fin n → ℝ) : gridPotential p [] = 0 := by
  simp [gridPotential, realizedRegret, realizedScore]


end CalibratedCE.ForecastProof
end

/- Complete checked body: HistoryStatistics -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

theorem outcomeCount_cons {n : ℕ} (h : History n) (e : (Fin n → ℝ) × Fin n)
    (q : Fin n → ℝ) (j : Fin n) :
    outcomeCount (e::h) q j = outcomeCount h q j + if e.1=q ∧ e.2=j then 1 else 0 := by
  classical
  by_cases he : e.1=q ∧ e.2=j <;> simp [outcomeCount, he]

theorem counted_sum {n : ℕ} (h : History n) (q : Fin n → ℝ) (f : Fin n → ℝ) :
    (h.map (fun e => if e.1 = q then f e.2 else 0)).sum =
      ∑ j, outcomeCount h q j * f j := by
  classical
  induction h with
  | nil => simp [outcomeCount]
  | cons e h ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp_rw [outcomeCount_cons, add_mul, Finset.sum_add_distrib]
    by_cases he : e.1=q <;> simp [he]
    ring

theorem outcomeCount_sum {n : ℕ} (h : History n) (q : Fin n → ℝ) :
    ∑ j, outcomeCount h q j = (NH h q : ℝ) := by
  classical
  have hcount : (h.map (fun e => if e.1=q then (1:ℝ) else 0)).sum = (NH h q : ℝ) := by
    induction h with
    | nil => simp [NH]
    | cons e h ih =>
      by_cases he : e.1=q <;> simp [NH, he] at * <;> linarith
  have he := counted_sum h q (fun _ => 1)
  simpa only [mul_one, hcount] using he.symm

theorem rhoH_isDist {n : ℕ} (h : History n) (q : Fin n → ℝ) (hq : NH h q ≠ 0) :
    IsDist (rhoH h q) := by
  have hreal : (NH h q : ℝ) ≠ 0 := by exact_mod_cast hq
  constructor
  · intro j
    simp only [rhoH, hq, if_false]
    positivity
  · simp only [rhoH, hq, if_false, ← Finset.sum_div]
    change (∑ j, outcomeCount h q j) / (NH h q : ℝ) = 1
    rw [outcomeCount_sum, div_self hreal]

theorem gridLoss_formula {k n : ℕ} (p : Fin k → Fin n → ℝ) (b : Fin n) (i : Fin k) :
    gridLoss p b i = 1/2 - p i b + (∑ j, (p i j)^2)/2 := by
  have h : ∀ j, ((if b = j then (1:ℝ) else 0)-p i j)^2 =
      (if b=j then 1 else 0) - 2*(if b=j then p i j else 0) + (p i j)^2 := by
    intro j
    split_ifs <;> ring
  unfold gridLoss
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp
  ring

theorem realizedScore_quadratic {k n : ℕ} (p : Fin k → Fin n → ℝ) (h : History n)
    (i a : Fin k) :
    2 * realizedScore p h i a = (NH h (p i) : ℝ) *
      (∑ j, ((rhoH h (p i) j - p i j)^2 - (rhoH h (p i) j - p a j)^2)) := by
  rw [realizedScore, counted_sum h (p i) (fun b => gridLoss p b i-gridLoss p b a)]
  simp_rw [gridLoss_formula]
  have hsum := outcomeCount_sum h (p i)
  have hpoint : ∀ j, 2 * outcomeCount h (p i) j *
      ((1/2-p i j+(∑ b, (p i b)^2)/2) - (1/2-p a j+(∑ b, (p a b)^2)/2)) =
      2 * outcomeCount h (p i) j * (p a j-p i j) +
      outcomeCount h (p i) j * ((∑ b, (p i b)^2)-(∑ b, (p a b)^2)) := by
    intro j; ring
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, hpoint]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← rhoH_mul_nh h (p i) j]
  ring

theorem grid_history_support {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (A : Opponent n) (t : ℕ) (h : History n)
    (hh : h ∈ (histLaw (gridForecaster hk p) A t).support) :
    ∀ e ∈ h, e.1 ∈ Set.range p := by
  induction t generalizing h with
  | zero =>
    have : h = [] := by simpa [histLaw] using hh
    subst h
    simp
  | succ t ih =>
    obtain ⟨g, hg, hh⟩ := (PMF.mem_support_bind_iff _ _ h).mp hh
    obtain ⟨v, hv, hh⟩ := (PMF.mem_support_bind_iff _ _ h).mp hh
    obtain ⟨b, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hh
    intro e he
    rcases List.mem_append.mp he with he | he
    · exact ih g hg e he
    · have heq : e = (v,b) := by simpa using he
      subst e
      obtain ⟨i, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hv
      exact ⟨i,rfl⟩


end CalibratedCE.ForecastProof
end

/- Complete checked body: RegretPotential -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

theorem potential_step_bound {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (h : History n) (a : Fin k) (b : Fin n) :
    gridPotential p (h ++ [(p a,b)]) ≤ gridPotential p h +
      2 * ∑ j, realizedRegret p h a j * (gridLoss p b a - gridLoss p b j) +
      ∑ j, (gridLoss p b a - gridLoss p b j)^2 := by
  classical
  have hrow : ∀ i, (∑ j, (realizedRegret p (h ++ [(p a,b)]) i j)^2) ≤
      (∑ j, (realizedRegret p h i j)^2) +
        if a = i then 2 * ∑ j, realizedRegret p h i j * (gridLoss p b i - gridLoss p b j) +
          ∑ j, (gridLoss p b i - gridLoss p b j)^2 else 0 := by
    intro i
    by_cases hai : a = i
    · subst i
      simp only [if_true]
      calc
        _ ≤ ∑ j, (realizedRegret p h a j + (gridLoss p b a - gridLoss p b j))^2 := by
          apply Finset.sum_le_sum
          intro j _
          unfold realizedRegret
          rw [realizedScore_append p hp, if_pos rfl]
          exact aux_nr_sq _ _
        _ = _ := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    · simp only [if_neg hai, add_zero]
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro j _
      simp only [realizedRegret, realizedScore_append p hp, if_neg hai, add_zero]
  calc
    _ ≤ ∑ i, ((∑ j, (realizedRegret p h i j)^2) +
        if a = i then 2 * ∑ j, realizedRegret p h i j * (gridLoss p b i - gridLoss p b j) +
          ∑ j, (gridLoss p b i - gridLoss p b j)^2 else 0) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [gridPotential]; ring

theorem potential_expected_step {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (hd : ∀ i, IsDist (p i)) (h : History n) (b : Fin n) :
    ∑ a, gridMix hk p h a * gridPotential p (h ++ [(p a,b)]) ≤ gridPotential p h + k := by
  let w := gridMix hk p h
  let R := realizedRegret p h
  let l := gridLoss p b
  have hw := (gridMix_spec hk p h).1
  have hf := (gridMix_spec hk p h).2
  have hc : ∑ a, w a * ∑ j, R a j * (l a-l j) = 0 := by
    have he : ∀ a, w a * ∑ j, R a j * (l a-l j) =
        l a * (w a * ∑ j, R a j) - ∑ j, w a * R a j * l j := by
      intro a
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he]
    rw [Finset.sum_sub_distrib, Finset.sum_comm (f := fun a j => w a * R a j * l j)]
    have he' : ∀ a, l a * (w a * ∑ j, R a j) = ∑ j, w j * R j a * l a := by
      intro a
      rw [hf a, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [he']
    exact sub_self _
  have hq : ∑ a, w a * ∑ j, (l a-l j)^2 ≤ (k:ℝ) := by
    calc
      _ ≤ ∑ a, w a * (k:ℝ) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (hw.1 a)
        calc
          _ ≤ ∑ _j : Fin k, (1:ℝ) := by
            apply Finset.sum_le_sum
            intro j _
            have ha := gridLoss_bounds p hd b a
            have hj := gridLoss_bounds p hd b j
            dsimp [l]
            nlinarith
          _ = _ := by simp
      _ = k := by rw [← Finset.sum_mul, hw.2, one_mul]
  calc
    _ ≤ ∑ a, w a * (gridPotential p h +
        2 * ∑ j, R a j * (l a-l j) + ∑ j, (l a-l j)^2) :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left
        (potential_step_bound p hp h a b) (hw.1 a))
    _ = gridPotential p h + 2 * (∑ a, w a * ∑ j, R a j * (l a-l j)) +
        ∑ a, w a * ∑ j, (l a-l j)^2 := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hw.2, one_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ gridPotential p h + k := by rw [hc]; linarith

theorem grid_expected_potential {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (hd : ∀ i, IsDist (p i)) (A : Opponent n) (t : ℕ) :
    pmfMean (histLaw (gridForecaster hk p) A t) (gridPotential p) ≤ (k:ℝ) * t := by
  apply histLaw_drift_bound _ _ (gridForecaster_finite hk p) _ _ (gridPotential_nil p)
  intro h
  rw [gridForecaster_mean]
  have he : (∑ a, gridMix hk p h a * pmfMean (A h)
      (fun j => gridPotential p (h ++ [(p a,j)]))) =
      pmfMean (A h) (fun j => ∑ a, gridMix hk p h a * gridPotential p (h ++ [(p a,j)])) := by
    rw [pmfMean_sum _ (Set.toFinite _)]
    apply Finset.sum_congr rfl
    intro a _
    rw [pmfMean_smul]
  rw [he]
  calc
    _ ≤ pmfMean (A h) (fun _ => gridPotential p h + k) :=
      pmfMean_mono _ (Set.toFinite _) (fun b _ => potential_expected_step hk p hp hd h b)
    _ = _ := pmfMean_const _ _


end CalibratedCE.ForecastProof
end

/- Complete checked body: GridScoreBound -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

noncomputable def gridEnergy {k n : ℕ} (p : Fin k → Fin n → ℝ) (h : History n)
    (i : Fin k) : ℝ := (NH h (p i) : ℝ) * ∑ j, (rhoH h (p i) j-p i j)^2

theorem quadratic_upper (z c : ℝ) (hc : 0 < c) : z ≤ c*z^2+1/(4*c) := by
  have hd : 0 < 4*c := by positivity
  calc
    z ≤ (4*c^2*z^2+1)/(4*c) := (le_div_iff₀ hd).2 (by nlinarith [sq_nonneg (2*c*z-1)])
    _ = _ := by field_simp

theorem abs_young (z ν : ℝ) (hν : 0 < ν) : |z| ≤ ν+z^2/(4*ν) := by
  have hd : 0 < 4*ν := by positivity
  calc
    |z| ≤ (4*ν^2+z^2)/(4*ν) := (le_div_iff₀ hd).2 (by
      nlinarith [sq_nonneg (|z|-2*ν), sq_abs z])
    _ = _ := by field_simp

theorem gridEnergy_bound {k n : ℕ} (p : Fin k → Fin n → ℝ) (δ c : ℝ)
    (_hδ : 0 ≤ δ) (hc : 0 < c)
    (hnet : ∀ q, IsDist q → ∃ a, ∑ j, (q j-p a j)^2 ≤ δ)
    (h : History n) (i : Fin k) :
    gridEnergy p h i ≤ δ*(NH h (p i):ℝ) +
      2*c*(∑ a, (realizedRegret p h i a)^2) + 1/(2*c) := by
  have hsum0 : 0 ≤ ∑ a, (realizedRegret p h i a)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hi : NH h (p i) = 0
  · simp only [gridEnergy, hi, Nat.cast_zero, zero_mul, mul_zero, zero_add]
    positivity
  · obtain ⟨a, ha⟩ := hnet _ (rhoH_isDist h (p i) hi)
    have hid := realizedScore_quadratic p h i a
    rw [Finset.sum_sub_distrib, mul_sub] at hid
    have hN : 0 ≤ (NH h (p i) : ℝ) := by positivity
    have he := mul_le_mul_of_nonneg_left ha hN
    have hR : realizedScore p h i a ≤ realizedRegret p h i a := le_max_right _ _
    have hsq : (realizedRegret p h i a)^2 ≤ ∑ b, (realizedRegret p h i b)^2 :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
    have hsqC := mul_le_mul_of_nonneg_left hsq hc.le
    have hu := quadratic_upper (realizedRegret p h i a) c hc
    have hcoef : 2*(1/(4*c)) = 1/(2*c) := by ring
    unfold gridEnergy
    nlinarith

theorem grid_nh_sum {k n : ℕ} (p : Fin k → Fin n → ℝ) (hp : Function.Injective p)
    (h : History n) (hh : ∀ e ∈ h, e.1 ∈ Set.range p) :
    ∑ i, (NH h (p i):ℝ) = h.length := by
  classical
  have hs : (h.map Prod.fst).toFinset ⊆ Finset.univ.image p := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    obtain ⟨i, hi⟩ := hh e he
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  calc
    _ = ∑ q ∈ Finset.univ.image p, (NH h q : ℝ) := by rw [Finset.sum_image]; exact fun _ _ _ _ he => hp he
    _ = ∑ q ∈ (h.map Prod.fst).toFinset, (NH h q : ℝ) := by
      symm
      apply Finset.sum_subset hs
      intro q _ hq
      rw [nh_zero_of_not_mem h q hq, Nat.cast_zero]
    _ = h.length := NH_sum h

theorem scoreMass_le_energy {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (h : History n) (hh : ∀ e ∈ h, e.1 ∈ Set.range p)
    (ν : ℝ) (hν : 0 < ν) :
    scoreMass h ≤ (n:ℝ)*ν*h.length + (∑ i, gridEnergy p h i)/(4*ν) := by
  classical
  have hs : (h.map Prod.fst).toFinset ⊆ Finset.univ.image p := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    obtain ⟨i, hi⟩ := hh e he
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [scoreMass_eq_sum h _ hs, Finset.sum_image (fun _ _ _ _ he => hp he)]
  have hi : ∀ i, (∑ j, |discrepancy h (p i) j|) ≤
      (n:ℝ)*ν*(NH h (p i):ℝ) + gridEnergy p h i/(4*ν) := by
    intro i
    calc
      _ ≤ ∑ j, (ν*(NH h (p i):ℝ) +
          (NH h (p i):ℝ)*(rhoH h (p i) j-p i j)^2/(4*ν)) := by
        apply Finset.sum_le_sum
        intro j _
        have hy := mul_le_mul_of_nonneg_right (abs_young (rhoH h (p i) j-p i j) ν hν)
          (show 0 ≤ (NH h (p i):ℝ) by positivity)
        have he : discrepancy h (p i) j = (rhoH h (p i) j-p i j)*(NH h (p i):ℝ) := by
          rw [sub_mul, rhoH_mul_nh]
          rfl
        rw [he, abs_mul, abs_of_nonneg (show 0 ≤ (NH h (p i):ℝ) by positivity)]
        convert hy using 1
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div, ← Finset.mul_sum]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, gridEnergy]
        ring
  calc
    _ ≤ ∑ i, ((n:ℝ)*ν*(NH h (p i):ℝ) + gridEnergy p h i/(4*ν)) :=
      Finset.sum_le_sum (fun i _ => hi i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, grid_nh_sum p hp h hh, ← Finset.sum_div]

theorem scoreMass_affine_potential {k n : ℕ} (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (δ ν c : ℝ) (hδ : 0 ≤ δ) (hν : 0 < ν) (hc : 0 < c)
    (hnet : ∀ q, IsDist q → ∃ a, ∑ j, (q j-p a j)^2 ≤ δ)
    (h : History n) (hh : ∀ e ∈ h, e.1 ∈ Set.range p) :
    scoreMass h ≤ ((n:ℝ)*ν+δ/(4*ν))*h.length +
      (c/(2*ν))*gridPotential p h + (k:ℝ)/(8*ν*c) := by
  have he : ∑ i, gridEnergy p h i ≤ δ*h.length +
      2*c*gridPotential p h + (k:ℝ)/(2*c) := by
    calc
      _ ≤ ∑ i, (δ*(NH h (p i):ℝ) + 2*c*(∑ a, (realizedRegret p h i a)^2) + 1/(2*c)) :=
        Finset.sum_le_sum (fun i _ => gridEnergy_bound p δ c hδ hc hnet h i)
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [grid_nh_sum p hp h hh]
        change δ * h.length + 2*c*gridPotential p h + _ = _
        ring
  calc
    _ ≤ (n:ℝ)*ν*h.length + (∑ i, gridEnergy p h i)/(4*ν) := scoreMass_le_energy p hp h hh ν hν
    _ ≤ (n:ℝ)*ν*h.length + (δ*h.length+2*c*gridPotential p h+(k:ℝ)/(2*c))/(4*ν) := by
      gcongr
    _ = _ := by ring


end CalibratedCE.ForecastProof
end

/- Complete checked body: SimplexGrids -/
section

open scoped BigOperators
open Set

namespace CalibratedCE.ForecastProof

open CalibratedCE.Forecast

theorem finite_simplex_grid (n : ℕ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ k : ℕ, ∃ _hk : 0 < k, ∃ p : Fin k → Fin n → ℝ,
      Function.Injective p ∧ (∀ i, IsDist (p i)) ∧
      ∀ q : Fin n → ℝ, IsDist q → ∃ i, ∑ j, (q j - p i j)^2 ≤ δ := by
  classical
  let r : ℝ := Real.sqrt (δ / n)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hr : 0 < r := Real.sqrt_pos.2 (div_pos hδ hnR)
  obtain ⟨s, hs, hsf, hcover⟩ :=
    (isCompact_stdSimplex ℝ (Fin n)).finite_cover_balls hr
  have hd : IsDist (fun j : Fin n => if j = ⟨0, hn⟩ then 1 else 0) := by
    constructor
    · intro j; dsimp; split_ifs <;> norm_num
    · simp
  have hsne : s.Nonempty := by
    have hh := hcover hd
    simp only [Set.mem_iUnion] at hh
    obtain ⟨p, hp, _⟩ := hh
    exact ⟨p, hp⟩
  let := hsf.fintype
  let := hsne.to_subtype
  let k := Fintype.card s
  have hk : 0 < k := Fintype.card_pos
  let e : s ≃ Fin k := Fintype.equivFin s
  let p : Fin k → Fin n → ℝ := fun i => (e.symm i).val
  refine ⟨k, hk, p, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro i
    exact hs (e.symm i).property
  · intro q hq
    have hh := hcover hq
    simp only [Set.mem_iUnion] at hh
    obtain ⟨v, hv, hdist⟩ := hh
    refine ⟨e ⟨v, hv⟩, ?_⟩
    have hp : p (e ⟨v, hv⟩) = v := by simp [p]
    rw [hp]
    have hd' : dist q v < r := hdist
    have hc : ∀ j : Fin n, (q j - v j)^2 ≤ r^2 := by
      intro j
      have hj : |q j - v j| ≤ r :=
        (dist_le_pi_dist q v j).trans hd'.le
      have hab := abs_nonneg (q j - v j)
      nlinarith [sq_abs (q j - v j)]
    calc
      ∑ j : Fin n, (q j - v j)^2 ≤ ∑ _j : Fin n, r^2 :=
        Finset.sum_le_sum (fun j _ => hc j)
      _ = (n : ℝ) * r^2 := by simp
      _ = δ := by
        rw [Real.sq_sqrt (div_nonneg hδ.le hnR.le)]
        field_simp

end CalibratedCE.ForecastProof

end

/- Complete checked body: FixedGridBound -/
section

open scoped BigOperators
open CalibratedCE.Forecast

namespace CalibratedCE.ForecastProof

theorem fixed_grid_mean_bound {k n : ℕ} (hk : 0 < k) (p : Fin k → Fin n → ℝ)
    (hp : Function.Injective p) (hd : ∀ i, IsDist (p i))
    (δ ν c : ℝ) (hδ : 0 ≤ δ) (hν : 0 < ν) (hc : 0 < c)
    (hnet : ∀ q, IsDist q → ∃ a, ∑ j, (q j-p a j)^2 ≤ δ)
    (A : Opponent n) (t : ℕ) :
    pmfMean (histLaw (gridForecaster hk p) A t) scoreMass ≤
      ((n:ℝ)*ν+δ/(4*ν)+(c/(2*ν))*k)*t + (k:ℝ)/(8*ν*c) := by
  let μ := histLaw (gridForecaster hk p) A t
  have hμ : μ.support.Finite := histLaw_finite _ _ (gridForecaster_finite hk p) t
  have hb : ∀ h ∈ μ.support, scoreMass h ≤ ((n:ℝ)*ν+δ/(4*ν))*t +
      (c/(2*ν))*gridPotential p h + (k:ℝ)/(8*ν*c) := by
    intro h hh
    have he := scoreMass_affine_potential p hp δ ν c hδ hν hc hnet h
      (grid_history_support hk p A t h hh)
    rw [histLaw_length _ _ t h hh] at he
    exact he
  have hpot := grid_expected_potential hk p hp hd A t
  have hmul : 0 ≤ c/(2*ν) := by positivity
  calc
    _ ≤ pmfMean μ (fun h => ((n:ℝ)*ν+δ/(4*ν))*t +
      (c/(2*ν))*gridPotential p h + (k:ℝ)/(8*ν*c)) := pmfMean_mono μ hμ hb
    _ = ((n:ℝ)*ν+δ/(4*ν))*t +
      (c/(2*ν))*pmfMean μ (gridPotential p) + (k:ℝ)/(8*ν*c) := by
        rw [pmfMean_add _ hμ, pmfMean_add _ hμ, pmfMean_const, pmfMean_smul, pmfMean_const]
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_left hpot hmul
      change (c/(2*ν))*pmfMean μ (gridPotential p) ≤ (c/(2*ν))*((k:ℝ)*t) at hm
      nlinarith

theorem exists_fixed_forecaster (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η) :
    ∃ (F : Forecaster n) (B : ℝ), 0 ≤ B ∧ finiteForecaster F ∧
      (∀ h p, p ∈ (F h).support → IsDist p) ∧
      ∀ A : Opponent n, ∀ t : ℕ, pmfMean (histLaw F A t) scoreMass ≤ η*t+B := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  let ν := η/(4*n)
  have hν : 0 < ν := by dsimp [ν]; positivity
  let δ := η*ν
  have hδ : 0 < δ := mul_pos hη hν
  obtain ⟨k, hk, p, hp, hd, hnet⟩ := finite_simplex_grid n hn δ hδ
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  let c := η*ν/(2*k)
  have hc : 0 < c := by dsimp [c]; positivity
  let B := (k:ℝ)/(8*ν*c)
  refine ⟨gridForecaster hk p, B, by dsimp [B]; positivity,
    gridForecaster_finite hk p, gridForecaster_valid hk p hd, ?_⟩
  intro A t
  have he := fixed_grid_mean_bound hk p hp hd δ ν c hδ.le hν hc hnet A t
  have h1 : (n:ℝ)*ν = η/4 := by dsimp [ν]; field_simp
  have h2 : δ/(4*ν) = η/4 := by dsimp [δ]; field_simp
  have h3 : c/(2*ν)*(k:ℝ) = η/4 := by dsimp [c]; field_simp; norm_num
  rw [h1,h2,h3] at he
  dsimp only [B]
  nlinarith [show 0 ≤ (t:ℝ) by positivity]


end CalibratedCE.ForecastProof
end

/- Complete checked body: CalibrationRoot -/
section

namespace CalibratedCE.Forecast

theorem exists_calibrated_randomized_forecast (n : ℕ) (hn : 0 < n) :
    ∃ F : List ((Fin n → ℝ) × Fin n) → PMF (Fin n → ℝ),
      (∀ h, ∀ p ∈ (F h).support, IsDist p) ∧
      ∀ A : List ((Fin n → ℝ) × Fin n) → PMF (Fin n),
        ∀ ε : ℝ, 0 < ε →
          Filter.Tendsto
            (fun t : ℕ => (histLaw F A t).toOuterMeasure {h | calibScoreH h < ε})
            Filter.atTop (nhds 1) := by
  apply CalibratedCE.ForecastProof.calibrated_of_affine_bounds n
  intro η hη
  obtain ⟨F, B, _hB, hF, hv, hb⟩ :=
    CalibratedCE.ForecastProof.exists_fixed_forecaster n hn η hη
  exact ⟨F, B, hF, hv, hb⟩

end CalibratedCE.Forecast

end

open CalibratedCE CalibratedCE.Forecast
open Filter


theorem solution (n : ℕ) (hn : 0 < n) :
    ∃ F : List ((Fin n → ℝ) × Fin n) → PMF (Fin n → ℝ),
      (∀ h, ∀ p ∈ (F h).support, IsDist p) ∧
      ∀ A : List ((Fin n → ℝ) × Fin n) → PMF (Fin n),
        ∀ ε : ℝ, 0 < ε →
          Filter.Tendsto
            (fun t : ℕ => (histLaw F A t).toOuterMeasure {h | calibScoreH h < ε})
            Filter.atTop (nhds 1) := by
  exact CalibratedCE.Forecast.exists_calibrated_randomized_forecast n hn

#print axioms CalibratedCE.Forecast.exists_calibrated_randomized_forecast
#print axioms solution
