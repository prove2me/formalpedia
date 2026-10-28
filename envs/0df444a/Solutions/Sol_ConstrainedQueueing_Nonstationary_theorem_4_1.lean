-- Prove2me | solution 1 for ConstrainedQueueing.Nonstationary.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T09:38:34.712078+00:00
-- url     : https://prove2.me/submissions/e50d9ef7-40b3-49e5-a978-90623f5a3087

import Mathlib
import Definitions.Def_ConstrainedQueueing_Nonstationary_Model


open Set Filter Topology
open ConstrainedQueueing.Nonstationary

namespace CQProof

variable {L N : ℕ}

def rateImage (net : Network L N) : Set (Fin L → ℝ) :=
  (fun f => -((routing net).mulVec f)) '' coS net

theorem coS_nonneg (net : Network L N) {f : Fin N → ℝ} (hf : f ∈ coS net) : 0 ≤ f := by
  apply (convexHull_min (t := Set.Ici (0 : Fin N → ℝ)) ?_ (convex_Ici (𝕜 := ℝ) 0)) hf
  rintro _ ⟨E, _, rfl⟩ i
  simp only [ConstrainedQueueing.MaxThroughput.actVec, Pi.zero_apply]
  split_ifs <;> norm_num

theorem coS_compact (net : Network L N) : IsCompact (coS net) := by
  exact (Set.toFinite (ConstrainedQueueing.MaxThroughput.actVec '' net.S)).isCompact_convexHull ℝ

theorem routing_continuous (net : Network L N) :
    Continuous (fun f : Fin N → ℝ => -((routing net).mulVec f)) := by
  apply continuous_pi
  intro l
  simp only [Pi.neg_apply, Matrix.mulVec, dotProduct]
  fun_prop

theorem rateImage_closed (net : Network L N) : IsClosed (rateImage net) :=
  ((coS_compact net).image (routing_continuous net)).isClosed

theorem scaled_mem (net : Network L N) {a : Fin L → ℝ} {f : Fin N → ℝ}
    (ha : 0 ≤ a) (hf : f ∈ coS net) (heq : a = -((routing net).mulVec f))
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ < 1) : θ • a ∈ Cprime net := by
  have hf0 := coS_nonneg net hf
  refine ⟨smul_nonneg hθ ha, θ • f, ⟨smul_nonneg hθ hf0, ?_⟩, f, hf, ?_⟩
  · rw [heq, Matrix.mulVec_smul, smul_neg]
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    constructor
    · intro hi
      have hfi : 0 < f i := lt_of_le_of_ne (hf0 i) (by intro hz; simp [← hz] at hi)
      nlinarith
    · intro hi
      simp [hi]

theorem rate_mem_closure (net : Network L N) {a : Fin L → ℝ}
    (ha0 : 0 ≤ a) (ha : a ∈ rateImage net) : a ∈ closure (Cprime net) := by
  obtain ⟨f, hf, rfl⟩ := ha
  let θ : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hlim : Tendsto θ atTop (𝓝 1) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1
    have hh := h.comp (tendsto_add_atTop_nat 1)
    simpa [θ, Nat.cast_add, Nat.cast_one] using tendsto_const_nhds.sub hh
  have hlim' : Tendsto (fun n => θ n • (-((routing net).mulVec f))) atTop
      (𝓝 (-((routing net).mulVec f))) := by
    simpa only [one_smul] using hlim.smul_const (-((routing net).mulVec f))
  apply mem_closure_of_tendsto hlim'
  apply Filter.Eventually.of_forall
  intro n
  apply scaled_mem net ha0 hf rfl
  · dsimp [θ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hh : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    linarith
  · dsimp [θ]
    have hh : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem outside_rateImage (net : Network L N) {a : Fin L → ℝ}
    (ha0 : 0 ≤ a) (ha : a ∉ closure (Cprime net)) : a ∉ rateImage net :=
  fun h => ha (rate_mem_closure net ha0 h)

end CQProof


open Set Filter Topology Finset
open ConstrainedQueueing.Nonstationary

namespace CQProof
variable {L N : ℕ}

def activation (π : HistPolicy L N) (X : ℕ → Fin L → ℕ) (t : ℕ) :=
  π t (fun k => X k)

noncomputable def actAvg (π : HistPolicy L N) (X : ℕ → Fin L → ℕ) (t : ℕ) (i : Fin N) : ℝ :=
  (∑ s ∈ range t, ConstrainedQueueing.MaxThroughput.actVec (activation π X s) i) / (t : ℝ)

theorem routing_actVec (net : Network L N) (E : Finset (Fin N)) (l : Fin L) :
    ((routing net).mulVec (ConstrainedQueueing.MaxThroughput.actVec E)) l =
      (numFeeding net E l : ℝ) - (numServing net E l : ℝ) := by
  classical
  simp only [Matrix.mulVec, dotProduct, routing, ConstrainedQueueing.MaxThroughput.actVec,
    numFeeding, numServing, Nat.cast_sum, card_eq_sum_ones, Nat.cast_one,
    sub_mul, sum_sub_distrib]
  congr 1 <;> simp [mul_ite]

theorem activation_mem (net : Network L N) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (X : ℕ → Fin L → ℕ) (t : ℕ) :
    activation π X t ∈ net.S := (hπ t (fun k => X k)).1

theorem actAvg_mem (net : Network L N) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (X : ℕ → Fin L → ℕ) {t : ℕ} (ht : 0 < t) :
    actAvg π X t ∈ coS net := by
  have ht' : (t : ℝ) ≠ 0 := by positivity
  have hh := (convex_convexHull ℝ (ConstrainedQueueing.MaxThroughput.actVec '' net.S)).sum_mem
    (t := range t) (w := fun _ => (t : ℝ)⁻¹)
    (z := fun s => ConstrainedQueueing.MaxThroughput.actVec (activation π X s))
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp [ht'])
    (fun s _ => subset_convexHull ℝ _ ⟨_, activation_mem net π hπ X s, rfl⟩)
  have heq : actAvg π X t = ∑ s ∈ range t, (t : ℝ)⁻¹ • ConstrainedQueueing.MaxThroughput.actVec (activation π X s) := by
    ext i
    simp [actAvg, Finset.sum_apply, div_eq_mul_inv, Finset.mul_sum, mul_comm]
  rw [heq]
  exact hh

theorem run_step (net : Network L N) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ) (A X : ℕ → Fin L → ℕ)
    (hX : IsRun net π x0 A X) (t : ℕ) (l : Fin L) :
    (X (t+1) l : ℝ) = (X t l : ℝ) + (A t l : ℝ) +
      ((routing net).mulVec (ConstrainedQueueing.MaxThroughput.actVec (activation π X t))) l := by
  have hs : numServing net (activation π X t) l ≤ X t l :=
    (hπ t (fun k => X k)).2 l
  have hh := hX.2 t l
  change X (t + 1) l = X t l - numServing net (activation π X t) l +
    numFeeding net (activation π X t) l + A t l at hh
  rw [hh, Nat.cast_add, Nat.cast_add, Nat.cast_sub hs, routing_actVec]
  ring

theorem run_balance (net : Network L N) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ) (A X : ℕ → Fin L → ℕ)
    (hX : IsRun net π x0 A X) (t : ℕ) (l : Fin L) :
    (X t l : ℝ) = (x0 l : ℝ) + (∑ s ∈ range t, (A s l : ℝ)) +
      ∑ s ∈ range t, ((routing net).mulVec (ConstrainedQueueing.MaxThroughput.actVec (activation π X s))) l := by
  induction t with
  | zero => simp [hX.1]
  | succ t ih => rw [run_step net π hπ x0 A X hX, ih, sum_range_succ, sum_range_succ]; ring

theorem run_balance_avg (net : Network L N) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ) (A X : ℕ → Fin L → ℕ)
    (hX : IsRun net π x0 A X) {t : ℕ} (_ht : 0 < t) (l : Fin L) :
    (X t l : ℝ) / (t : ℝ) =
      ((∑ s ∈ range t, (A s l : ℝ)) / (t : ℝ) + (x0 l : ℝ) / (t : ℝ)) -
        (-(routing net).mulVec (actAvg π X t)) l := by
  rw [run_balance net π hπ x0 A X hX]
  simp only [Pi.neg_apply, sub_neg_eq_add, add_div]
  congr 1
  · ring
  · simp only [Matrix.mulVec, dotProduct, actAvg, mul_div_assoc, Finset.mul_sum,
      Finset.sum_div]
    rw [Finset.sum_comm]

end CQProof


open MeasureTheory ProbabilityTheory Filter Topology

namespace CQProof

lemma mean_nonneg {L : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : ℕ → Ω → Fin L → ℕ) (a : Fin L → ℝ)
    (hmean : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ) : 0 ≤ a := by
  intro l
  rw [hmean l]
  exact integral_nonneg (fun _ => Nat.cast_nonneg _)

theorem arrival_average_ae {L : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Fin L → ℕ) (hAmeas : ∀ t, Measurable (A t))
    (hindep : iIndepFun A μ) (hident : ∀ t, IdentDistrib (A t) (A 0) μ μ)
    (hsq : ∀ l, Integrable (fun ω => (A 0 ω l : ℝ)^2) μ)
    (a : Fin L → ℝ) (hmean : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun t l => (∑ s ∈ Finset.range t, (A s ω l : ℝ))/(t:ℝ))
      atTop (𝓝 a) := by
  have coord (l : Fin L) : Measurable (fun v : Fin L → ℕ => (v l : ℝ)) := by
    fun_prop
  have hint (l : Fin L) : Integrable (fun ω => (A 0 ω l : ℝ)) μ := by
    apply (hsq l).mono ((coord l).comp (hAmeas 0)).aestronglyMeasurable
    filter_upwards [] with ω
    change ‖(A 0 ω l : ℝ)‖ ≤ ‖(A 0 ω l : ℝ)^2‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (A 0 ω l)), abs_of_nonneg (sq_nonneg (A 0 ω l : ℝ))]
    have h : A 0 ω l ≤ (A 0 ω l)^2 := Nat.le_self_pow (by omega) _
    exact_mod_cast h
  have hc (l : Fin L) : ∀ᵐ ω ∂μ,
      Tendsto (fun t => (∑ s ∈ Finset.range t, (A s ω l : ℝ))/(t:ℝ)) atTop (𝓝 (a l)) := by
    rw [hmean l]
    exact strong_law_ae_real (fun t ω => (A t ω l : ℝ)) (hint l)
      (fun i j hij => (hindep.indepFun hij).comp (coord l) (coord l))
      (fun t => (hident t).comp (coord l))
  filter_upwards [ae_all_iff.mpr hc] with ω hω
  exact tendsto_pi_nhds.mpr hω

end CQProof


open Filter Topology

namespace CQProof

theorem closed_escape {L : ℕ} (K : Set (Fin L → ℝ)) (a : Fin L → ℝ)
    (z u x : ℕ → Fin L → ℝ) (hK : IsClosed K) (ha : a ∉ K)
    (hz : ∀ t, 0 < t → z t ∈ K) (hu : Tendsto u atTop (𝓝 a))
    (hx : ∀ t l, 0 ≤ x t l)
    (hbal : ∀ t, 0 < t → ∀ l, x t l / (t:ℝ) = u t l - z t l) :
    Tendsto (fun t => ∑ l, x t l) atTop atTop := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl a ha
  have hnear : ∀ᶠ t in atTop, dist (u t) a < ε / 2 :=
    (Metric.tendsto_nhds.mp hu) (ε / 2) (by positivity)
  have hlinear : ∀ᶠ t : ℕ in atTop, (ε / 2) * (t:ℝ) ≤ ∑ l, x t l := by
    filter_upwards [hnear, eventually_gt_atTop (0:ℕ)] with t ht hpos
    have htR : (0:ℝ) < t := by exact_mod_cast hpos
    have hfar : ε ≤ dist (z t) a := by
      by_contra! h
      exact (hball h) (hz t hpos)
    have hnorm : ‖u t - z t‖ ≤ (∑ l, x t l) / (t:ℝ) := by
      apply (pi_norm_le_iff_of_nonneg (div_nonneg (Finset.sum_nonneg fun l _ => hx t l) htR.le)).mpr
      intro l
      change ‖u t l - z t l‖ ≤ _
      rw [← hbal t hpos l, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hx t l) htR.le)]
      exact div_le_div_of_nonneg_right (Finset.single_le_sum (fun j _ => hx t j) (Finset.mem_univ l)) htR.le
    have htri := dist_triangle (z t) (u t) a
    have hdist : dist (z t) (u t) ≤ (∑ l, x t l) / (t:ℝ) := by
      simpa only [dist_eq_norm, norm_sub_rev] using hnorm
    have hquot : ε / 2 ≤ (∑ l, x t l) / (t:ℝ) := by linarith
    exact (le_div_iff₀ htR).mp hquot
  exact tendsto_atTop_mono' atTop hlinear
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < ε / 2))

end CQProof


open Filter Topology Finset
open ConstrainedQueueing.Nonstationary

namespace CQProof
variable {L N : ℕ}

theorem run_diverges (net : Network L N) {a : Fin L → ℝ}
    (ha0 : 0 ≤ a) (ha : a ∉ closure (Cprime net)) (π : HistPolicy L N)
    (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ) (A X : ℕ → Fin L → ℕ)
    (hX : IsRun net π x0 A X)
    (havg : Tendsto (fun t l => (∑ s ∈ range t, (A s l : ℝ)) / (t : ℝ)) atTop (𝓝 a)) :
    Tendsto (fun t => ∑ l, (X t l : ℝ)) atTop atTop := by
  apply closed_escape (rateImage net) a
    (fun t => -(routing net).mulVec (actAvg π X t))
    (fun t l => (∑ s ∈ range t, (A s l : ℝ)) / (t : ℝ) + (x0 l : ℝ) / (t : ℝ))
    (fun t l => (X t l : ℝ)) (rateImage_closed net) (outside_rateImage net ha0 ha)
  · intro t ht
    exact ⟨actAvg π X t, actAvg_mem net π hπ X ht, rfl⟩
  · apply tendsto_pi_nhds.mpr
    intro l
    simpa using (tendsto_pi_nhds.mp havg l).add
      (tendsto_const_div_atTop_nhds_zero_nat (x0 l : ℝ))
  · intro t l
    positivity
  · intro t ht l
    exact run_balance_avg net π hπ x0 A X hX ht l

end CQProof


namespace ConstrainedQueueing.Nonstationary

open MeasureTheory ProbabilityTheory Filter

/-- Theorem 4.1 (p. 1941): single class, one-slot service times. Let the arrival vectors `A t`
(arrivals at the `L` queues in slot `t + 1`) be i.i.d. in time, with independent components and
finite second moments, and let `a` be their mean. If `a` lies outside the closure of `C'`, then
for every admissible history-dependent policy `π` and every initial state, the total number of
customers in the system tends to infinity almost surely. -/
theorem theorem_4_1 {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (hS0 : (∅ : Finset (Fin N)) ∈ net.S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Fin L → ℕ) (hAmeas : ∀ t, Measurable (A t))
    (hindep : iIndepFun (fun t => A t) μ) (hident : ∀ t, IdentDistrib (A t) (A 0) μ μ)
    (hindepQ : ∀ t, iIndepFun (fun l ω => A t ω l) μ)
    (hsq : ∀ l, Integrable (fun ω => ((A 0 ω l : ℝ)) ^ 2) μ)
    (a : Fin L → ℝ) (hmean : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ)
    (ha : a ∉ closure (Cprime net))
    (π : HistPolicy L N) (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ)
    (X : ℕ → Ω → Fin L → ℕ) (hX : ∀ ω, IsRun net π x0 (fun t => A t ω) (fun t => X t ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => ∑ l, (X t ω l : ℝ)) atTop atTop := by
  have : C1 net := hC1
  have : (∅ : Finset (Fin N)) ∈ net.S := hS0
  have : ∀ t, iIndepFun (fun l ω => A t ω l) μ := hindepQ
  filter_upwards [CQProof.arrival_average_ae μ A hAmeas hindep hident hsq a hmean] with ω hω
  exact CQProof.run_diverges net (CQProof.mean_nonneg μ A a hmean) ha π hπ x0
    (fun t => A t ω) (fun t => X t ω) (hX ω) hω

end ConstrainedQueueing.Nonstationary

open MeasureTheory ProbabilityTheory Filter ConstrainedQueueing.Nonstationary

theorem solution {L N : ℕ} (net : Network L N) (hC1 : C1 net)
    (hS0 : (∅ : Finset (Fin N)) ∈ net.S)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : ℕ → Ω → Fin L → ℕ) (hAmeas : ∀ t, Measurable (A t))
    (hindep : iIndepFun (fun t => A t) μ) (hident : ∀ t, IdentDistrib (A t) (A 0) μ μ)
    (hindepQ : ∀ t, iIndepFun (fun l ω => A t ω l) μ)
    (hsq : ∀ l, Integrable (fun ω => ((A 0 ω l : ℝ)) ^ 2) μ)
    (a : Fin L → ℝ) (hmean : ∀ l, a l = ∫ ω, (A 0 ω l : ℝ) ∂μ)
    (ha : a ∉ closure (Cprime net))
    (π : HistPolicy L N) (hπ : IsAdmissiblePolicy net π) (x0 : Fin L → ℕ)
    (X : ℕ → Ω → Fin L → ℕ) (hX : ∀ ω, IsRun net π x0 (fun t => A t ω) (fun t => X t ω)) :
    ∀ᵐ ω ∂μ, Tendsto (fun t => ∑ l, (X t ω l : ℝ)) atTop atTop := ConstrainedQueueing.Nonstationary.theorem_4_1 net hC1 hS0 μ A hAmeas hindep hident hindepQ hsq a hmean ha π hπ x0 X hX

