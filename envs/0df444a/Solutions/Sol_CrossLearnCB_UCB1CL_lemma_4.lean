-- Prove2me | solution 1 for CrossLearnCB.UCB1CL.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:35:14.041555+00:00
-- url     : https://prove2.me/submissions/ec232cfa-8d58-46fe-b325-1006cd03033f

import Mathlib
import Definitions.Def_CrossLearnCB_UCB1CL_Model
import Theorems.Thm_CrossLearnCB_UCB1CL_per_round_bound

open MeasureTheory ProbabilityTheory

namespace UCB1CLLemma4Aux
open CrossLearnCB.UCB1CL

/-- A set of arm sequences determined by the first `T` arms is measurable. -/
lemma measurableSet_of_dep {K : ℕ} [NeZero K] (T : ℕ) (p : (ℕ → Fin K) → Prop)
    (hp : ∀ J J' : ℕ → Fin K, (∀ s < T, J s = J' s) → (p J ↔ p J')) :
    MeasurableSet {J | p J} := by
  classical
  let ext : (Fin T → Fin K) → (ℕ → Fin K) := fun y s => if h : s < T then y ⟨s, h⟩ else 0
  have hres : Measurable (fun J : ℕ → Fin K => fun s : Fin T => J s) :=
    measurable_pi_lambda _ (fun s => measurable_pi_apply _)
  have : {J | p J} = (fun J : ℕ → Fin K => fun s : Fin T => J s) ⁻¹' {y | p (ext y)} := by
    ext J
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    apply hp
    intro s hs
    simp [ext, hs]
  rw [this]
  exact hres (Set.to_countable _).measurableSet

lemma obsCount_congr {K C : ℕ} (G : Fin K → Fin C → Fin C → Prop) (ctx : ℕ → Fin C)
    (J J' : ℕ → Fin K) (t : ℕ) (h : ∀ s < t, J s = J' s) (i : Fin K) (c : Fin C) :
    obsCount G ctx J t i c = obsCount G ctx J' t i c := by
  classical
  unfold obsCount
  congr 1
  apply Finset.filter_congr
  intro s hs
  rw [h s (Finset.mem_range.1 hs)]

/-- `Σ_{t<T} 1/(t+1)² ≤ π²/6`. -/
lemma sum_inv_sq_le (T : ℕ) :
    ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 ≤ Real.pi ^ 2 / 6 := by
  have h := hasSum_zeta_two
  have h1 : ∑ n ∈ Finset.range (T + 1), 1 / (n : ℝ) ^ 2 ≤ Real.pi ^ 2 / 6 :=
    sum_le_hasSum _ (fun n _ => by positivity) h
  rw [Finset.sum_range_succ'] at h1
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h1
  norm_num at h1
  simpa [one_div] using h1

end UCB1CLLemma4Aux

open CrossLearnCB.UCB1CL in
theorem solution {K C : ℕ} [NeZero K] [NeZero C] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : ℕ → Ω → Fin K → Fin C → ℝ)
    (hR : IsStochRewards P R) (G : Fin K → Fin C → Fin C → Prop) (hG : HasSelfLoops G)
    (ctx : ℕ → Fin C) (T : ℕ) (hT : 2 ≤ T) (I : ℕ → Ω → Fin K)
    (hI : IsUCB1CLProcess R T G ctx I) (Δmin : ℝ) (hΔ : 0 < Δmin) :
    ∫ ω, regPost (gap P R) G ctx (fun s => I s ω) T Δmin ∂P ≤ K * Real.pi ^ 2 / 3 := by
  classical
  -- gaps lie in [0, 1]
  have hmeasR : ∀ i c, Measurable (fun ω => R 0 ω i c) := fun i c =>
    (measurable_pi_apply c).comp ((measurable_pi_apply i).comp (hR.measurable 0))
  have hmu : ∀ i c, mu P R i c ∈ Set.Icc (0 : ℝ) 1 := by
    intro i c
    have hint : Integrable (fun ω => R 0 ω i c) P := by
      refine (integrable_const (1 : ℝ)).mono' (hmeasR i c).aestronglyMeasurable
        (ae_of_all _ (fun ω => ?_))
      have := hR.mem_Icc 0 ω i c
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
    constructor
    · exact integral_nonneg (fun ω => (hR.mem_Icc 0 ω i c).1)
    · unfold mu
      calc ∫ ω, R 0 ω i c ∂P ≤ ∫ _ω, (1 : ℝ) ∂P :=
            integral_mono hint (integrable_const _) (fun ω => (hR.mem_Icc 0 ω i c).2)
        _ = 1 := by simp
  have hgap : ∀ i c, gap P R i c ∈ Set.Icc (0 : ℝ) 1 := by
    intro i c
    unfold gap muStar
    constructor
    · have := Finset.le_sup' (fun j => mu P R j c) (Finset.mem_univ i)
      linarith
    · have h1 : Finset.univ.sup' Finset.univ_nonempty (fun j => mu P R j c) ≤ 1 :=
        Finset.sup'_le _ _ (fun j _ => (hmu j c).2)
      linarith [(hmu i c).1]
  -- measurability of the arm process
  have hImeas : ∀ t, Measurable (I t) := by
    intro t
    refine (hI.adapted t).mono ?_ le_rfl
    apply Measurable.comap_le
    exact measurable_pi_lambda _ (fun s => hR.measurable s)
  have hJmeas : Measurable (fun ω => fun s => I s ω) := measurable_pi_lambda _ hImeas
  -- the events of the per-round bound
  let E : ℕ → Fin K → Set Ω := fun t i => {ω | I t ω = i ∧
      mThr T (gap P R i (ctx t)) < (obsCount G ctx (fun s => I s ω) t i (ctx t) : ℝ)}
  have hE : ∀ t, t < T → ∀ i, MeasurableSet (E t i) := by
    intro t ht i
    have hset := UCB1CLLemma4Aux.measurableSet_of_dep (K := K) T
      (fun J => J t = i ∧ mThr T (gap P R i (ctx t)) < (obsCount G ctx J t i (ctx t) : ℝ))
      (by
        intro J J' h
        rw [h t ht, UCB1CLLemma4Aux.obsCount_congr G ctx J J' t (fun s hs => h s (by omega))])
    exact hJmeas hset
  let ψ : ℕ → Fin K → Ω → ℝ := fun t i ω =>
    if 0 < gap P R i (ctx t) then (E t i).indicator (fun _ => (1 : ℝ)) ω else 0
  have hψint : ∀ t ∈ Finset.range T, ∀ i ∈ (Finset.univ : Finset (Fin K)),
      Integrable (ψ t i) P := by
    intro t ht i _
    simp only [ψ]
    split_ifs
    · exact (integrable_const (1 : ℝ)).indicator (hE t (Finset.mem_range.1 ht) i)
    · exact integrable_const 0
  have hψ : ∀ t ∈ Finset.range T, ∀ i, ∫ ω, ψ t i ω ∂P ≤ 2 / ((t : ℝ) + 1) ^ 2 := by
    intro t ht i
    have ht' := Finset.mem_range.1 ht
    simp only [ψ]
    split_ifs with hpos
    · rw [show (fun _ : Ω => (1 : ℝ)) = (1 : Ω → ℝ) from rfl,
        integral_indicator_one (hE t ht' i)]
      have hb := CrossLearnCB.UCB1CL.per_round_bound P R hR G hG ctx T hT I hI t ht' i hpos
      have hfin : P (E t i) ≠ ⊤ := measure_ne_top _ _
      rw [Measure.real]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      rw [ENNReal.toReal_ofReal (by positivity)] at this
      exact this
    · simp; positivity
  -- pathwise domination
  have hpath : ∀ ω, regPost (gap P R) G ctx (fun s => I s ω) T Δmin
      ≤ ∑ t ∈ Finset.range T, ∑ i, ψ t i ω := by
    intro ω
    unfold regPost
    apply Finset.sum_le_sum
    intro t _
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin K)), 0 ≤ ψ t i ω := by
      intro i _
      simp only [ψ]
      split_ifs
      · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      · exact le_rfl
    split_ifs with hc
    · have hpos : 0 < gap P R (I t ω) (ctx t) := lt_of_lt_of_le hΔ hc.1
      have hval : ψ t (I t ω) ω = 1 := by
        simp only [ψ, if_pos hpos]
        rw [Set.indicator_of_mem]
        exact ⟨rfl, hc.2⟩
      calc gap P R (I t ω) (ctx t) ≤ 1 := (hgap _ _).2
        _ = ψ t (I t ω) ω := hval.symm
        _ ≤ ∑ i, ψ t i ω := Finset.single_le_sum hnn (Finset.mem_univ _)
    · exact Finset.sum_nonneg hnn
  have hnonneg : ∀ ω, 0 ≤ regPost (gap P R) G ctx (fun s => I s ω) T Δmin := by
    intro ω
    unfold regPost
    apply Finset.sum_nonneg
    intro t _
    split_ifs
    · exact (hgap _ _).1
    · exact le_rfl
  have hsumint : Integrable (fun ω => ∑ t ∈ Finset.range T, ∑ i, ψ t i ω) P :=
    integrable_finsetSum _ (fun t ht => integrable_finsetSum _ (fun i hi => hψint t ht i hi))
  calc ∫ ω, regPost (gap P R) G ctx (fun s => I s ω) T Δmin ∂P
      ≤ ∫ ω, ∑ t ∈ Finset.range T, ∑ i, ψ t i ω ∂P :=
        integral_mono_of_nonneg (ae_of_all _ hnonneg) hsumint (ae_of_all _ hpath)
    _ = ∑ t ∈ Finset.range T, ∑ i, ∫ ω, ψ t i ω ∂P := by
        rw [integral_finsetSum _ (fun t ht => integrable_finsetSum _
          (fun i hi => hψint t ht i hi))]
        apply Finset.sum_congr rfl
        intro t ht
        rw [integral_finsetSum _ (fun i hi => hψint t ht i hi)]
    _ ≤ ∑ t ∈ Finset.range T, ∑ _i : Fin K, 2 / ((t : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro i _
        exact hψ t ht i
    _ = 2 * K * ∑ t ∈ Finset.range T, 1 / ((t : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t _
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ 2 * K * (Real.pi ^ 2 / 6) := by
        apply mul_le_mul_of_nonneg_left (UCB1CLLemma4Aux.sum_inv_sq_le T)
        positivity
    _ = K * Real.pi ^ 2 / 3 := by ring
