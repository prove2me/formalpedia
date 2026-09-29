-- Prove2me | solution 1 for BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-31T17:39:46.150803+00:00
-- url     : https://prove2.me/submissions/f7e7038a-18d6-4b85-96c2-ce9535ad6d8b

import Definitions.Def_BanditTrajectory
import Theorems.Thm_InformationTheory_klDiv_map_eq_klDiv_trim_comap
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_BanditAlgorithm_klDiv_banditStepKernel_eq_sum_of_support
import Theorems.Thm_BanditAlgorithm_banditTrajMeasure_joint_eq_compProd
import Theorems.Thm_ProbabilityTheory_compProd_restrict_prod_univ
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

/-!
Assembly of `BanditAlgorithm.bandit_prefix_klDiv_one_step_on_event`.
-/

open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal

namespace BanditAlgorithm

theorem banditRewardKernel_apply_rfl' {k : ℕ} (ν : StochasticBandit k) (i : Fin k) :
    banditRewardKernel ν i = ν.P i := rfl

/-- Appending one round to a history, as a measurable equivalence. -/
noncomputable def snocEquiv (k n : ℕ) :
    (BanditHistory k n × (Fin k × ℝ)) ≃ᵐ BanditHistory k (n + 1) :=
  (MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ Fin k × ℝ) (Fin.last n)).symm

lemma snocEquiv_apply {k n : ℕ} (p : BanditHistory k n × (Fin k × ℝ)) :
    snocEquiv k n p = Fin.snoc (α := fun _ ↦ Fin k × ℝ) p.1 p.2 := by
  funext t
  simp [snocEquiv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_last]
  rfl

lemma prefix_succ {k n : ℕ} (ω : ℕ → Fin k × ℝ) :
    banditTrajPrefix k (n + 1) ω
      = snocEquiv k n (banditTrajPrefix k n ω, ω n) := by
  rw [snocEquiv_apply]
  funext t
  refine Fin.lastCases ?_ (fun j ↦ ?_) t
  · simp [banditTrajPrefix]
  · simp [banditTrajPrefix]

/-- The joint map: length-`n` prefix together with the next observation. -/
def prefixPair (k n : ℕ) (ω : ℕ → Fin k × ℝ) : BanditHistory k n × (Fin k × ℝ) :=
  (banditTrajPrefix k n ω, ω n)

lemma measurable_prefixPair {k n : ℕ} : Measurable (prefixPair k n) :=
  measurable_banditTrajPrefix.prodMk (measurable_pi_apply n)

/-- Trimming and restricting to a set of the small σ-algebra commute. -/
lemma trim_restrict {α : Type*} {m m₀ : MeasurableSpace α} (hm : m ≤ m₀)
    (ρ : @Measure α m₀) {T : Set α} (hT : MeasurableSet[m] T) :
    (ρ.trim hm).restrict T = (ρ.restrict T).trim hm := by
  refine @Measure.ext _ m _ _ (fun A hA ↦ ?_)
  rw [Measure.restrict_apply hA, trim_measurableSet_eq hm (hA.inter hT),
    trim_measurableSet_eq hm hA, Measure.restrict_apply (hm _ hA)]

/-- Skeleton of the assembly: the four steps, with the analytic content still to be filled. -/
theorem _root_.solution {k : ℕ}
    (ν ν' : StochasticBandit k) (π : BanditPolicy k) (n : ℕ)
    (E : Set (ℕ → Fin k × ℝ))
    (hE : MeasurableSet[banditFiltration k n] E) :
    @klDiv (ℕ → Fin k × ℝ) (banditFiltration k (n + 1))
        (((banditTrajMeasure ν π).trim ((banditFiltration k).le (n + 1))).restrict E)
        (((banditTrajMeasure ν' π).trim ((banditFiltration k).le (n + 1))).restrict E) ≤
      @klDiv (ℕ → Fin k × ℝ) (banditFiltration k n)
          (((banditTrajMeasure ν π).trim ((banditFiltration k).le n)).restrict E)
          (((banditTrajMeasure ν' π).trim ((banditFiltration k).le n)).restrict E) +
        ∑ i, (banditTrajMeasure ν π) (E ∩ {ω | (ω n).1 = i}) *
          klDiv (ν.P i) (ν'.P i) := by
  classical
  set P := banditTrajMeasure ν π with hP
  set Q := banditTrajMeasure ν' π with hQ
  -- STEP 0: if a played arm has infinite divergence the right-hand side is already `⊤`
  by_cases hbad : ∃ i, klDiv (ν.P i) (ν'.P i) = ⊤ ∧ P (E ∩ {ω | (ω n).1 = i}) ≠ 0
  · obtain ⟨i, hi, hne⟩ := hbad
    have hsum : ∑ j, P (E ∩ {ω | (ω n).1 = j}) * klDiv (ν.P j) (ν'.P j) = ⊤ := by
      refine ENNReal.sum_eq_top.mpr ⟨i, Finset.mem_univ i, ?_⟩
      rw [hi, ENNReal.mul_top hne]
    rw [hsum, add_top]
    exact le_top
  push_neg at hbad
  -- so every arm reachable on `E` at this round has finite divergence
  have hgood : ∀ i, P (E ∩ {ω | (ω n).1 = i}) ≠ 0 → klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
    intro i hne hi
    exact hne (hbad i hi)
  -- `E` is a cylinder over the length-`n` prefix
  obtain ⟨E', hE'meas, hE'eq⟩ : ∃ E' : Set (BanditHistory k n),
      MeasurableSet E' ∧ banditTrajPrefix k n ⁻¹' E' = E := id hE
  have hpre : ∀ ω, prefixPair k n ω ∈ E' ×ˢ (univ : Set (Fin k × ℝ)) ↔ ω ∈ E := by
    intro ω
    simp only [prefixPair, Set.mem_prod, Set.mem_univ, and_true]
    rw [← hE'eq]
    rfl
  have hEpre : prefixPair k n ⁻¹' (E' ×ˢ (univ : Set (Fin k × ℝ))) = E := by
    ext ω; exact hpre ω
  -- STEP 4 : the restricted one-step factorisation
  have hfact : ∀ ρ : Measure (ℕ → Fin k × ℝ), ∀ nu : StochasticBandit k,
      ρ = banditTrajMeasure nu π →
      (ρ.restrict E).map (prefixPair k n)
        = ((ρ.restrict E).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel nu π n) := by
    intro ρ nu hρ
    subst hρ
    have h1 : ((banditTrajMeasure nu π).restrict E).map (prefixPair k n)
        = ((banditTrajMeasure nu π).map (prefixPair k n)).restrict
            (E' ×ˢ (univ : Set (Fin k × ℝ))) := by
      rw [Measure.restrict_map measurable_prefixPair
        (hE'meas.prod MeasurableSet.univ), hEpre]
    rw [h1, show (banditTrajMeasure nu π).map (prefixPair k n)
        = ((banditTrajMeasure nu π).map (banditTrajPrefix k n)) ⊗ₘ
          (banditStepKernel nu π n) from
      BanditAlgorithm.banditTrajMeasure_joint_eq_compProd nu π n,
      ProbabilityTheory.compProd_restrict_prod_univ _ _ hE'meas,
      Measure.restrict_map measurable_banditTrajPrefix hE'meas, hE'eq]
  -- STEPS 1-3 : both sides become divergences of push-forwards
  have hEn : MeasurableSet[banditFiltration k n] E := hE
  have hEn1 : MeasurableSet[banditFiltration k (n + 1)] E :=
    (banditFiltration k).mono (Nat.le_succ n) _ hE
  have hpush : ∀ (m : ℕ) (hEm : MeasurableSet[banditFiltration k m] E),
      @klDiv (ℕ → Fin k × ℝ) (banditFiltration k m)
          ((P.trim ((banditFiltration k).le m)).restrict E)
          ((Q.trim ((banditFiltration k).le m)).restrict E)
        = klDiv ((P.restrict E).map (banditTrajPrefix k m))
            ((Q.restrict E).map (banditTrajPrefix k m)) := by
    intro m hEm
    rw [trim_restrict _ _ hEm, trim_restrict _ _ hEm]
    exact (InformationTheory.klDiv_map_eq_klDiv_trim_comap
      (measurable_banditTrajPrefix (k := k) (n := m)) _ _).symm
  rw [hpush n hEn, hpush (n + 1) hEn1]
  -- drop the append: it is a measurable embedding
  have hsnoc : ∀ ρ : Measure (ℕ → Fin k × ℝ),
      (ρ.restrict E).map (banditTrajPrefix k (n + 1))
        = ((ρ.restrict E).map (prefixPair k n)).map (snocEquiv k n) := by
    intro ρ
    rw [Measure.map_map (snocEquiv k n).measurable measurable_prefixPair]
    congr 1
    funext ω
    exact prefix_succ ω
  rw [hsnoc P, hsnoc Q,
    InformationTheory.klDiv_map_measurableEmbedding (snocEquiv k n).measurableEmbedding,
    hfact P ν rfl, hfact Q ν' rfl,
    klDiv_compProd_eq_add]
  refine add_le_add le_rfl ?_
  -- STEP 6 : evaluate the conditional term
  have hsing : ∀ (m : Measure (Fin k)), ∀ᵐ i ∂m, m {i} ≠ 0 := by
    intro m
    classical
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have hset : {i : Fin k | m {i} = 0} = ⋃ i ∈ {i : Fin k | m {i} = 0}, ({i} : Set (Fin k)) := by
      ext i; simp
    rw [hset, measure_biUnion_null_iff (Set.to_countable _)]
    exact fun i hi ↦ hi
  -- the arm marginal of the step kernel
  have harm : ∀ (nu : StochasticBandit k) (h : BanditHistory k n) (i : Fin k),
      banditStepKernel nu π n h ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))
        = (π.select n h) {i} := by
    intro nu h i
    rw [banditStepKernel, Kernel.compProd_apply
      ((measurableSet_singleton i).prod MeasurableSet.univ)]
    simp only [Kernel.comap_apply]
    have hfun : ∀ b : Fin k, (banditRewardKernel nu) b
        (Prod.mk b ⁻¹' ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)))
        = Set.indicator ({i} : Set (Fin k)) (fun _ ↦ (1 : ℝ≥0∞)) b := by
      intro b
      by_cases hb : b = i
      · subst hb
        have hu : Prod.mk b ⁻¹' ((({b} : Set (Fin k))) ×ˢ (univ : Set ℝ)) = univ := by
          ext c; simp
        rw [hu, Set.indicator_of_mem (by simp : b ∈ ({b} : Set (Fin k)))]
        have hk : (banditRewardKernel nu) b = nu.P b := rfl
        rw [hk, measure_univ]
      · have he : Prod.mk b ⁻¹' ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)) = (∅ : Set ℝ) := by
          ext c; simp [hb]
        rw [he, Set.indicator_of_notMem (by simpa using hb), measure_empty]
    rw [lintegral_congr hfun, lintegral_indicator (measurableSet_singleton i)]
    simp
  -- the occupation identity
  have hocc : ∀ i : Fin k,
      ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n))
        = P (E ∩ {ω | (ω n).1 = i}) := by
    intro i
    have hSm : MeasurableSet ((univ : Set (BanditHistory k n)) ×ˢ
        ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) :=
      MeasurableSet.univ.prod ((measurableSet_singleton i).prod MeasurableSet.univ)
    calc ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n))
        = ∫⁻ h, (banditStepKernel ν π n h) (Prod.mk h ⁻¹'
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))))
            ∂((P.restrict E).map (banditTrajPrefix k n)) := by
          refine lintegral_congr fun h ↦ ?_
          rw [← harm ν h i]
          congr 1
          ext x; simp
      _ = (((P.restrict E).map (banditTrajPrefix k n)) ⊗ₘ (banditStepKernel ν π n))
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) :=
          (Measure.compProd_apply hSm).symm
      _ = ((P.restrict E).map (prefixPair k n))
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ))) := by
          rw [hfact P ν rfl]
      _ = (P.restrict E) (prefixPair k n ⁻¹'
            ((univ : Set (BanditHistory k n)) ×ˢ ((({i} : Set (Fin k))) ×ˢ (univ : Set ℝ)))) :=
          Measure.map_apply measurable_prefixPair hSm
      _ = P (E ∩ {ω | (ω n).1 = i}) := by
          rw [Measure.restrict_apply (measurable_prefixPair hSm)]
          congr 1
          ext ω
          simp [prefixPair, and_comm]
  -- almost every history only plays arms of finite divergence
  have hae : ∀ᵐ h ∂((P.restrict E).map (banditTrajPrefix k n)),
      ∀ i, (π.select n h) {i} ≠ 0 → klDiv (ν.P i) (ν'.P i) ≠ ⊤ := by
    rw [ae_all_iff]
    intro i
    by_cases hi : klDiv (ν.P i) (ν'.P i) = ⊤
    · have h0 : ∫⁻ h, (π.select n h) {i} ∂((P.restrict E).map (banditTrajPrefix k n)) = 0 := by
        rw [hocc i]; exact hbad i hi
      have hz := (lintegral_eq_zero_iff
        (Kernel.measurable_coe (π.select n) (measurableSet_singleton i))).mp h0
      filter_upwards [hz] with h hh hne
      exact absurd hh hne
    · filter_upwards with h _ ; exact hi
  -- fibrewise absolute continuity, almost everywhere
  have hac : ∀ᵐ h ∂((P.restrict E).map (banditTrajPrefix k n)),
      banditStepKernel ν π n h ≪ banditStepKernel ν' π n h := by
    filter_upwards [hae] with h hh
    rw [banditStepKernel, banditStepKernel, Kernel.compProd_apply_eq_compProd_sectR,
      Kernel.compProd_apply_eq_compProd_sectR]
    refine Measure.AbsolutelyContinuous.compProd_right ?_
    filter_upwards [hsing (π.select n h)] with i hi
    simpa [Kernel.sectR_apply, banditRewardKernel_apply_rfl'] using
      (klDiv_ne_top_iff.mp (hh i hi)).1
  rw [InformationTheory.klDiv_compProd_self_eq_lintegral_of_ae _ _ _ hac]
  refine le_of_eq ?_
  calc ∫⁻ h, klDiv (banditStepKernel ν π n h) (banditStepKernel ν' π n h)
        ∂((P.restrict E).map (banditTrajPrefix k n))
      = ∫⁻ h, ∑ i, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
          ∂((P.restrict E).map (banditTrajPrefix k n)) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with h hh
        exact BanditAlgorithm.klDiv_banditStepKernel_eq_sum_of_support ν ν' π h hh
    _ = ∑ i, ∫⁻ h, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
          ∂((P.restrict E).map (banditTrajPrefix k n)) := by
        refine lintegral_finset_sum _ fun i _ ↦ ?_
        exact ((Kernel.measurable_coe (π.select n)
          (measurableSet_singleton i)).ennreal_toReal.ennreal_ofReal).mul_const _
    _ = ∑ i, P (E ∩ {ω | (ω n).1 = i}) * klDiv (ν.P i) (ν'.P i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hcongr : ∫⁻ h, ENNReal.ofReal ((π.select n h).real {i}) * klDiv (ν.P i) (ν'.P i)
              ∂((P.restrict E).map (banditTrajPrefix k n))
            = ∫⁻ h, (π.select n h) {i} * klDiv (ν.P i) (ν'.P i)
              ∂((P.restrict E).map (banditTrajPrefix k n)) := by
          refine lintegral_congr fun h ↦ ?_
          rw [ofReal_measureReal]
        rw [hcongr, lintegral_mul_const _
          (Kernel.measurable_coe (π.select n) (measurableSet_singleton i)), hocc i]

end BanditAlgorithm
