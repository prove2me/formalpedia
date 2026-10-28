-- Prove2me | solution 1 for BitranCaldentey2003.prop8_eq35_convex_region_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:23:41.904544+00:00
-- url     : https://prove2.me/submissions/72fe4bcf-f4cb-441f-a301-b9c01c734f7a

import Mathlib
import Definitions.Def_PricingRM_DetHeuristic_PricingModel

open MeasureTheory ProbabilityTheory PricingRM.DetHeuristic
open scoped ENNReal

namespace BCDis

noncomputable def d0 (p : ℝ) : ℝ := if p ≤ 1 then 1 else 1 / p
noncomputable def d1 (p : ℝ) : ℝ := if p ≤ 0 then 1 / 10 else 2
noncomputable def dm (n : Fin 2) (p : ℝ) : ℝ := if n = 0 then d0 p else d1 p

lemma dm_nonneg (n : Fin 2) (p : ℝ) : 0 ≤ dm n p := by
  unfold dm d0 d1
  split_ifs with h1 h2 h2 <;> try norm_num
  push Not at h2; positivity

noncomputable def M : PricingModel 2 where
  μ n p := Measure.dirac (dm n p)
  isProb _ _ := inferInstance
  nonneg n p := by
    rw [ae_dirac_eq, Filter.eventually_pure]
    exact dm_nonneg n p
  integrable n p := integrable_dirac (by simp)

lemma mean (n : Fin 2) (p : ℝ) : meanDemand M n p = dm n p := by
  simp [meanDemand, M]

lemma pi_dirac (a : Fin 2 → ℝ) : Measure.pi (fun n => Measure.dirac (a n)) = Measure.dirac a := by
  apply Measure.pi_eq
  intro s hs
  rw [Measure.dirac_apply' _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.dirac_apply' _ (hs _)]
  by_cases h : a ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem h]
    simp only [Pi.one_apply]
    rw [Finset.prod_eq_one]
    intro i _
    rw [Set.indicator_of_mem (h i (Set.mem_univ i))]; rfl
  · rw [Set.indicator_of_notMem h]
    simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at h
    obtain ⟨i, hi⟩ := h
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rw [Set.indicator_of_notMem hi]

lemma detObj (q : Fin 2 → ℝ) (hq : ∀ n, 0 ≤ q n) : detObjective M q = min (q 0) 1 + 2 * q 1 := by
  simp only [detObjective, Fin.sum_univ_two, mean, dm, d0, d1]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  have h0 := hq 0; have h1 := hq 1
  congr 1
  · split_ifs with h
    · rw [min_eq_left h]; ring
    · push Not at h; rw [min_eq_right h.le]; field_simp
  · split_ifs with h
    · have : q 1 = 0 := le_antisymm h h1
      rw [this]; ring
    · ring

lemma conc : ConcaveOn ℝ (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) (detObjective M) := by
  have hc : ConcaveOn ℝ (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) (fun q : Fin 2 → ℝ => min (q 0) 1 + 2 * q 1) := by
    have hs : Convex ℝ (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) := convex_pi (fun _ _ => convex_Ici 0)
    have l0 : ConcaveOn ℝ (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) (fun q : Fin 2 → ℝ => q 0) :=
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).concaveOn hs
    have l1 : ConcaveOn ℝ (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) (fun q : Fin 2 → ℝ => 2 * q 1) :=
      ((2 : ℝ) • LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).concaveOn hs
    exact (l0.inf (concaveOn_const 1 hs)).add l1
  refine hc.congr ?_
  intro q hq
  exact (detObj q (fun n => hq n (Set.mem_univ n))).symm

lemma feas_iff (q : Fin 2 → ℝ) : DetFeasible M (3 / 2) q ↔ (∀ n, 0 ≤ q n) ∧ q 1 = 0 := by
  unfold DetFeasible
  simp only [Fin.sum_univ_two, mean, dm, d0, d1, Fin.isValue, ↓reduceIte, one_ne_zero]
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨hq, ?_⟩
    by_contra hne
    have : ¬ q 1 ≤ 0 := fun h => hne (le_antisymm h (hq 1))
    rw [if_neg this] at hs
    have : 0 ≤ (if q 0 ≤ 1 then (1:ℝ) else 1 / q 0) := by
      split_ifs with h
      · norm_num
      · push Not at h; positivity
    linarith
  · rintro ⟨hq, h1⟩
    refine ⟨hq, ?_⟩
    rw [h1, if_pos le_rfl]
    have : (if q 0 ≤ 1 then (1:ℝ) else 1 / q 0) ≤ 1 := by
      split_ifs with h
      · exact le_rfl
      · push Not at h; rw [div_le_one (by linarith)]; exact h.le
    linarith

def pdet : Fin 2 → ℝ := ![1, 0]

lemma opt : IsDetOptimal M (3 / 2) pdet := by
  have hp : DetFeasible M (3 / 2) pdet := (feas_iff _).mpr ⟨fun n => by fin_cases n <;> simp [pdet], by simp [pdet]⟩
  refine ⟨hp, fun q hq => ?_⟩
  obtain ⟨hq0, hq1⟩ := (feas_iff q).mp hq
  rw [detObj q hq0, detObj pdet hp.1, hq1]
  simp [pdet]

lemma optValue_top : optValue M (3 / 2) = ⊤ := by
  unfold optValue
  rw [valueToGo]
  apply eq_top_iff.mpr
  refine le_trans ?_ (le_iSup₂ (f := fun p (_ : p ∈ Set.Ici (0:ℝ)) => _) 0 (Set.mem_Ici.mpr le_rfl))
  simp only [M, lintegral_dirac]
  simp only [dm, Fin.isValue, show (⟨2 - (1 + 1), by omega⟩ : Fin 2) = 0 from rfl, ↓reduceIte, d0, zero_le_one]
  norm_num
  rw [valueToGo]
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  refine le_trans ?_ (le_iSup₂ (f := fun p (_ : p ∈ Set.Ici (0:ℝ)) => _) (2 * (r : ℝ) + 1) (Set.mem_Ici.mpr (by positivity)))
  simp only [lintegral_dirac]
  simp only [dm, show (⟨2 - (0 + 1), by omega⟩ : Fin 2) = 1 from rfl, Fin.isValue, one_ne_zero, ↓reduceIte, d1]
  have hr : ¬ (2 * (r : ℝ) + 1 ≤ 0) := by have := r.2; linarith
  rw [if_neg hr, valueToGo, add_zero, show min (2:ℝ) (1/2) = 1/2 by norm_num, ← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [r.2]

lemma law : heuristicLaw M pdet = Measure.dirac (fun n => dm n (pdet n)) := by
  unfold heuristicLaw; exact pi_dirac _

lemma eta0 : eta M (3 / 2) pdet 0 = 0 := by
  have hv : cumVariance M pdet 0 = 0 := by
    unfold cumVariance; rw [law]; exact variance_dirac _
  have hm : cumMean M pdet 0 = 1 := by
    unfold cumMean; rw [law, integral_dirac]
    simp [cumDemand, dm, d0, pdet, Finset.sum_filter, Fin.sum_univ_two]
  rw [eta, hv, hm]
  norm_num

end BCDis

theorem solution : ¬ (∀ {N : ℕ} (M : PricingModel N)
    (hN : 0 < N)
    (hconc : ConcaveOn ℝ (Set.univ.pi fun _ : Fin N => Set.Ici (0 : ℝ)) (detObjective M))
    (C₀ : ℝ) (hconvF : Convex ℝ {q : Fin N → ℝ | DetFeasible M C₀ q})
    (hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand M n pinf < C₀)
    (pdet : Fin N → ℝ) (hopt : IsDetOptimal M C₀ pdet)
    (hL2 : ∀ n, MemLp (fun x : ℝ => x) 2 (M.μ n (pdet n)))
    (hmean : ∀ n, 0 < meanDemand M n (pdet n))
    (hVdet : 0 < detObjective M pdet),
    1 ≥ heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ∧
      heuristicRevenue M C₀ pdet / (optValue M C₀).toReal ≥
        (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ∧
      (1 / detObjective M pdet) *
          ∑ n, pdet n * meanDemand M n (pdet n) *
            (1 - eta M C₀ pdet n / meanDemand M n (pdet n)) ≥
        1 - Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
          (fun n => eta M C₀ pdet n / meanDemand M n (pdet n))) := by
  intro H
  have hconvF : Convex ℝ {q : Fin 2 → ℝ | DetFeasible BCDis.M (3 / 2) q} := by
    have : {q : Fin 2 → ℝ | DetFeasible BCDis.M (3 / 2) q} =
        (Set.univ.pi fun _ : Fin 2 => Set.Ici (0 : ℝ)) ∩ {q | q 1 = 0} := by
      ext q
      simp only [Set.mem_setOf_eq, BCDis.feas_iff, Set.mem_inter_iff, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici]
    rw [this]
    exact (convex_pi (fun _ _ => convex_Ici 0)).inter
      (convex_hyperplane (LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).isLinear 0)
  have hslater : ∃ pinf : ℝ, 0 ≤ pinf ∧ ∑ n, meanDemand BCDis.M n pinf < 3 / 2 :=
    ⟨0, le_rfl, by simp [Fin.sum_univ_two, BCDis.mean, BCDis.dm, BCDis.d0, BCDis.d1]; norm_num⟩
  have hL2 : ∀ n, MemLp (fun x : ℝ => x) 2 (BCDis.M.μ n (BCDis.pdet n)) := by
    intro n
    exact MemLp.of_bound (C := |BCDis.dm n (BCDis.pdet n)|) aestronglyMeasurable_id
      (by simp only [BCDis.M]; rw [ae_dirac_eq, Filter.eventually_pure]; simp)
  have hmean : ∀ n, 0 < meanDemand BCDis.M n (BCDis.pdet n) := by
    intro n; rw [BCDis.mean]; fin_cases n <;> simp [BCDis.dm, BCDis.d0, BCDis.d1, BCDis.pdet]
  have hV : detObjective BCDis.M BCDis.pdet = 1 := by
    rw [BCDis.detObj _ (fun n => by fin_cases n <;> simp [BCDis.pdet])]; simp [BCDis.pdet]
  have h := (H BCDis.M (by norm_num) BCDis.conc (3 / 2) hconvF hslater BCDis.pdet BCDis.opt hL2 hmean
    (by rw [hV]; norm_num)).2.1
  rw [BCDis.optValue_top, ENNReal.toReal_top, div_zero, hV, Fin.sum_univ_two, BCDis.eta0, BCDis.mean,
    BCDis.mean] at h
  simp [BCDis.pdet, BCDis.dm, BCDis.d0] at h
  linarith
