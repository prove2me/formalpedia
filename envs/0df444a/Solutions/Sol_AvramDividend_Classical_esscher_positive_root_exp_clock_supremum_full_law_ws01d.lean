-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_exp_clock_supremum_full_law_ws01d
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T13:07:28.317793+00:00
-- url     : https://prove2.me/submissions/30b89331-09f1-4675-a739-cd56e7311aa1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_exp_clock_supremum_tail_ws01d
import Theorems.Thm_AvramDividend_Classical_levy_exponential_real_clock_extrema_drawdown_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_real
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

/-- Full law of the actual Esscher-tilted real-clock Lévy running maximum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (phi q : ℝ) (hphi : 0 < phi) (hq : 0 < q) (hroot : X.ψ phi = q)
    (p : ℝ) (hp : 0 < p)
    (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (phi + lam) - q = p) :
    Measure.map (fun z : Ω × ℝ => runningSup X z.2.toNNReal z.1)
      ((P.prod (ProbabilityTheory.expMeasure p)).withDensity
        (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
          (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q)))) =
    ProbabilityTheory.expMeasure lam := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure p) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure hp
  let J : Measure (Ω × ℝ) :=
    (P.prod (ProbabilityTheory.expMeasure p)).withDensity
      (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
        (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * q)))
  have hJoint : Measurable (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
      (phi * X.X z.2.toNNReal z.1 - (z.2.toNNReal : ℝ) * X.ψ phi))) :=
    chat04_esscher_likelihood_joint_measurable_of_joint_levy_state X phi
      (chat04_levy_joint_time_state_measurable X)
  have hJ : IsProbabilityMeasure J := by
    dsimp [J]
    rw [← hroot]
    exact chat04_esscher_joint_exponential_horizon_probability_of_measurable_likelihood
      X phi p (le_of_lt hphi) hp hJoint
  letI : IsProbabilityMeasure J := hJ
  let M : Ω × ℝ → ℝ := fun z => runningSup X z.2.toNNReal z.1
  have hM : Measurable M :=
    (levy_exponential_real_clock_extrema_drawdown_measurable X).fst.fst
  let μ : Measure ℝ := Measure.map M J
  let ν : Measure ℝ := ProbabilityTheory.expMeasure lam
  letI : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map hM.aemeasurable
  letI : IsProbabilityMeasure ν := ProbabilityTheory.isProbabilityMeasure_expMeasure hlam
  have hcomp (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a : ℝ) :
      ρ (Iic a) = 1 - ρ (Ioi a) := by
    simpa only [Set.compl_Ioi, measure_univ] using
      (measure_compl (μ := ρ) measurableSet_Ioi (measure_ne_top ρ (Ioi a)))
  have hpos (a : ℝ) (ha : 0 < a) : μ (Iic a) = ν (Iic a) := by
    have hμtail : μ (Ioi a) =
        ENNReal.ofReal (Real.exp (-(lam * a))) := by
      change Measure.map M J (Ioi a) = _
      rw [Measure.map_apply hM measurableSet_Ioi]
      change J {z : Ω × ℝ | a < runningSup X z.2.toNNReal z.1} = _
      exact esscher_positive_root_exp_clock_supremum_tail_ws01d
        X phi q hphi hq hroot p hp lam hlam hshift a ha
    have hνtail : ν (Ioi a) =
        ENNReal.ofReal (Real.exp (-(lam * a))) :=
      avram_ws01e_b_expMeasure_strict_survival_real lam a hlam ha.le
    rw [hcomp μ a, hcomp ν a, hμtail, hνtail]
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hrpos (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  have hranti : Antitone r := by
    intro i j hij
    dsimp [r]
    have hposi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    have hijr : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      have h : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      linarith
    exact one_div_le_one_div_of_le hposi hijr
  have hrtend : Tendsto r atTop (nhds (0 : ℝ)) := by
    simpa only [r] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
          atTop (nhds (0 : ℝ)))
  have hrInter : (⋂ n : ℕ, Iic (r n)) = Iic (0 : ℝ) := by
    ext x
    simp only [Set.mem_iInter, Set.mem_Iic]
    constructor
    · intro hx
      by_contra hnot
      have hxpos : (0 : ℝ) < x := lt_of_not_ge hnot
      obtain ⟨n, hn⟩ :=
        (hrtend.eventually (eventually_lt_nhds hxpos)).exists
      exact (not_lt_of_ge (hx n)) hn
    · intro hx n
      exact le_trans hx (le_of_lt (hrpos n))
  have hsetanti : Antitone (fun n : ℕ => Iic (r n)) := by
    intro i j hij; exact Iic_subset_Iic.mpr (hranti hij)
  have hμInter :
      μ (⋂ n : ℕ, Iic (r n)) =
        ⨅ n : ℕ, μ (Iic (r n)) :=
    hsetanti.measure_iInter
      (fun n => (measurableSet_Iic :
        MeasurableSet (Iic (r n))).nullMeasurableSet)
      ⟨0, measure_ne_top μ (Iic (r 0))⟩
  have hνInter :
      ν (⋂ n : ℕ, Iic (r n)) =
        ⨅ n : ℕ, ν (Iic (r n)) :=
    hsetanti.measure_iInter
      (fun n => (measurableSet_Iic :
        MeasurableSet (Iic (r n))).nullMeasurableSet)
      ⟨0, measure_ne_top ν (Iic (r 0))⟩
  have hzero : μ (Iic (0 : ℝ)) = ν (Iic (0 : ℝ)) := by
    calc
      μ (Iic (0 : ℝ)) = μ (⋂ n : ℕ, Iic (r n)) := by rw [hrInter]
      _ = ⨅ n : ℕ, μ (Iic (r n)) := hμInter
      _ = ⨅ n : ℕ, ν (Iic (r n)) := by
        congr 1
        funext n
        exact hpos (r n) (hrpos n)
      _ = ν (⋂ n : ℕ, Iic (r n)) := hνInter.symm
      _ = ν (Iic (0 : ℝ)) := by rw [hrInter]
  have hνtail0 : ν (Ioi (0 : ℝ)) = 1 := by
    simpa using (avram_ws01e_b_expMeasure_strict_survival_real lam 0 hlam le_rfl)
  have hνzero : ν (Iic (0 : ℝ)) = 0 := by rw [hcomp ν 0, hνtail0]; simp
  have hμzero : μ (Iic (0 : ℝ)) = 0 := hzero.trans hνzero
  have hneg (a : ℝ) (ha : a < 0) : μ (Iic a) = ν (Iic a) := by
    have hs : Iic a ⊆ Iic (0 : ℝ) := Iic_subset_Iic.mpr ha.le
    have hμ : μ (Iic a) = 0 := by
      refine le_antisymm ?_ bot_le
      simpa only [hμzero] using (measure_mono (μ := μ) hs)
    have hν : ν (Iic a) = 0 := by
      refine le_antisymm ?_ bot_le
      simpa only [hνzero] using (measure_mono (μ := ν) hs)
    exact hμ.trans hν.symm
  have heq : μ = ν := by
    apply Measure.ext_of_Iic μ ν
    intro a
    by_cases ha : 0 < a
    · exact hpos a ha
    by_cases hneg' : a < 0
    · exact hneg a hneg'
    have ha0 : a = 0 :=
      le_antisymm (le_of_not_gt ha) (le_of_not_gt hneg')
    subst a
    exact hzero
  exact heq
