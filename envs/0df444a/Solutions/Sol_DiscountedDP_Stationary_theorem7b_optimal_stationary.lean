-- Prove2me | solution 1 for DiscountedDP.Stationary.theorem7b_optimal_stationary
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:14:26.862836+00:00
-- url     : https://prove2.me/submissions/b80d80f0-3064-4811-b046-a16bb91ac9d9

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Operators



namespace DiscountedDP.Stationary

open MeasureTheory ProbabilityTheory

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

lemma d6_hsnd (n : ℕ) : Measurable (fun h : Hist S A n => h.2) := measurable_snd

lemma d6_prob (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) :
    ∀ n, IsProbabilityMeasure (historyLaw P π s n) := by
  intro n
  induction n with
  | zero => simp only [historyLaw]; exact Measure.dirac.isProbabilityMeasure
  | succ n ih =>
    haveI := π.κ_markov n
    haveI := P.q_markov
    haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
    simp only [historyLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)

lemma d6_stage_prob (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    IsProbabilityMeasure (stageLaw P π s n) := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI := d6_prob P π s n
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  simp only [stageLaw]
  infer_instance

lemma d6_hist_succ (P : Problem S A) (π : Plan (S := S) (A := A)) (s : S) (n : ℕ)
    (g : S → ℝ) (hg : Measurable g) :
    ∫ h, g h.2 ∂historyLaw P π s (n+1) = ∫ x, g x.2 ∂stageLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  simp only [historyLaw, stageLaw]
  have hφ : Measurable (fun x : (Hist S A n × A) × S =>
          (((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => S × A)
            (Fin.last n)).symm ((x.1.1.2, x.1.2), x.1.1.1), x.2) : Hist S A (n+1))) := by fun_prop
  exact integral_map hφ.aemeasurable (f := fun h : Hist S A (n+1) => g h.2)
    ((hg.comp (d6_hsnd (n+1))).aestronglyMeasurable)

lemma d6_bdd_int {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ x, |g x| ≤ C) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall (fun x => by simpa using hC x))

lemma c3_meas (P : Problem S A) (f : S → A) (hf : Measurable f) (F : S × A × S → ℝ)
    (hF : Measurable F) : Measurable (fun x => ∫ y, F (x, f x, y) ∂P.q (x, f x)) := by
  haveI := P.q_markov
  have hm : Measurable (fun s : S => (s, f s)) := measurable_id.prodMk hf
  let κ := P.q.comap (fun s : S => (s, f s)) hm
  have h : StronglyMeasurable (fun x => ∫ y, F (x, f x, y) ∂κ x) := by
    apply StronglyMeasurable.integral_kernel_prod_right (κ := κ)
      (f := fun (x : S) (y : S) => F (x, f x, y))
    apply Measurable.stronglyMeasurable
    exact hF.comp (measurable_fst.prodMk ((hf.comp measurable_fst).prodMk measurable_snd))
  exact h.measurable

lemma c3_bound (P : Problem S A) (x : S) (a : A) (F : S × A × S → ℝ)
    (C : ℝ) (hC : ∀ z, |F z| ≤ C) : |∫ y, F (x, a, y) ∂P.q (x, a)| ≤ C := by
  haveI := P.q_markov
  have := norm_integral_le_of_norm_le_const (μ := P.q (x, a))
    (f := fun y => F (x, a, y)) (C := C)
    (Filter.Eventually.of_forall (fun y => by simpa using hC _))
  simpa using this

lemma c3_PBM (P : Problem S A) (f : S → A) (hf : Measurable f) (g : S → ℝ) (hg : IsBM g) :
    IsBM (fun x => ∫ y, g y ∂P.q (x, f x)) := by
  obtain ⟨C, hC⟩ := hg.2
  exact ⟨c3_meas P f hf (fun z => g z.2.2) (hg.1.comp (measurable_snd.comp measurable_snd)),
    C, fun x => c3_bound P x (f x) (fun z => g z.2.2) C (fun z => hC _)⟩

lemma c3_stage (P : Problem S A) (σ : MarkovPlan S A) (s : S) (n : ℕ)
    (F : S × A × S → ℝ) (hF : Measurable F) (C : ℝ) (hC : ∀ z, |F z| ≤ C) :
    ∫ x, F (x.1.1.2, x.1.2, x.2) ∂stageLaw P σ.toPlan s n =
      ∫ h, (∫ y, F (h.2, (σ n).1 h.2, y) ∂P.q (h.2, (σ n).1 h.2)) ∂historyLaw P σ.toPlan s n := by
  haveI := σ.toPlan.κ_markov n
  haveI := P.q_markov
  haveI := d6_prob P σ.toPlan s n
  haveI := d6_stage_prob P σ.toPlan s n
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  set μ := historyLaw P σ.toPlan s n with hμ
  set κ := σ.toPlan.κ n with hκ
  have iF : Integrable (fun x : (Hist S A n × A) × S => F (x.1.1.2, x.1.2, x.2)) (stageLaw P σ.toPlan s n) :=
    d6_bdd_int _ _ (hF.comp (by fun_prop)) C (fun x => hC _)
  have hst : stageLaw P σ.toPlan s n = (μ.compProd κ).compProd (nextKernel P n) := rfl
  rw [hst] at iF ⊢
  rw [Measure.integral_compProd iF]
  have hnext : ∀ p : Hist S A n × A, nextKernel P n p = P.q (p.1.2, p.2) := by
    intro p
    simp only [nextKernel]
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have hGm : StronglyMeasurable (fun p : Hist S A n × A =>
      ∫ y, F (p.1.2, p.2, y) ∂nextKernel P n p) := by
    apply StronglyMeasurable.integral_kernel_prod_right (κ := nextKernel P n)
      (f := fun (p : Hist S A n × A) (y : S) => F (p.1.2, p.2, y))
    apply Measurable.stronglyMeasurable
    exact hF.comp (by fun_prop)
  have iG : Integrable (fun p : Hist S A n × A => ∫ y, F (p.1.2, p.2, y) ∂nextKernel P n p)
      (μ.compProd κ) := by
    refine d6_bdd_int _ _ hGm.measurable C (fun p => ?_)
    rw [hnext]; exact c3_bound P _ _ F C hC
  rw [Measure.integral_compProd iG]
  congr 1
  funext h
  have hk : κ h = Measure.dirac ((σ n).1 h.2) := by
    rw [hκ]; simp only [MarkovPlan.toPlan]; rw [Kernel.deterministic_apply]
  rw [hk, integral_dirac' _ _ ?_]
  · rw [hnext]
  · exact (hGm.measurable.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

lemma c3_Esucc (P : Problem S A) (σ : MarkovPlan S A) (s : S) (n : ℕ) (g : S → ℝ) (hg : IsBM g) :
    ∫ h, g h.2 ∂historyLaw P σ.toPlan s (n+1) =
      ∫ h, (∫ y, g y ∂P.q (h.2, (σ n).1 h.2)) ∂historyLaw P σ.toPlan s n := by
  obtain ⟨C, hC⟩ := hg.2
  rw [d6_hist_succ P σ.toPlan s n g hg.1]
  exact c3_stage P σ s n (fun z => g z.2.2) (hg.1.comp (measurable_snd.comp measurable_snd)) C
    (fun z => hC _)

lemma c3_E0 (P : Problem S A) (σ : Plan (S := S) (A := A)) (s : S) (g : S → ℝ) (hg : Measurable g) :
    ∫ h, g h.2 ∂historyLaw P σ s 0 = g s := by
  simp only [historyLaw]
  exact integral_dirac' _ _ ((hg.comp measurable_snd).stronglyMeasurable)

lemma c3_EBM (P : Problem S A) (σ : MarkovPlan S A) (n : ℕ) :
    ∀ g : S → ℝ, IsBM g → IsBM (fun s => ∫ h, g h.2 ∂historyLaw P σ.toPlan s n) := by
  induction n with
  | zero =>
    intro g hg
    have : (fun s => ∫ h, g h.2 ∂historyLaw P σ.toPlan s 0) = g := funext (fun s => c3_E0 P _ s g hg.1)
    rw [this]; exact hg
  | succ n ih =>
    intro g hg
    have : (fun s => ∫ h, g h.2 ∂historyLaw P σ.toPlan s (n+1)) =
        (fun s => ∫ h, (fun x => ∫ y, g y ∂P.q (x, (σ n).1 x)) h.2 ∂historyLaw P σ.toPlan s n) :=
      funext (fun s => c3_Esucc P σ s n g hg)
    rw [this]
    exact ih _ (c3_PBM P _ (σ n).2 g hg)

lemma c3_cons_succ (f : {g : S → A // Measurable g}) (π : MarkovPlan S A) (n : ℕ) :
    MarkovPlan.cons f π (n+1) = π n := by
  simp [MarkovPlan.cons]

lemma c3_cons_zero (f : {g : S → A // Measurable g}) (π : MarkovPlan S A) :
    MarkovPlan.cons f π 0 = f := by
  simp [MarkovPlan.cons]

lemma c3_Econs (P : Problem S A) (f : {g : S → A // Measurable g}) (π : MarkovPlan S A) (n : ℕ) :
    ∀ g : S → ℝ, IsBM g → ∀ s,
      ∫ h, g h.2 ∂historyLaw P (MarkovPlan.cons f π).toPlan s (n+1) =
        ∫ s', (∫ h, g h.2 ∂historyLaw P π.toPlan s' n) ∂P.q (s, f.1 s) := by
  induction n with
  | zero =>
    intro g hg s
    rw [c3_Esucc P _ s 0 g hg, c3_E0 P _ s _ (c3_PBM P _ ((MarkovPlan.cons f π 0).2) g hg).1,
      c3_cons_zero]
    congr 1; funext s'
    rw [c3_E0 P _ s' g hg.1]
  | succ n ih =>
    intro g hg s
    rw [c3_Esucc P _ s (n+1) g hg, c3_cons_succ]
    rw [ih _ (c3_PBM P _ (π n).2 g hg) s]
    congr 1; funext s'
    rw [c3_Esucc P π s' n g hg]

/-- one-step expected reward of a rule -/
noncomputable def c3_gr (P : Problem S A) (f : S → A) (x : S) : ℝ :=
  ∫ y, P.r (x, f x, y) ∂P.q (x, f x)

lemma c3_grBM (P : Problem S A) (f : {g : S → A // Measurable g}) : IsBM (c3_gr P f.1) := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  exact ⟨c3_meas P f.1 f.2 P.r P.r_measurable, Cr, fun x => c3_bound P x _ P.r Cr hr⟩

lemma c3_stageReward (P : Problem S A) (σ : MarkovPlan S A) (s : S) (n : ℕ) :
    stageReward P σ.toPlan s n = ∫ h, c3_gr P (σ n).1 h.2 ∂historyLaw P σ.toPlan s n := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  exact c3_stage P σ s n P.r P.r_measurable Cr hr

lemma c3_RBM (P : Problem S A) (σ : MarkovPlan S A) (n : ℕ) :
    IsBM (fun s => stageReward P σ.toPlan s n) := by
  have : (fun s => stageReward P σ.toPlan s n) =
      (fun s => ∫ h, c3_gr P (σ n).1 h.2 ∂historyLaw P σ.toPlan s n) :=
    funext (fun s => c3_stageReward P σ s n)
  rw [this]
  exact c3_EBM P σ n _ (c3_grBM P (σ n))

lemma c3_Rbound (P : Problem S A) (σ : Plan (S := S) (A := A)) (Cr : ℝ) (hr : ∀ x, |P.r x| ≤ Cr)
    (s : S) (n : ℕ) : |stageReward P σ s n| ≤ Cr := by
  haveI := d6_stage_prob P σ s n
  have := norm_integral_le_of_norm_le_const (μ := stageLaw P σ s n)
    (f := fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (C := Cr)
    (Filter.Eventually.of_forall (fun h => by simpa using hr _))
  simpa [stageReward] using this

lemma c3_summable (P : Problem S A) (σ : Plan (S := S) (A := A)) (Cr : ℝ) (hr : ∀ x, |P.r x| ≤ Cr)
    (s : S) : Summable (fun n => P.β ^ n * stageReward P σ s n) := by
  refine Summable.of_norm_bounded (g := fun n => Cr * P.β ^ n)
    ((summable_geometric_of_lt_one P.β_nonneg P.β_lt_one).mul_left Cr) ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg P.β_nonneg n), mul_comm]
  exact mul_le_mul_of_nonneg_right (c3_Rbound P σ Cr hr s n) (pow_nonneg P.β_nonneg n)

lemma c3_IBM (P : Problem S A) (σ : MarkovPlan S A) : IsBM (I P σ.toPlan) := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  have hβ0 := P.β_nonneg
  have hβ1 := P.β_lt_one
  refine ⟨?_, Cr / (1 - P.β), fun s => ?_⟩
  · have ht : Filter.Tendsto (fun N s => ∑ k ∈ Finset.range N, P.β ^ k * stageReward P σ.toPlan s k)
        Filter.atTop (nhds (I P σ.toPlan)) :=
      tendsto_pi_nhds.mpr (fun s => (c3_summable P σ.toPlan Cr hr s).hasSum.tendsto_sum_nat)
    refine measurable_of_tendsto_metrizable (fun N => ?_) ht
    exact Finset.measurable_sum _ (fun k _ => (c3_RBM P σ k).1.const_mul _)
  · have hs := c3_summable P σ.toPlan Cr hr s
    have h1 : |I P σ.toPlan s| ≤ ∑' n, Cr * P.β ^ n := by
      unfold I
      rw [← Real.norm_eq_abs]
      refine tsum_of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left Cr).hasSum ?_
      intro n
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
      exact mul_le_mul_of_nonneg_right (c3_Rbound P σ.toPlan Cr hr s n) (pow_nonneg hβ0 n)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1] at h1
    simpa [div_eq_mul_inv] using h1

theorem theorem3c_core
    (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : MarkovPlan S A) :
    ∀ s, T P f (I P π.toPlan) s =
      I P (MarkovPlan.cons f π).toPlan s := by
  intro s
  haveI := P.q_markov
  obtain ⟨Cr, hr⟩ := P.r_bounded
  have hβ0 := P.β_nonneg
  have hβ1 := P.β_lt_one
  set μ := P.q (s, f.1 s) with hμ
  have hR0 : stageReward P (MarkovPlan.cons f π).toPlan s 0 = ∫ y, P.r (s, f.1 s, y) ∂μ := by
    rw [c3_stageReward, c3_E0 P _ s _ (c3_grBM P _).1, c3_cons_zero]; rfl
  have hRs : ∀ n, stageReward P (MarkovPlan.cons f π).toPlan s (n+1) =
      ∫ s', stageReward P π.toPlan s' n ∂μ := by
    intro n
    rw [c3_stageReward, c3_cons_succ, c3_Econs P f π n _ (c3_grBM P _) s]
    congr 1; funext s'
    rw [c3_stageReward]
  have hsum := c3_summable P (MarkovPlan.cons f π).toPlan Cr hr s
  unfold I
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, hR0, hRs]
  -- swap tsum and integral
  have hRm : ∀ n, IsBM (fun s' => stageReward P π.toPlan s' n) := fun n => c3_RBM P π n
  have iF : ∀ n, Integrable (fun s' => P.β ^ (n+1) * stageReward P π.toPlan s' n) μ := fun n =>
    d6_bdd_int μ _ ((hRm n).1.const_mul _) (P.β ^ (n+1) * Cr) (fun s' => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ0 _)]
      exact mul_le_mul_of_nonneg_left (c3_Rbound P _ Cr hr s' n) (pow_nonneg hβ0 _))
  have hswap : ∑' n, P.β ^ (n+1) * ∫ s', stageReward P π.toPlan s' n ∂μ =
      ∫ s', ∑' n, P.β ^ (n+1) * stageReward P π.toPlan s' n ∂μ := by
    simp_rw [← integral_const_mul]
    apply integral_tsum_of_summable_integral_norm iF
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
      (f := fun n => Cr * P.β ^ (n+1)) (fun n => ?_)
      (((summable_geometric_of_lt_one hβ0 hβ1).mul_left Cr).comp_injective (add_left_injective 1))
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun s' => ‖P.β ^ (n+1) * stageReward P π.toPlan s' n‖) (C := Cr * P.β ^ (n+1))
      (Filter.Eventually.of_forall (fun s' => by
        rw [norm_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 _), mul_comm]
        exact mul_le_mul_of_nonneg_right (c3_Rbound P _ Cr hr s' n) (pow_nonneg hβ0 _)))
    exact (le_abs_self _).trans (by simpa using this)
  rw [hswap]
  have hinner : ∀ s', ∑' n, P.β ^ (n+1) * stageReward P π.toPlan s' n =
      P.β * ∑' n, P.β ^ n * stageReward P π.toPlan s' n := by
    intro s'
    rw [← tsum_mul_left]
    congr 1; funext n; ring
  simp_rw [hinner]
  unfold T
  have hIBM := c3_IBM P π
  obtain ⟨CI, hCI⟩ := hIBM.2
  have i1 : Integrable (fun y => P.r (s, f.1 s, y)) μ :=
    d6_bdd_int μ _ (P.r_measurable.comp (by fun_prop)) Cr (fun y => hr _)
  have i2 : Integrable (fun y => P.β * I P π.toPlan y) μ :=
    d6_bdd_int μ _ (hIBM.1.const_mul _) (P.β * CI) (fun y => by
      rw [abs_mul, abs_of_nonneg hβ0]; exact mul_le_mul_of_nonneg_left (hCI y) hβ0)
  change ∫ s', (P.r (s, f.1 s, s') + P.β * I P π.toPlan s') ∂μ = _
  rw [integral_add i1 i2]
  rfl

lemma d6_step (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s)
    (π : Plan (S := S) (A := A)) (s : S) (n : ℕ) :
    stageReward P π s n + P.β * ∫ h, u h.2 ∂historyLaw P π s (n+1) ≤
      ∫ h, u h.2 ∂historyLaw P π s n := by
  haveI := π.κ_markov n
  haveI := P.q_markov
  haveI := d6_prob P π s n
  haveI := d6_stage_prob P π s n
  haveI : IsMarkovKernel (nextKernel P n) := by unfold nextKernel; infer_instance
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hβ := P.β_nonneg
  rw [d6_hist_succ P π s n u hu.1]
  have hrm : Measurable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) :=
    P.r_measurable.comp (by fun_prop)
  have hum : Measurable (fun x : (Hist S A n × A) × S => u x.2) := hu.1.comp measurable_snd
  have i1 : Integrable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (stageLaw P π s n) :=
    d6_bdd_int _ _ hrm Cr (fun x => hr _)
  have i2 : Integrable (fun x : (Hist S A n × A) × S => u x.2) (stageLaw P π s n) :=
    d6_bdd_int _ _ hum Cu (fun x => hCu _)
  have e1 : stageReward P π s n + P.β * ∫ x, u x.2 ∂stageLaw P π s n =
      ∫ x, (P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) ∂stageLaw P π s n := by
    rw [integral_add i1 (i2.const_mul _), integral_const_mul]; rfl
  rw [e1]
  set μ := historyLaw P π s n with hμ
  set κ := π.κ n
  have hGm : Measurable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) :=
    hrm.add (hum.const_mul _)
  have iG : Integrable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2)
      (stageLaw P π s n) := i1.add (i2.const_mul _)
  have e2 : ∫ x, (P.r (x.1.1.2, x.1.2, x.2) + P.β * u x.2) ∂stageLaw P π s n =
      ∫ p, (∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p) ∂(μ.compProd κ) := by
    have : stageLaw P π s n = (μ.compProd κ).compProd (nextKernel P n) := rfl
    rw [this] at iG ⊢
    rw [Measure.integral_compProd iG]
  rw [e2]
  have hnext : ∀ p : Hist S A n × A, nextKernel P n p = P.q (p.1.2, p.2) := by
    intro p
    simp only [nextKernel]
    rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply]
  have e3 : ∀ p : Hist S A n × A, ∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p =
      Ta P p.2 u p.1.2 := by
    intro p; rw [hnext]; rfl
  simp_rw [e3]
  -- integrability
  have hTam : Measurable (fun p : Hist S A n × A => Ta P p.2 u p.1.2) := by
    have h : StronglyMeasurable (fun p : Hist S A n × A =>
        ∫ s', (P.r (p.1.2, p.2, s') + P.β * u s') ∂nextKernel P n p) := by
      apply StronglyMeasurable.integral_kernel_prod_right (κ := nextKernel P n)
        (f := fun (p : Hist S A n × A) (s' : S) => P.r (p.1.2, p.2, s') + P.β * u s')
      apply Measurable.stronglyMeasurable
      exact (P.r_measurable.comp (by fun_prop)).add ((hu.1.comp measurable_snd).const_mul _)
    simp_rw [e3] at h
    exact h.measurable
  have hTab : ∀ p : Hist S A n × A, |Ta P p.2 u p.1.2| ≤ Cr + P.β * Cu := by
    intro p
    have := norm_integral_le_of_norm_le_const (μ := P.q (p.1.2, p.2))
      (f := fun s' => P.r (p.1.2, p.2, s') + P.β * u s') (C := Cr + P.β * Cu)
      (Filter.Eventually.of_forall (fun s' => by
        simp only [Real.norm_eq_abs]
        calc |P.r (p.1.2, p.2, s') + P.β * u s'| ≤ |P.r (p.1.2, p.2, s')| + |P.β * u s'| := abs_add_le _ _
          _ ≤ Cr + P.β * Cu := by
            rw [abs_mul, abs_of_nonneg hβ]
            exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (hCu s') hβ)))
    simpa [Ta] using this
  have iT : Integrable (fun p : Hist S A n × A => Ta P p.2 u p.1.2) (μ.compProd κ) :=
    d6_bdd_int _ _ hTam _ hTab
  have iU : Integrable (fun p : Hist S A n × A => u p.1.2) (μ.compProd κ) :=
    d6_bdd_int _ _ (hu.1.comp (measurable_snd.comp measurable_fst)) Cu (fun p => hCu _)
  calc ∫ p, Ta P p.2 u p.1.2 ∂(μ.compProd κ) ≤ ∫ p, u p.1.2 ∂(μ.compProd κ) :=
        integral_mono iT iU (fun p => hupper _ _)
    _ = ∫ h, u h.2 ∂μ := by
        rw [Measure.integral_compProd iU]
        congr 1; funext h
        simp

theorem theorem6d_core
    (P : Problem S A) (u : S → ℝ) (hu : IsBM u)
    (hupper : ∀ a s, Ta P a u s ≤ u s) :
    ∀ π : Plan (S := S) (A := A), ∀ s, I P π s ≤ u s := by
  intro π s
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hβ0 := P.β_nonneg
  have hβ1 := P.β_lt_one
  set W : ℕ → ℝ := fun n => ∫ h, u h.2 ∂historyLaw P π s n with hW
  set R : ℕ → ℝ := fun n => stageReward P π s n with hR
  have hstep : ∀ n, R n + P.β * W (n+1) ≤ W n := fun n => d6_step P u hu hupper π s n
  have hW0 : W 0 = u s := by
    simp only [hW, historyLaw]
    exact integral_dirac' _ _ ((hu.1.comp measurable_snd).stronglyMeasurable)
  have hWb : ∀ n, |W n| ≤ Cu := by
    intro n
    haveI := d6_prob P π s n
    have := norm_integral_le_of_norm_le_const (μ := historyLaw P π s n) (f := fun h => u h.2) (C := Cu)
      (Filter.Eventually.of_forall (fun h => by simpa using hCu h.2))
    simpa using this
  have hRb : ∀ n, |R n| ≤ Cr := by
    intro n
    haveI := d6_stage_prob P π s n
    have := norm_integral_le_of_norm_le_const (μ := stageLaw P π s n)
      (f := fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (C := Cr)
      (Filter.Eventually.of_forall (fun h => by simpa using hr _))
    simpa [hR, stageReward] using this
  have hsum : Summable (fun n => P.β ^ n * R n) := by
    refine Summable.of_norm_bounded (g := fun n => Cr * P.β ^ n)
      ((summable_geometric_of_lt_one hβ0 hβ1).mul_left Cr) ?_
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 n), mul_comm]
    exact mul_le_mul_of_nonneg_right (hRb n) (pow_nonneg hβ0 n)
  have hpartial : ∀ N, ∑ k ∈ Finset.range N, P.β ^ k * R k ≤ W 0 - P.β ^ N * W N := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have := hstep N
      have hp : 0 ≤ P.β ^ N := pow_nonneg hβ0 N
      have : P.β ^ N * R N ≤ P.β ^ N * W N - P.β ^ (N+1) * W (N+1) := by
        rw [pow_succ]; nlinarith
      linarith
  have hbound : ∀ N, ∑ k ∈ Finset.range N, P.β ^ k * R k ≤ u s + P.β ^ N * Cu := by
    intro N
    have h1 := hpartial N
    have h2 : -(P.β ^ N * W N) ≤ P.β ^ N * Cu := by
      have := (abs_le.mp (hWb N)).1
      have hp : 0 ≤ P.β ^ N := pow_nonneg hβ0 N
      nlinarith
    linarith
  have ht : Filter.Tendsto (fun N => ∑ k ∈ Finset.range N, P.β ^ k * R k) Filter.atTop
      (nhds (I P π s)) := hsum.hasSum.tendsto_sum_nat
  have ht2 : Filter.Tendsto (fun N : ℕ => u s + P.β ^ N * Cu) Filter.atTop (nhds (u s + 0 * Cu)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const Cu)
  have := le_of_tendsto_of_tendsto' ht ht2 hbound
  simpa using this

lemma t4_T_measurable (P : Problem S A) (f : {g : S → A // Measurable g})
    (u : S → ℝ) (hu : IsBM u) : Measurable (T P f u) := by
  haveI := P.q_markov
  have hm : Measurable (fun s : S => (s, f.1 s)) := measurable_id.prodMk f.2
  let κ := P.q.comap (fun s : S => (s, f.1 s)) hm
  have h : StronglyMeasurable (fun s => ∫ s', P.r (s, f.1 s, s') + P.β * u s' ∂κ s) := by
    apply StronglyMeasurable.integral_kernel_prod_right
      (f := fun s s' => P.r (s, f.1 s, s') + P.β * u s')
    apply Measurable.stronglyMeasurable
    apply Measurable.add
    · exact P.r_measurable.comp (measurable_fst.prodMk ((f.2.comp measurable_fst).prodMk measurable_snd))
    · exact (hu.1.comp measurable_snd).const_mul _
  exact h.measurable

lemma t4_T_bound (P : Problem S A) (f : {g : S → A // Measurable g})
    (u : S → ℝ) (Cr Cu : ℝ) (hr : ∀ x, |P.r x| ≤ Cr) (hu : ∀ s, |u s| ≤ Cu) (s : S) :
    |T P f u s| ≤ Cr + P.β * Cu := by
  haveI := P.q_markov
  have := norm_integral_le_of_norm_le_const (μ := P.q (s, f.1 s))
    (f := fun s' => P.r (s, f.1 s, s') + P.β * u s') (C := Cr + P.β * Cu)
    (Filter.Eventually.of_forall (fun s' => by
      simp only [Real.norm_eq_abs]
      calc |P.r (s, f.1 s, s') + P.β * u s'| ≤ |P.r (s, f.1 s, s')| + |P.β * u s'| := abs_add_le _ _
        _ ≤ Cr + P.β * Cu := by
          rw [abs_mul, abs_of_nonneg P.β_nonneg]
          exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (hu s') P.β_nonneg)))
  simpa [T] using this

theorem theorem4d_core
    (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ)
    (hu : IsBM u) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : {g : S → A // Measurable g}, IsGenerated π f ∧
      ∀ s, U P π u s - ε ≤ T P f u s := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hbdd : ∀ s, BddAbove (Set.range fun n => T P (π n) u s) := by
    intro s
    refine ⟨Cr + P.β * Cu, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (le_abs_self _).trans (t4_T_bound P (π n) u Cr Cu hr hCu s)
  have hex : ∀ s, ∃ n, U P π u s - ε < T P (π n) u s := by
    intro s
    exact exists_lt_of_lt_ciSup (by unfold U; linarith : U P π u s - ε < ⨆ n, T P (π n) u s)
  have hUm : Measurable (U P π u) := by
    unfold U
    exact Measurable.iSup (fun n => t4_T_measurable P (π n) u hu)
  have hset : ∀ n, MeasurableSet {s | U P π u s - ε < T P (π n) u s} := fun n =>
    measurableSet_lt (hUm.sub_const ε) (t4_T_measurable P (π n) u hu)
  classical
  let N : S → ℕ := fun s => Nat.find (hex s)
  have hN : Measurable N := measurable_find (p := fun s n => U P π u s - ε < T P (π n) u s) hex hset
  have hfm : Measurable (fun s => (π (N s)).1 s) :=
    Measurable.find (f := fun n s => (π n).1 s) (p := fun n s => U P π u s - ε < T P (π n) u s)
      (fun n => (π n).2) hset hex
  refine ⟨⟨fun s => (π (N s)).1 s, hfm⟩, ⟨fun n => N ⁻¹' {n}, fun n => hN (measurableSet_singleton n), ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    exact Set.disjoint_left.mpr (fun s hi hj => hij (by simp at hi hj; omega))
  · ext s; simp
  · intro n s hs
    simp at hs
    simp [hs]
  · intro s
    exact (Nat.find_spec (hex s)).le

lemma t5_le_supNorm {S : Type*} {u : S → ℝ} (h : ∃ C : ℝ, ∀ s, |u s| ≤ C) (s : S) :
    |u s| ≤ supNorm u := by
  obtain ⟨C, hC⟩ := h
  exact le_ciSup (f := fun s => |u s|) ⟨C, by rintro _ ⟨t, rfl⟩; exact hC t⟩ s

lemma t5_supNorm_le {S : Type*} [Nonempty S] {u : S → ℝ} {c : ℝ} (h : ∀ s, |u s| ≤ c) :
    supNorm u ≤ c := ciSup_le h

lemma t5_supNorm_nonneg {S : Type*} [Nonempty S] {u : S → ℝ} (h : ∃ C : ℝ, ∀ s, |u s| ≤ C) :
    0 ≤ supNorm u :=
  le_trans (abs_nonneg _) (t5_le_supNorm h (Classical.arbitrary S))

lemma t5_bdd_sub {S : Type*} [MeasurableSpace S] {u v : S → ℝ} (hu : IsBM u) (hv : IsBM v) :
    ∃ C : ℝ, ∀ s, |u s - v s| ≤ C := by
  obtain ⟨C, hC⟩ := hu.2
  obtain ⟨D, hD⟩ := hv.2
  exact ⟨C + D, fun s => (abs_sub _ _).trans (add_le_add (hC s) (hD s))⟩

lemma t5_BM_add {S : Type*} [MeasurableSpace S] {u : S → ℝ} (hu : IsBM u) (c : ℝ) :
    IsBM (fun t => u t + c) := by
  obtain ⟨C, hC⟩ := hu.2
  exact ⟨hu.1.add_const c, C + |c|, fun s => (abs_add_le _ _).trans (add_le_add (hC s) le_rfl)⟩

lemma t5_zero_of_le {x K β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (h : ∀ n : ℕ, |x| ≤ K * β ^ n) :
    x = 0 := by
  have ht : Filter.Tendsto (fun n : ℕ => K * β ^ n) Filter.atTop (nhds (K * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).const_mul K
  rw [mul_zero] at ht
  have : |x| ≤ 0 := ge_of_tendsto' ht h
  exact abs_nonpos_iff.mp this

theorem theorem5_core
    {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : (S → ℝ) → S → ℝ)
    (hmap : ∀ u, IsBM u → IsBM (V u))
    (hmono : ∀ u v, IsBM u → IsBM v →
      (∀ s, u s ≤ v s) → ∀ s, V u s ≤ V v s)
    (hshift : ∀ u, IsBM u → ∀ c : ℝ, ∀ s,
      V (fun t => u t + c) s = V u s + β * c) :
    (∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤
        β * supNorm (fun s => u s - v s)) ∧
    ∃ ustar : S → ℝ, IsBM ustar ∧ (∀ s, V ustar s = ustar s) ∧
      (∀ v, IsBM v → (∀ s, V v s = v s) → v = ustar) ∧
      ∀ u, IsBM u → ∀ n : ℕ,
        supNorm (fun s => (V^[n] u) s - ustar s) ≤
          β ^ n * supNorm (fun s => u s - ustar s) := by
  have hcon : ∀ u v, IsBM u → IsBM v →
      supNorm (fun s => V u s - V v s) ≤ β * supNorm (fun s => u s - v s) := by
    intro u v hu hv
    set c := supNorm (fun s => u s - v s) with hc
    have h1 : ∀ s, |u s - v s| ≤ c := fun s => t5_le_supNorm (u := fun s => u s - v s) (t5_bdd_sub hu hv) s
    have hA : ∀ s, V u s ≤ V v s + β * c := by
      intro s
      rw [← hshift v hv c s]
      exact hmono u _ hu (t5_BM_add hv c) (fun t => by have := h1 t; rw [abs_le] at this; linarith) s
    have hB : ∀ s, V v s ≤ V u s + β * c := by
      intro s
      rw [← hshift u hu c s]
      exact hmono v _ hv (t5_BM_add hu c) (fun t => by have := h1 t; rw [abs_le] at this; linarith) s
    apply t5_supNorm_le
    intro s
    rw [abs_le]
    constructor
    · linarith [hB s]
    · linarith [hA s]
  refine ⟨hcon, ?_⟩
  -- iterates
  set u : ℕ → S → ℝ := fun n => V^[n] (fun _ => 0) with hu_def
  have hBM0 : IsBM (fun _ : S => (0:ℝ)) := ⟨measurable_const, 0, fun s => by simp⟩
  have hiter : ∀ w, IsBM w → ∀ n, IsBM (V^[n] w) := by
    intro w hw n
    induction n with
    | zero => simpa using hw
    | succ n ih => rw [Function.iterate_succ_apply']; exact hmap _ ih
  have huBM : ∀ n, IsBM (u n) := fun n => hiter _ hBM0 n
  have usucc : ∀ n, u (n + 1) = V (u n) := fun n => by
    simp only [hu_def]; rw [Function.iterate_succ_apply']
  set D := supNorm (fun s => u 1 s - u 0 s) with hD
  have hdiff : ∀ n, supNorm (fun s => u (n+1) s - u n s) ≤ D * β ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, mul_one]
    | succ n ih =>
      have e : supNorm (fun s => u (n+1+1) s - u (n+1) s) = supNorm (fun s => V (u (n+1)) s - V (u n) s) := by
        rw [usucc (n+1), usucc n]
      rw [e]
      calc supNorm (fun s => V (u (n+1)) s - V (u n) s)
          ≤ β * supNorm (fun s => u (n+1) s - u n s) := hcon _ _ (huBM _) (huBM _)
        _ ≤ β * (D * β ^ n) := mul_le_mul_of_nonneg_left ih hβ0
        _ = D * β ^ (n+1) := by ring
  have hpt : ∀ s n, dist (u n s) (u (n+1) s) ≤ D * β ^ n := by
    intro s n
    rw [Real.dist_eq, abs_sub_comm]
    exact (t5_le_supNorm (u := fun s => u (n+1) s - u n s) (t5_bdd_sub (huBM _) (huBM _)) s).trans (hdiff n)
  have hcs : ∀ s, CauchySeq (fun n => u n s) := fun s => cauchySeq_of_le_geometric β D hβ1 (hpt s)
  choose L hL using fun s => cauchySeq_tendsto_of_complete (hcs s)
  have hdistL : ∀ s n, |u n s - L s| ≤ D * β ^ n / (1 - β) := by
    intro s n
    rw [← Real.dist_eq]
    exact dist_le_of_le_geometric_of_tendsto β D hβ1 (hpt s) (hL s) n
  have hLBM : IsBM L := by
    refine ⟨measurable_of_tendsto_metrizable (fun n => (huBM n).1) (tendsto_pi_nhds.mpr hL), D * β ^ 0 / (1 - β), ?_⟩
    intro s
    have := hdistL s 0
    simp only [hu_def, Function.iterate_zero, id] at this
    simpa using this
  have hsupL : ∀ n, supNorm (fun s => u n s - L s) ≤ D * β ^ n / (1 - β) :=
    fun n => t5_supNorm_le (fun s => hdistL s n)
  have hfix : ∀ s, V L s = L s := by
    intro s
    have : V L s - L s = 0 := by
      apply t5_zero_of_le (K := 2 * D / (1 - β)) hβ0 hβ1
      intro n
      have h1 : |V L s - V (u n) s| ≤ β * (D * β ^ n / (1 - β)) := by
        have := t5_le_supNorm (u := fun s => V L s - V (u n) s) (t5_bdd_sub (hmap _ hLBM) (hmap _ (huBM n))) s
        refine this.trans ((hcon _ _ hLBM (huBM n)).trans (mul_le_mul_of_nonneg_left ?_ hβ0))
        have := hsupL n
        refine le_trans (le_of_eq ?_) this
        unfold supNorm; congr 1; funext t; exact abs_sub_comm _ _
      have h2 : |u (n+1) s - L s| ≤ D * β ^ (n+1) / (1 - β) := hdistL s (n+1)
      rw [usucc n] at h2
      have hD0 : 0 ≤ D := t5_supNorm_nonneg (t5_bdd_sub (huBM 1) (huBM 0))
      have hb : β * (D * β ^ n / (1 - β)) ≤ D * β ^ n / (1 - β) := by
        have : 0 ≤ D * β ^ n / (1 - β) := div_nonneg (mul_nonneg hD0 (pow_nonneg hβ0 n)) (by linarith)
        nlinarith
      have hb2 : D * β ^ (n+1) / (1 - β) ≤ D * β ^ n / (1 - β) := by
        rw [pow_succ, ← mul_assoc]
        have : 0 ≤ D * β ^ n / (1 - β) := div_nonneg (mul_nonneg hD0 (pow_nonneg hβ0 n)) (by linarith)
        rw [mul_div_right_comm]; nlinarith
      calc |V L s - L s| ≤ |V L s - V (u n) s| + |V (u n) s - L s| := abs_sub_le _ _ _
        _ ≤ D * β ^ n / (1 - β) + D * β ^ n / (1 - β) := add_le_add (h1.trans hb) (h2.trans hb2)
        _ = 2 * D / (1 - β) * β ^ n := by ring
    linarith
  refine ⟨L, hLBM, hfix, ?_, ?_⟩
  · intro v hv hvfix
    have hVv : V v = v := funext hvfix
    have hVL : V L = L := funext hfix
    have h := hcon v L hv hLBM
    rw [hVv, hVL] at h
    have h0 : 0 ≤ supNorm (fun s => v s - L s) := t5_supNorm_nonneg (t5_bdd_sub hv hLBM)
    have hz : supNorm (fun s => v s - L s) ≤ 0 := by nlinarith
    funext s
    have := (t5_le_supNorm (u := fun s => v s - L s) (t5_bdd_sub hv hLBM) s).trans hz
    have := abs_nonpos_iff.mp this
    linarith
  · intro w hw n
    induction n with
    | zero => simp
    | succ n ih =>
      have hVL : V L = L := funext hfix
      have e : (fun s => (V^[n+1] w) s - L s) = (fun s => V (V^[n] w) s - V L s) := by
        funext s; rw [Function.iterate_succ_apply', hVL]
      rw [e]
      calc _ ≤ β * supNorm (fun s => (V^[n] w) s - L s) := hcon _ _ (hiter w hw n) hLBM
        _ ≤ β * (β ^ n * supNorm (fun s => w s - L s)) := mul_le_mul_of_nonneg_left ih hβ0
        _ = _ := by ring


lemma a6_real_upper (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R W : ℕ → ℝ) (C d : ℝ) (hd : 0 ≤ d)
    (hs : Summable (fun n => β ^ n * R n)) (hW : ∀ n, |W n| ≤ C)
    (hstep : ∀ n, R n + β * W (n+1) ≤ W n + d) :
    ∑' n, β ^ n * R n ≤ W 0 + d / (1 - β) := by
  have hgs : Summable (fun n : ℕ => β ^ n) := summable_geometric_of_lt_one hβ0 hβ1
  have hpartial : ∀ N, ∑ k ∈ Finset.range N, β ^ k * R k ≤
      W 0 - β ^ N * W N + d * ∑ k ∈ Finset.range N, β ^ k := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have := hstep N
      have hp : 0 ≤ β ^ N := pow_nonneg hβ0 N
      have : β ^ N * R N ≤ β ^ N * W N - β ^ (N+1) * W (N+1) + d * β ^ N := by
        rw [pow_succ]; nlinarith
      linarith
  have hgeo : ∀ N, ∑ k ∈ Finset.range N, β ^ k ≤ 1 / (1 - β) := by
    intro N
    rw [one_div, ← tsum_geometric_of_lt_one hβ0 hβ1]
    exact hgs.sum_le_tsum _ (fun i _ => pow_nonneg hβ0 i)
  have hbound : ∀ N, ∑ k ∈ Finset.range N, β ^ k * R k ≤ W 0 + d / (1 - β) + β ^ N * C := by
    intro N
    have h1 := hpartial N
    have h2 : -(β ^ N * W N) ≤ β ^ N * C := by
      have := (abs_le.mp (hW N)).1
      have hp : 0 ≤ β ^ N := pow_nonneg hβ0 N
      nlinarith
    have h3 : d * ∑ k ∈ Finset.range N, β ^ k ≤ d / (1 - β) := by
      have := mul_le_mul_of_nonneg_left (hgeo N) hd
      simpa [div_eq_mul_inv] using this
    linarith
  have ht := hs.hasSum.tendsto_sum_nat
  have ht2 : Filter.Tendsto (fun N : ℕ => W 0 + d / (1 - β) + β ^ N * C) Filter.atTop
      (nhds (W 0 + d / (1 - β) + 0 * C)) :=
    tendsto_const_nhds.add ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const C)
  have := le_of_tendsto_of_tendsto' ht ht2 hbound
  simpa using this

lemma a6_real_lower (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (R W : ℕ → ℝ) (C d : ℝ) (hd : 0 ≤ d)
    (hs : Summable (fun n => β ^ n * R n)) (hW : ∀ n, |W n| ≤ C)
    (hstep : ∀ n, W n - d ≤ R n + β * W (n+1)) :
    W 0 - d / (1 - β) ≤ ∑' n, β ^ n * R n := by
  have := a6_real_upper β hβ0 hβ1 (fun n => -R n) (fun n => -W n) C d hd
    (by simpa [mul_neg] using hs.neg) (fun n => by simpa using hW n)
    (fun n => by have := hstep n; linarith)
  simp only [mul_neg, tsum_neg] at this
  linarith

lemma a6_TE (P : Problem S A) (σ : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u) (s : S) (n : ℕ) :
    stageReward P σ.toPlan s n + P.β * ∫ h, u h.2 ∂historyLaw P σ.toPlan s (n+1) =
      ∫ h, T P (σ n) u h.2 ∂historyLaw P σ.toPlan s n := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  haveI := d6_stage_prob P σ.toPlan s n
  have hβ := P.β_nonneg
  rw [d6_hist_succ P σ.toPlan s n u hu.1]
  have hF : Measurable (fun z : S × A × S => P.r z + P.β * u z.2.2) :=
    P.r_measurable.add ((hu.1.comp (measurable_snd.comp measurable_snd)).const_mul _)
  have := c3_stage P σ s n (fun z => P.r z + P.β * u z.2.2) hF (Cr + P.β * Cu) (fun z => by
    calc |P.r z + P.β * u z.2.2| ≤ |P.r z| + |P.β * u z.2.2| := abs_add_le _ _
      _ ≤ Cr + P.β * Cu := by
        rw [abs_mul, abs_of_nonneg hβ]
        exact add_le_add (hr _) (mul_le_mul_of_nonneg_left (hCu _) hβ))
  have i1 : Integrable (fun x : (Hist S A n × A) × S => P.r (x.1.1.2, x.1.2, x.2)) (stageLaw P σ.toPlan s n) :=
    d6_bdd_int _ _ (P.r_measurable.comp (by fun_prop)) Cr (fun x => hr _)
  have i2 : Integrable (fun x : (Hist S A n × A) × S => u x.2) (stageLaw P σ.toPlan s n) :=
    d6_bdd_int _ _ (hu.1.comp measurable_snd) Cu (fun x => hCu _)
  simp only at this
  rw [integral_add i1 (i2.const_mul _), integral_const_mul] at this
  exact this

lemma a6_upper (P : Problem S A) (σ : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u)
    (h : ∀ n x, T P (σ n) u x ≤ u x) : ∀ s, I P σ.toPlan s ≤ u s := by
  intro s
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have := a6_real_upper P.β P.β_nonneg P.β_lt_one (fun n => stageReward P σ.toPlan s n)
    (fun n => ∫ h, u h.2 ∂historyLaw P σ.toPlan s n) Cu 0 le_rfl
    (c3_summable P σ.toPlan Cr hr s)
    (fun n => by
      haveI := d6_prob P σ.toPlan s n
      have := norm_integral_le_of_norm_le_const (μ := historyLaw P σ.toPlan s n) (f := fun h => u h.2)
        (C := Cu) (Filter.Eventually.of_forall (fun h => by simpa using hCu h.2))
      simpa using this)
    (fun n => by
      rw [a6_TE P σ u hu s n, add_zero]
      haveI := d6_prob P σ.toPlan s n
      obtain ⟨CT, hCT⟩ := (t4_T_bound P (σ n) u Cr Cu hr hCu) |> fun hb => (⟨Cr + P.β * Cu, hb⟩ : ∃ C, ∀ x, |T P (σ n) u x| ≤ C)
      exact integral_mono (d6_bdd_int _ _ ((t4_T_measurable P (σ n) u hu).comp (d6_hsnd n)) CT (fun x => hCT _))
        (d6_bdd_int _ _ (hu.1.comp (d6_hsnd n)) Cu (fun x => hCu _)) (fun x => h n x.2))
  rw [c3_E0 P _ s u hu.1] at this
  simpa [I] using this

lemma a6_lower (P : Problem S A) (σ : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ n x, u x - c ≤ T P (σ n) u x) : ∀ s, u s - c / (1 - P.β) ≤ I P σ.toPlan s := by
  intro s
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have := a6_real_lower P.β P.β_nonneg P.β_lt_one (fun n => stageReward P σ.toPlan s n)
    (fun n => ∫ h, u h.2 ∂historyLaw P σ.toPlan s n) Cu c hc
    (c3_summable P σ.toPlan Cr hr s)
    (fun n => by
      haveI := d6_prob P σ.toPlan s n
      have := norm_integral_le_of_norm_le_const (μ := historyLaw P σ.toPlan s n) (f := fun h => u h.2)
        (C := Cu) (Filter.Eventually.of_forall (fun h => by simpa using hCu h.2))
      simpa using this)
    (fun n => by
      rw [a6_TE P σ u hu s n]
      haveI := d6_prob P σ.toPlan s n
      have hTi : Integrable (fun h : Hist S A n => T P (σ n) u h.2) (historyLaw P σ.toPlan s n) :=
        d6_bdd_int (historyLaw P σ.toPlan s n) _ ((t4_T_measurable P (σ n) u hu).comp (d6_hsnd n))
        (Cr + P.β * Cu) (fun x => t4_T_bound P (σ n) u Cr Cu hr hCu _)
      have hui : Integrable (fun h : Hist S A n => u h.2) (historyLaw P σ.toPlan s n) :=
        d6_bdd_int (historyLaw P σ.toPlan s n) _ (hu.1.comp (d6_hsnd n)) Cu (fun x => hCu _)
      have := integral_mono (f := fun h : Hist S A n => u h.2 - c) (hui.sub (integrable_const c)) hTi
        (fun x => h n x.2)
      rw [integral_sub hui (integrable_const c)] at this
      simpa using this)
  rw [c3_E0 P _ s u hu.1] at this
  simpa [I] using this

lemma a6_T_le_U (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u)
    (g : {g : S → A // Measurable g}) (hg : IsGenerated π g) (x : S) : T P g u x ≤ U P π u x := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  obtain ⟨pieces, -, -, hcov, hpc⟩ := hg
  have : x ∈ ⋃ n, pieces n := by rw [hcov]; trivial
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp this
  have e : T P g u x = T P (π m) u x := by
    unfold T; rw [hpc m x hm]
  rw [e]
  exact le_ciSup (f := fun n => T P (π n) u x) ⟨Cr + P.β * Cu, by
    rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (t4_T_bound P (π n) u Cr Cu hr hCu x)⟩ m

theorem theorem6a_core
    (P : Problem S A) (π : MarkovPlan S A) (ustar : S → ℝ)
    (hu : IsBM ustar) (hfix : ∀ s, U P π ustar s = ustar s) :
    (∀ π' : MarkovPlan S A, IsGeneratedPlan π π' →
      ∀ s, I P π'.toPlan s ≤ ustar s) ∧
    (∀ ε : ℝ, 0 < ε → ∃ f : {g : S → A // Measurable g},
      IsGenerated π f ∧ ∀ s,
        ustar s - ε ≤ I P (stationary f).toPlan s) ∧
    (∀ ε : ℝ, 0 < ε → ∀ f : {g : S → A // Measurable g},
      (∀ s, ustar s - ε * (1 - P.β) ≤ T P f ustar s) →
      ∀ s, ustar s - ε ≤ I P (stationary f).toPlan s) := by
  have hβ1 : 0 < 1 - P.β := by linarith [P.β_lt_one]
  have part3 : ∀ ε : ℝ, 0 < ε → ∀ f : {g : S → A // Measurable g},
      (∀ s, ustar s - ε * (1 - P.β) ≤ T P f ustar s) →
      ∀ s, ustar s - ε ≤ I P (stationary f).toPlan s := by
    intro ε hε f hf s
    have := a6_lower P (stationary f) ustar hu (ε * (1 - P.β)) (by positivity) (fun n x => hf x) s
    rwa [mul_div_cancel_right₀ _ hβ1.ne'] at this
  refine ⟨?_, ?_, part3⟩
  · intro π' hπ' s
    exact a6_upper P π' ustar hu (fun n x => (a6_T_le_U P π ustar hu (π' n) (hπ' n) x).trans
      (le_of_eq (hfix x))) s
  · intro ε hε
    obtain ⟨f, hgen, hf⟩ := theorem4d_core P π ustar hu (ε * (1 - P.β)) (by positivity)
    exact ⟨f, hgen, part3 ε hε f (fun s => by rw [← hfix s]; exact hf s)⟩


lemma b7_Ta_equiv (P : Problem S A) (s : S) (a b : A) (h : ActEquiv P s a b) (u : S → ℝ) :
    Ta P a u s = Ta P b u s := by
  unfold Ta
  rw [h.2]
  congr 1; funext s'; rw [h.1 s']

lemma b7_Ta_bound (P : Problem S A) (u : S → ℝ) (Cr Cu : ℝ) (hr : ∀ x, |P.r x| ≤ Cr)
    (hu : ∀ s, |u s| ≤ Cu) (a : A) (s : S) : |Ta P a u s| ≤ Cr + P.β * Cu :=
  t4_T_bound P ⟨fun _ => a, measurable_const⟩ u Cr Cu hr hu s

lemma b7_U_bdd (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u) (s : S) :
    BddAbove (Set.range fun n => T P (π n) u s) := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  exact ⟨Cr + P.β * Cu, by
    rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (t4_T_bound P (π n) u Cr Cu hr hCu s)⟩

lemma b7_Ta_le_U (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (u : S → ℝ) (hu : IsBM u) (a : A) (s : S) : Ta P a u s ≤ U P π u s := by
  obtain ⟨n, hn⟩ := hπ s a
  rw [← b7_Ta_equiv P s _ _ hn u]
  exact le_ciSup (b7_U_bdd P π u hu s) n

lemma b7_opt (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (v : S → ℝ) (hv : IsBM v) (hfix : ∀ s, U P π v s = v s) :
    (∀ π' : Plan (S := S) (A := A), ∀ s, I P π' s ≤ v s) ∧ (∀ s, v s = optReturn P s) := by
  have hup : ∀ π' : Plan (S := S) (A := A), ∀ s, I P π' s ≤ v s :=
    theorem6d_core P v hv (fun a s => (b7_Ta_le_U P π hπ v hv a s).trans (le_of_eq (hfix s)))
  refine ⟨hup, fun s => ?_⟩
  haveI : Nonempty (Plan (S := S) (A := A)) :=
    ⟨(stationary (⟨fun _ => Classical.arbitrary A, measurable_const⟩ : {g : S → A // Measurable g})).toPlan⟩
  have hbdd : BddAbove (Set.range fun π' : Plan (S := S) (A := A) => I P π' s) :=
    ⟨v s, by rintro _ ⟨π', rfl⟩; exact hup π' s⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨f, -, hf⟩ := (theorem6a_core P π v hv hfix).2.1 ε hε
    have := hf s
    have h2 : I P (stationary f).toPlan s ≤ optReturn P s := le_ciSup hbdd _
    linarith
  · exact ciSup_le (fun π' => hup π' s)

lemma b7_U_eq (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (u : S → ℝ) (hu : IsBM u) (s : S) : U P π u s = ⨆ a : A, Ta P a u s := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hbA : BddAbove (Set.range fun a : A => Ta P a u s) :=
    ⟨Cr + P.β * Cu, by rintro _ ⟨a, rfl⟩; exact (le_abs_self _).trans (b7_Ta_bound P u Cr Cu hr hCu a s)⟩
  apply le_antisymm
  · exact ciSup_le (fun n => le_ciSup (f := fun a : A => Ta P a u s) hbA ((π n).1 s))
  · exact ciSup_le (fun a => b7_Ta_le_U P π hπ u hu a s)

theorem theorem7a_core
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssCountable P π)
    (ustar : S → ℝ) (hu : IsBM ustar)
    (hfix : ∀ s, U P π ustar s = ustar s) :
    (∀ s, ustar s = optReturn P s) ∧
    (∀ u, IsBM u → ∀ s, U P π u s = ⨆ a : A, Ta P a u s) ∧
    (∀ v, IsBM v → (∀ s, v s = ⨆ a : A, Ta P a v s) → v = ustar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ f : {g : S → A // Measurable g},
      IsEOptimal P ε (stationary f).toPlan) := by
  obtain ⟨hup, hopt⟩ := b7_opt P π hπ ustar hu hfix
  refine ⟨hopt, fun u hu' s => b7_U_eq P π hπ u hu' s, ?_, ?_⟩
  · intro v hv hvf
    have hvfix : ∀ s, U P π v s = v s := fun s => by rw [b7_U_eq P π hπ v hv s, hvf s]
    have := (b7_opt P π hπ v hv hvfix).2
    funext s
    rw [this s, hopt s]
  · intro ε hε
    obtain ⟨f, -, hf⟩ := (theorem6a_core P π ustar hu hfix).2.1 ε hε
    exact ⟨f, fun π' s => by have := hf s; have := hup π' s; linarith⟩

lemma b7_U_BM (P : Problem S A) (π : MarkovPlan S A) (u : S → ℝ) (hu : IsBM u) : IsBM (U P π u) := by
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  refine ⟨Measurable.iSup (fun n => t4_T_measurable P (π n) u hu), Cr + P.β * Cu, fun s => ?_⟩
  rw [abs_le]
  constructor
  · have h0 := le_ciSup (b7_U_bdd P π u hu s) 0
    have := (abs_le.mp (t4_T_bound P (π 0) u Cr Cu hr hCu s)).1
    unfold U; linarith
  · exact ciSup_le (fun n => (le_abs_self _).trans (t4_T_bound P (π n) u Cr Cu hr hCu s))

lemma b7_T_mono (P : Problem S A) (f : {g : S → A // Measurable g}) (u v : S → ℝ)
    (hu : IsBM u) (hv : IsBM v) (h : ∀ s, u s ≤ v s) (s : S) : T P f u s ≤ T P f v s := by
  haveI := P.q_markov
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  obtain ⟨Cv, hCv⟩ := hv.2
  have hβ := P.β_nonneg
  have hrm : Measurable (fun y : S => P.r (s, f.1 s, y)) := P.r_measurable.comp (by fun_prop)
  unfold T
  apply integral_mono
  · exact (d6_bdd_int _ _ hrm Cr (fun y => hr _)).add
      ((d6_bdd_int _ _ hu.1 Cu hCu).const_mul _)
  · exact (d6_bdd_int _ _ hrm Cr (fun y => hr _)).add
      ((d6_bdd_int _ _ hv.1 Cv hCv).const_mul _)
  · intro y
    have := mul_le_mul_of_nonneg_left (h y) hβ
    simp only; linarith

lemma b7_T_shift (P : Problem S A) (f : {g : S → A // Measurable g}) (u : S → ℝ)
    (hu : IsBM u) (c : ℝ) (s : S) : T P f (fun t => u t + c) s = T P f u s + P.β * c := by
  haveI := P.q_markov
  obtain ⟨Cr, hr⟩ := P.r_bounded
  obtain ⟨Cu, hCu⟩ := hu.2
  have hrm : Measurable (fun y : S => P.r (s, f.1 s, y)) := P.r_measurable.comp (by fun_prop)
  have i1 : Integrable (fun y => P.r (s, f.1 s, y) + P.β * u y) (P.q (s, f.1 s)) :=
    (d6_bdd_int _ _ hrm Cr (fun y => hr _)).add ((d6_bdd_int _ _ hu.1 Cu hCu).const_mul _)
  unfold T
  have e : (fun y => P.r (s, f.1 s, y) + P.β * (u y + c)) =
      (fun y => (P.r (s, f.1 s, y) + P.β * u y) + P.β * c) := by funext y; ring
  rw [e, integral_add i1 (integrable_const _), integral_const]
  simp

theorem theorem7b_core
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssFinite P π) :
    ∃ f : {g : S → A // Measurable g},
      IsOptimal P (stationary f).toPlan := by
  obtain ⟨pieces, -, -, hcov, hpc⟩ := hπ
  have hmem : ∀ s, ∃ n, s ∈ pieces n := fun s => by
    have : s ∈ ⋃ n, pieces n := by rw [hcov]; trivial
    exact Set.mem_iUnion.mp this
  have hEC : EssCountable P π := by
    intro s a
    obtain ⟨n, hn⟩ := hmem s
    obtain ⟨i, -, hi⟩ := hpc n s hn a
    exact ⟨i, hi⟩
  -- fixed point of U
  obtain ⟨-, ustar, hu, hfix, -, -⟩ := theorem5_core P.β P.β_nonneg P.β_lt_one (U P π)
    (fun u hu => b7_U_BM P π u hu)
    (fun u v hu hv h s => ciSup_mono (b7_U_bdd P π v hv s) (fun n => b7_T_mono P (π n) u v hu hv h s))
    (fun u hu c s => by
      unfold U
      simp_rw [b7_T_shift P _ u hu c s]
      exact (ciSup_add (b7_U_bdd P π u hu s) _).symm)
  -- attained maximum
  have hatt : ∀ s, ∃ i, T P (π i) ustar s = ustar s := by
    intro s
    obtain ⟨n, hn⟩ := hmem s
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image (Finset.range (n+1))
      (fun i => T P (π i) ustar s) ⟨0, by simp⟩
    refine ⟨i0, le_antisymm ?_ ?_⟩
    · rw [← hfix s]; exact le_ciSup (b7_U_bdd P π ustar hu s) i0
    · rw [← hfix s]
      apply ciSup_le
      intro j
      obtain ⟨i, hi, hij⟩ := hpc n s hn ((π j).1 s)
      have e : T P (π j) ustar s = T P (π i) ustar s := by
        show Ta P ((π j).1 s) ustar s = Ta P ((π i).1 s) ustar s
        rw [b7_Ta_equiv P s _ _ hij ustar]
      rw [e]
      exact hi0 i (Finset.mem_range.mpr (by omega))
  classical
  have hset : ∀ n, MeasurableSet {s | T P (π n) ustar s = ustar s} := fun n =>
    measurableSet_eq_fun (t4_T_measurable P (π n) ustar hu) hu.1
  have hfm : Measurable (fun s => (π (Nat.find (hatt s))).1 s) :=
    Measurable.find (f := fun n s => (π n).1 s) (p := fun n s => T P (π n) ustar s = ustar s)
      (fun n => (π n).2) hset hatt
  let f : {g : S → A // Measurable g} := ⟨fun s => (π (Nat.find (hatt s))).1 s, hfm⟩
  have hTf : ∀ s, T P f ustar s = ustar s := fun s => Nat.find_spec (hatt s)
  refine ⟨f, fun π' s => ?_⟩
  have h1 := (b7_opt P π hEC ustar hu hfix).1 π' s
  have h2 := a6_lower P (stationary f) ustar hu 0 le_rfl (fun n x => by
    rw [sub_zero]; exact le_of_eq (hTf x).symm) s
  rw [zero_div, sub_zero] at h2
  linarith

end DiscountedDP.Stationary

open DiscountedDP.Stationary


theorem solution
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (π : MarkovPlan S A) (hπ : EssFinite P π) :
    ∃ f : {g : S → A // Measurable g},
      IsOptimal P (stationary f).toPlan := by
  exact theorem7b_core P π hπ
