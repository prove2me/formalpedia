-- Prove2me | solution 1 for DiscountedDP.Stationary.theorem3c_prefix_return
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T21:08:48.965981+00:00
-- url     : https://prove2.me/submissions/ff634f9c-296f-4b2e-8492-21ac4f76cb0a

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

end DiscountedDP.Stationary

open DiscountedDP.Stationary


theorem solution
    {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
    [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]
    (P : Problem S A) (f : {g : S → A // Measurable g})
    (π : MarkovPlan S A) :
    ∀ s, T P f (I P π.toPlan) s =
      I P (MarkovPlan.cons f π).toPlan s := by
  exact theorem3c_core P f π
