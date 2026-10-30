-- Prove2me | solution 1 for FragileBandit.CauchyTail.change_of_measure
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T12:38:55.593478+00:00
-- url     : https://prove2.me/submissions/2481eb5a-3564-4a8a-aa84-24e14f7e1225

import Mathlib
import Definitions.Def_FragileBandit_CauchyTail_Setting

open MeasureTheory ProbabilityTheory Filter BanditAlgorithm FragileBandit.CauchyTail
open scoped ENNReal Topology

namespace CTCoMAux

variable {K : ℕ}

/-- The one-round likelihood ratio factor. -/
noncomputable def ell (ν ν' : StochasticBandit K) (S : Finset (Fin K)) (p : Fin K × ℝ) : ℝ≥0∞ :=
  if p.1 ∈ S then (ν.P p.1).rnDeriv (ν'.P p.1) p.2 else 1

/-- The likelihood ratio of a history. -/
noncomputable def lr (ν ν' : StochasticBandit K) (S : Finset (Fin K)) {T : ℕ}
    (h : BanditHistory K T) : ℝ≥0∞ :=
  ∏ t : Fin T, ell ν ν' S (h t)

lemma measurable_ell (ν ν' : StochasticBandit K) (S : Finset (Fin K)) :
    Measurable (ell ν ν' S) := by
  apply measurable_from_prod_countable_right
  intro a
  unfold ell
  by_cases ha : a ∈ S
  · simp only [ha, if_true]; exact Measure.measurable_rnDeriv _ _
  · simp only [ha, if_false]; exact measurable_const

lemma measurable_lr (ν ν' : StochasticBandit K) (S : Finset (Fin K)) (T : ℕ) :
    Measurable (fun h : BanditHistory K T => lr ν ν' S h) := by
  unfold lr
  exact Finset.measurable_prod _ (fun t _ => (measurable_ell ν ν' S).comp (measurable_pi_apply t))

lemma lr_snoc (ν ν' : StochasticBandit K) (S : Finset (Fin K)) {T : ℕ}
    (h : BanditHistory K T) (p : Fin K × ℝ) :
    lr ν ν' S (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) = lr ν ν' S h * ell ν ν' S p := by
  unfold lr
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- Integral against the step: unfold the step kernel. -/
lemma lintegral_step (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    (h : BanditHistory K T) {F : Fin K × ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ p, F p ∂(banditStepKernel ν π T h) = ∫⁻ a, ∫⁻ x, F (a, x) ∂(ν.P a) ∂(π.select T h) := by
  unfold banditStepKernel
  rw [Kernel.lintegral_compProd _ _ _ hF]
  rfl

/-- One-step inequality for the inner integral. -/
lemma inner_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (S : Finset (Fin K))
    (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (T : ℕ) (h : BanditHistory K T)
    {g : Fin K × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ell ν ν' S p * g p ∂(banditStepKernel ν' π T h) ≤
      ∫⁻ p, g p ∂(banditStepKernel ν π T h) := by
  rw [lintegral_step ν' π T h (F := fun p => ell ν ν' S p * g p) ((measurable_ell ν ν' S).mul hg),
    lintegral_step ν π T h hg]
  apply lintegral_mono
  intro a
  by_cases ha : a ∈ S
  · simp only [ell, ha, if_true]
    have hga : Measurable (fun x => g (a, x)) := hg.comp measurable_prodMk_left
    calc ∫⁻ x, (ν.P a).rnDeriv (ν'.P a) x * g (a, x) ∂(ν'.P a)
        = ∫⁻ x, g (a, x) ∂((ν'.P a).withDensity ((ν.P a).rnDeriv (ν'.P a))) :=
          (lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hga).symm
      _ ≤ ∫⁻ x, g (a, x) ∂(ν.P a) := lintegral_mono' (Measure.withDensity_rnDeriv_le _ _) le_rfl
  · simp only [ell, ha, if_false, one_mul]
    rw [hS a ha]

lemma inner_eq (ν ν' : StochasticBandit K) (π : BanditPolicy K) (S : Finset (Fin K))
    (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (hac : ∀ j ∈ S, ν.P j ≪ ν'.P j) (T : ℕ)
    (h : BanditHistory K T) {g : Fin K × ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, ell ν ν' S p * g p ∂(banditStepKernel ν' π T h) =
      ∫⁻ p, g p ∂(banditStepKernel ν π T h) := by
  rw [lintegral_step ν' π T h (F := fun p => ell ν ν' S p * g p) ((measurable_ell ν ν' S).mul hg),
    lintegral_step ν π T h hg]
  apply lintegral_congr
  intro a
  by_cases ha : a ∈ S
  · simp only [ell, ha, if_true]
    have hga : Measurable (fun x => g (a, x)) := hg.comp measurable_prodMk_left
    calc ∫⁻ x, (ν.P a).rnDeriv (ν'.P a) x * g (a, x) ∂(ν'.P a)
        = ∫⁻ x, g (a, x) ∂((ν'.P a).withDensity ((ν.P a).rnDeriv (ν'.P a))) :=
          (lintegral_withDensity_eq_lintegral_mul _ (Measure.measurable_rnDeriv _ _) hga).symm
      _ = ∫⁻ x, g (a, x) ∂(ν.P a) := by rw [Measure.withDensity_rnDeriv_eq _ _ (hac a ha)]
  · simp only [ell, ha, if_false, one_mul]
    rw [hS a ha]

/-- Unfold the integral over `banditMeasure (T+1)`. -/
lemma lintegral_succ (ν : StochasticBandit K) (π : BanditPolicy K) (T : ℕ)
    {g : BanditHistory K (T + 1) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ h, g h ∂(banditMeasure ν π (T + 1)) =
      ∫⁻ h, ∫⁻ p, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) ∂(banditStepKernel ν π T h)
        ∂(banditMeasure ν π T) := by
  rw [banditMeasure.eq_2, lintegral_map hg measurable_banditHistorySnoc,
    Measure.lintegral_compProd (f := fun a => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) a.1 a.2))
      (hg.comp measurable_banditHistorySnoc)]

lemma main_le (ν ν' : StochasticBandit K) (π : BanditPolicy K) (S : Finset (Fin K))
    (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (T : ℕ) :
    ∀ g : BanditHistory K T → ℝ≥0∞, Measurable g →
      ∫⁻ h, lr ν ν' S h * g h ∂(banditMeasure ν' π T) ≤ ∫⁻ h, g h ∂(banditMeasure ν π T) := by
  induction T with
  | zero =>
    intro g hg
    apply le_of_eq
    simp only [banditMeasure.eq_1, lr, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  | succ T ih =>
    intro g hg
    have hsn := measurable_banditHistorySnoc (k := K) (n := T)
    have hF : Measurable (fun h : BanditHistory K (T + 1) => lr ν ν' S h * g h) :=
      (measurable_lr ν ν' S (T + 1)).mul hg
    rw [lintegral_succ ν' π T hF, lintegral_succ ν π T hg]
    simp_rw [lr_snoc]
    set G : BanditHistory K T → ℝ≥0∞ := fun h =>
      ∫⁻ p, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) ∂(banditStepKernel ν π T h) with hG
    have hGm : Measurable G := (hg.comp hsn).lintegral_kernel_prod_right'
    calc ∫⁻ h, ∫⁻ p, lr ν ν' S h * ell ν ν' S p * g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p)
          ∂(banditStepKernel ν' π T h) ∂(banditMeasure ν' π T)
        = ∫⁻ h, lr ν ν' S h * ∫⁻ p, ell ν ν' S p * g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p)
          ∂(banditStepKernel ν' π T h) ∂(banditMeasure ν' π T) := by
          apply lintegral_congr; intro h
          simp_rw [mul_assoc]
          rw [lintegral_const_mul]
          exact (measurable_ell ν ν' S).mul (hg.comp (hsn.comp measurable_prodMk_left))
      _ ≤ ∫⁻ h, lr ν ν' S h * G h ∂(banditMeasure ν' π T) := by
          apply lintegral_mono; intro h
          exact mul_le_mul_right (inner_le ν ν' π S hS T h
            (g := fun p => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p))
            (hg.comp (hsn.comp measurable_prodMk_left))) _
      _ ≤ ∫⁻ h, G h ∂(banditMeasure ν π T) := ih G hGm

lemma main_eq (ν ν' : StochasticBandit K) (π : BanditPolicy K) (S : Finset (Fin K))
    (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (hac : ∀ j ∈ S, ν.P j ≪ ν'.P j) (T : ℕ) :
    ∀ g : BanditHistory K T → ℝ≥0∞, Measurable g →
      ∫⁻ h, lr ν ν' S h * g h ∂(banditMeasure ν' π T) = ∫⁻ h, g h ∂(banditMeasure ν π T) := by
  induction T with
  | zero =>
    intro g hg
    simp only [banditMeasure.eq_1, lr, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  | succ T ih =>
    intro g hg
    have hsn := measurable_banditHistorySnoc (k := K) (n := T)
    have hF : Measurable (fun h : BanditHistory K (T + 1) => lr ν ν' S h * g h) :=
      (measurable_lr ν ν' S (T + 1)).mul hg
    rw [lintegral_succ ν' π T hF, lintegral_succ ν π T hg]
    simp_rw [lr_snoc]
    set G : BanditHistory K T → ℝ≥0∞ := fun h =>
      ∫⁻ p, g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p) ∂(banditStepKernel ν π T h) with hG
    have hGm : Measurable G := (hg.comp hsn).lintegral_kernel_prod_right'
    calc ∫⁻ h, ∫⁻ p, lr ν ν' S h * ell ν ν' S p * g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p)
          ∂(banditStepKernel ν' π T h) ∂(banditMeasure ν' π T)
        = ∫⁻ h, lr ν ν' S h * ∫⁻ p, ell ν ν' S p * g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p)
          ∂(banditStepKernel ν' π T h) ∂(banditMeasure ν' π T) := by
          apply lintegral_congr; intro h
          simp_rw [mul_assoc]
          rw [lintegral_const_mul]
          exact (measurable_ell ν ν' S).mul (hg.comp (hsn.comp measurable_prodMk_left))
      _ = ∫⁻ h, lr ν ν' S h * G h ∂(banditMeasure ν' π T) := by
          apply lintegral_congr; intro h
          rw [inner_eq ν ν' π S hS hac T h (g := fun p => g (Fin.snoc (α := fun _ ↦ Fin K × ℝ) h p))
            (hg.comp (hsn.comp measurable_prodMk_left))]
      _ = ∫⁻ h, G h ∂(banditMeasure ν π T) := ih G hGm

end CTCoMAux

open CTCoMAux in
theorem solution {K : ℕ} (π : BanditPolicy K) (ν ν' : StochasticBandit K)
    (S : Finset (Fin K)) (hS : ∀ j, j ∉ S → ν.P j = ν'.P j) (T : ℕ)
    (E : Set (BanditHistory K T)) (hE : MeasurableSet E) :
    (∫⁻ h in E, ∏ t : Fin T,
        (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
        ∂(banditMeasure ν' π T)) ≤ banditMeasure ν π T E ∧
    ((∀ j ∈ S, ν.P j ≪ ν'.P j) →
      banditMeasure ν π T E =
        ∫⁻ h in E, ∏ t : Fin T,
          (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
          ∂(banditMeasure ν' π T)) := by
  have hconv : (∫⁻ h in E, ∏ t : Fin T,
        (if (h t).1 ∈ S then (ν.P (h t).1).rnDeriv (ν'.P (h t).1) (h t).2 else 1)
        ∂(banditMeasure ν' π T)) =
      ∫⁻ h, lr ν ν' S h * E.indicator 1 h ∂(banditMeasure ν' π T) := by
    rw [← lintegral_indicator hE]
    apply lintegral_congr; intro h
    by_cases hh : h ∈ E
    · simp [Set.indicator_of_mem hh, lr, ell]
    · simp [Set.indicator_of_notMem hh]
  have hind : Measurable (E.indicator (1 : BanditHistory K T → ℝ≥0∞)) :=
    measurable_one.indicator hE
  have hPE : banditMeasure ν π T E = ∫⁻ h, E.indicator 1 h ∂(banditMeasure ν π T) := by
    rw [lintegral_indicator_one hE]
  refine ⟨?_, fun hac => ?_⟩
  · rw [hconv, hPE]; exact main_le ν ν' π S hS T _ hind
  · rw [hconv, hPE]; exact (main_eq ν ν' π S hS hac T _ hind).symm
