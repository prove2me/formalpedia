-- Prove2me | solution 1 for FiniteEnergyPlane.contDiffOn_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T21:35:09.866049+00:00
-- url     : https://prove2.me/submissions/ccadae33-ffc5-43f2-b79a-d65d5a30fd22

import Mathlib



/-! Finite-order smoothness of parametric interval integrals. -/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff

theorem pfe_near {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (hO : IsOpen O)
    {F : E × ℝ → G} (hF : ContinuousOn F (O ×ˢ Set.univ)) (a b : ℝ) {x : E} (hx : x ∈ O) :
    ∃ C : ℝ, ∃ ε > 0, ∀ y ∈ ball x ε, y ∈ O ∧ ∀ t ∈ Set.uIcc a b, ‖F (y, t)‖ ≤ C := by
  have hOo : IsOpen (O ×ˢ (Set.univ : Set ℝ)) := hO.prod isOpen_univ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ t ∈ Set.uIcc a b, ‖F (x, t)‖ ≤ C := by
    have : ContinuousOn (fun t => F (x, t)) (Set.uIcc a b) :=
      hF.comp (f := fun t : ℝ => (x, t)) (by fun_prop) fun t _ => ⟨hx, trivial⟩
    exact isCompact_uIcc.exists_bound_of_continuousOn this
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Set.uIcc a b, ‖F (y, t)‖ < C + 1 := by
    refine isCompact_uIcc.eventually_forall_of_forall_eventually ?_
    intro t ht
    have hat : ContinuousAt F (x, t) := hF.continuousAt (hOo.mem_nhds ⟨hx, trivial⟩)
    exact hat.norm.eventually_lt continuousAt_const (by linarith [hC t ht])
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hnear.and (hO.mem_nhds hx))
  exact ⟨C + 1, ε, hε, fun y hy => ⟨(hball y hy).2, fun t ht => ((hball y hy).1 t ht).le⟩⟩

theorem pfe_continuousOn {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (hO : IsOpen O)
    {F : E × ℝ → G} (hF : ContinuousOn F (O ×ˢ Set.univ)) (a b : ℝ) :
    ContinuousOn (fun x => ∫ t in a..b, F (x, t)) O := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨C, ε, hε, hb⟩ := pfe_near hO hF a b hx
  refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
    intervalIntegrable_const ?_
  · filter_upwards [ball_mem_nhds x hε] with y hy
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact hF.comp (f := fun t : ℝ => (y, t)) (by fun_prop) fun t _ => ⟨(hb y hy).1, trivial⟩
  · filter_upwards [ball_mem_nhds x hε] with y hy
    exact ae_of_all _ fun t ht => (hb y hy).2 t (Set.uIoc_subset_uIcc ht)
  · refine ae_of_all _ fun t _ => ?_
    have hat : ContinuousAt F (x, t) :=
      hF.continuousAt ((hO.prod isOpen_univ).mem_nhds ⟨hx, trivial⟩)
    exact hat.comp (f := fun y : E => (y, t)) (by fun_prop)

theorem pfe_hasFDerivAt {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (hO : IsOpen O)
    {F : E × ℝ → G} (hF : ContDiffOn ℝ 1 F (O ×ˢ Set.univ)) (a b : ℝ) {x : E} (hx : x ∈ O) :
    HasFDerivAt (fun x => ∫ t in a..b, F (x, t))
      (∫ t in a..b, (fderiv ℝ F (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hOo : IsOpen (O ×ˢ (Set.univ : Set ℝ)) := hO.prod isOpen_univ
  have hFc := hF.continuousOn
  have hdc : ContinuousOn (fderiv ℝ F) (O ×ˢ Set.univ) :=
    hF.continuousOn_fderiv_of_isOpen hOo le_rfl
  have hF'c : ContinuousOn (fun p : E × ℝ => (fderiv ℝ F p).comp
      (ContinuousLinearMap.inl ℝ E ℝ)) (O ×ˢ Set.univ) :=
    hdc.clm_comp continuousOn_const
  obtain ⟨C, ε, hε, hb⟩ := pfe_near hO hF'c a b hx
  refine (intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun y t => F (y, t))
    (F' := fun y t => (fderiv ℝ F (y, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
    (bound := fun _ => C) (s := ball x ε)
    (ball_mem_nhds x hε) ?_ ?_ ?_ ?_ ?_ ?_)
  · filter_upwards [ball_mem_nhds x hε] with y hy
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact hFc.comp (f := fun t : ℝ => (y, t)) (by fun_prop) fun t _ => ⟨(hb y hy).1, trivial⟩
  · refine ContinuousOn.intervalIntegrable ?_
    exact hFc.comp (f := fun t : ℝ => (x, t)) (by fun_prop) fun t _ => ⟨hx, trivial⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    exact hF'c.comp (f := fun t : ℝ => (x, t)) (by fun_prop) fun t _ => ⟨hx, trivial⟩
  · exact ae_of_all _ fun t ht y hy => (hb y hy).2 t (Set.uIoc_subset_uIcc ht)
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t ht y hy => ?_
    have h1 : HasFDerivAt F (fderiv ℝ F (y, t)) (y, t) :=
      ((hF.differentiableOn one_ne_zero).differentiableAt
        (hOo.mem_nhds ⟨(hb y hy).1, trivial⟩)).hasFDerivAt
    exact h1.comp (f := fun y : E => (y, t)) y (hasFDerivAt_prodMk_left y t)

universe w

theorem contDiffOn_intervalIntegral_aux {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) : ∀ {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (_ : IsOpen O)
    {F : E × ℝ → G} (_ : ContDiffOn ℝ l F (O ×ˢ Set.univ)) (a b : ℝ),
    ContDiffOn ℝ l (fun x => ∫ t in a..b, F (x, t)) O := by
  induction l with
  | zero =>
    intro G _ _ O hO F hF a b
    exact contDiffOn_zero.2 (pfe_continuousOn hO (contDiffOn_zero.1 hF) a b)
  | succ l ih =>
    intro G _ _ O hO F hF a b
    have hOo : IsOpen (O ×ˢ (Set.univ : Set ℝ)) := hO.prod isOpen_univ
    have hF1 : ContDiffOn ℝ 1 F (O ×ˢ Set.univ) :=
      hF.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le l))
    have hc : ((l + 1 : ℕ) : WithTop ℕ∞) = (l : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [hc] at hF ⊢
    have hd := ((contDiffOn_succ_iff_fderiv_of_isOpen hOo).1 hF).2.2
    refine (contDiffOn_succ_iff_fderiv_of_isOpen hO).2
      ⟨fun x hx => (pfe_hasFDerivAt hO hF1 a b hx).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
    have h2 := ih hO (F := fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ))
      (hd.clm_comp contDiffOn_const) a b
    exact h2.congr fun x hx => (pfe_hasFDerivAt hO hF1 a b hx).fderiv

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

universe w

theorem solution {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : ℕ) {G : Type w} [NormedAddCommGroup G] [NormedSpace ℝ G] {O : Set E} (hO : IsOpen O)
    {F : E × ℝ → G} (hF : ContDiffOn ℝ l F (O ×ˢ Set.univ)) (a b : ℝ) :
    ContDiffOn ℝ l (fun x => ∫ t in a..b, F (x, t)) O :=
  contDiffOn_intervalIntegral_aux l hO hF a b
