-- Prove2me | solution 1 for AvramDividend.Classical.chat06_ae_repair_preserves_full_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:04:01.466352+00:00
-- url     : https://prove2.me/submissions/d401554b-423b-42e4-bfff-119d63e0fb6f

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.HasLaw

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

namespace AvramChat06

/-- Repairing all exceptional compound-Poisson paths using a
single probability-one global guard does not change the
independence of entire vector-valued past and future laws.
This is stronger than coordinatewise independence. -/
theorem ae_path_repair_preserves_full_independence
    {Ω E A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω}
    (driver : Ω → E) (G : Set E)
    (hG : ∀ᵐ ω ∂P, driver ω ∈ G)
    (rawPast fixedPast : Ω → A)
    (rawFuture fixedFuture : Ω → B)
    (hPast : ∀ ω, driver ω ∈ G →
      fixedPast ω = rawPast ω)
    (hFuture : ∀ ω, driver ω ∈ G →
      fixedFuture ω = rawFuture ω)
    (hI : IndepFun rawPast rawFuture P) :
    IndepFun fixedPast fixedFuture P := by
  have hp : rawPast =ᵐ[P] fixedPast := by
    filter_upwards [hG] with ω hg
    exact (hPast ω hg).symm
  have hf : rawFuture =ᵐ[P] fixedFuture := by
    filter_upwards [hG] with ω hg
    exact (hFuture ω hg).symm
  exact hI.congr hp hf

/-- The same probability-one repair preserves the entire marginal
law of a vector-valued random variable. -/
theorem ae_path_repair_preserves_joint_law
    {Ω E A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A]
    {P : Measure Ω}
    (driver : Ω → E) (G : Set E)
    (hG : ∀ᵐ ω ∂P, driver ω ∈ G)
    (raw fixed : Ω → A) (μ : Measure A)
    (hRepair : ∀ ω, driver ω ∈ G → fixed ω = raw ω)
    (hLaw : HasLaw raw μ P) :
    HasLaw fixed μ P := by
  have heq : fixed =ᵐ[P] raw := by
    filter_upwards [hG] with ω hg
    exact hRepair ω hg
  exact hLaw.congr heq

end AvramChat06

open AvramChat06

theorem solution
    {Ω E A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω}
    (driver : Ω → E) (G : Set E)
    (hG : ∀ᵐ ω ∂P, driver ω ∈ G)
    (rawPast fixedPast : Ω → A)
    (rawFuture fixedFuture : Ω → B)
    (hPast : ∀ ω, driver ω ∈ G →
      fixedPast ω = rawPast ω)
    (hFuture : ∀ ω, driver ω ∈ G →
      fixedFuture ω = rawFuture ω)
    (hI : IndepFun rawPast rawFuture P) :
    IndepFun fixedPast fixedFuture P := by
  exact ae_path_repair_preserves_full_independence
    driver G hG rawPast fixedPast rawFuture fixedFuture
    hPast hFuture hI
