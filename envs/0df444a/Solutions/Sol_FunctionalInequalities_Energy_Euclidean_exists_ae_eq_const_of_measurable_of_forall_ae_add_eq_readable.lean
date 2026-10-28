-- Prove2me | solution 1 for FunctionalInequalities.Energy.Euclidean.exists_ae_eq_const_of_measurable_of_forall_ae_add_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:42:19.51533+00:00
-- url     : https://prove2.me/submissions/a62ff1d6-16ab-4909-9e6a-8f62922db368

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_ZeroGradient

noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
/-- A measurable function invariant under every translation up to null sets is almost everywhere
constant. -/
theorem solution {g : V → ℝ} (hg : Measurable g)
    (htr : ∀ v : V, ∀ᵐ x ∂m, g (x + v) = g x) :
    ∃ c : ℝ, ∀ᵐ x ∂m, g x = c := by
  have hmeas :
      MeasurableSet {q : V × V | g (q.2 + q.1) = g q.2} := by
    exact measurableSet_eq_fun
      (hg.comp (measurable_snd.add measurable_fst))
      (hg.comp measurable_snd)

  have hprod : ∀ᵐ v ∂m, ∀ᵐ y ∂m, g (y + v) = g y := by
    filter_upwards [] with v
    exact htr v

  have hcomm : ∀ᵐ y ∂m, ∀ᵐ v ∂m, g (y + v) = g y :=
    (Measure.ae_ae_comm (μ := m) (ν := m) hmeas).mp hprod

  have hm0 : m ≠ 0 := NeZero.ne m
  have hne : (ae m).NeBot := ae_neBot.2 hm0
  obtain ⟨y₀, hy₀⟩ := Filter.Eventually.exists hcomm

  have hpull : ∀ᵐ z ∂m, g (y₀ + (z - y₀)) = g y₀ :=
    (measurePreserving_sub_right m y₀).quasiMeasurePreserving.ae hy₀

  refine ⟨g y₀, ?_⟩
  filter_upwards [hpull] with z hz
  have hEq : y₀ + (z - y₀) = z := by
    abel
  rw [hEq] at hz
  exact hz
