-- Prove2me | solution 1 for ConnesGreen.canonical_nested_diagonal_actual_tail_marker_recovery
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:57:06.648486+00:00
-- url     : https://prove2.me/submissions/ae19e36b-ddd4-423e-824d-27663b4cabfe

import Theorems.Thm_ConnesGreen_canonical_uniform_band_actual_tail_marker_recovery
import Theorems.Thm_WeilDefect_MarkerStability_tail_marker_stability
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma ConnesGreen.uniform_band_fixed_selected_enlargement
    (T : ℝ) (hT : 0 < T) (S U : Finset CriticalZeros)
    (η μ₀ α : ℝ) (hη : 0 < η) (hμ₀ : 0 < μ₀) (hα : 0 < α) (hα1 : α < 1) :
    ∃ F : Finset CriticalZeros, U ⊆ F ∧ S ⊆ F ∧
      (∀ τ ∈ F, reflectedZero τ ∈ F) ∧
      ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < η ∧
          (∀ ν : ℝ, μ₀ ≤ ν →
            ‖canonicalTailCovariance t ht F‖ ≤ α * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S)‖ ≤ α) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < η) := by
  obtain ⟨F, hUF, hclosed, hrec⟩ :=
    canonical_uniform_band_actual_tail_marker_recovery T hT (U ∪ S) η μ₀ α hη hμ₀ hα hα1
  refine ⟨F, Finset.subset_union_left.trans hUF, Finset.subset_union_right.trans hUF, hclosed, ?_⟩
  intro t ht htT
  obtain ⟨Ptail, hcols, hsmall, hband, hactual, _⟩ := hrec t ht htT
  refine ⟨Ptail, hcols, hsmall, ?_, hactual⟩
  intro ν hν
  have hb := (hband ν hν).1
  have hL : 0 ≤ canonicalPositiveCovariance t ht :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalPositiveSynthesis t ht))
  have hR : 0 ≤ canonicalTailCovariance t ht F :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
      (ContinuousLinearMap.isPositive_self_comp_adjoint (canonicalBackgroundSynthesis t ht F))
  exact ⟨hb, tail_marker_stability _ _ (canonicalSelectedSynthesis t ht S)
    hL hR ν α (hμ₀.trans_le hν) hα.le hα1 hb⟩

lemma ConnesGreen.nested_finite_choice {ι : Type*} [DecidableEq ι]
    (Q : ℕ → Finset ι → Prop)
    (h : ∀ n U, ∃ F : Finset ι, U ⊆ F ∧ Q n F) :
    ∃ F : ℕ → Finset ι, Monotone F ∧ ∀ n, Q n (F n) := by
  let pick := fun n U => Classical.choose (h n U)
  have spec : ∀ n U, U ⊆ pick n U ∧ Q n (pick n U) :=
    fun n U => Classical.choose_spec (h n U)
  let F : ℕ → Finset ι := fun n => Nat.rec (pick 0 ∅) (fun k prev => pick (k + 1) prev) n
  have hsucc : ∀ n, F (n + 1) = pick (n + 1) (F n) := fun _ => rfl
  refine ⟨F, monotone_nat_of_le_succ (fun n => ?_), ?_⟩
  · rw [hsucc]
    exact (spec (n + 1) (F n)).1
  · intro n
    cases n with
    | zero => exact (spec 0 ∅).2
    | succ n => rw [hsucc]; exact (spec (n + 1) (F n)).2
theorem solution
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) := by
  let Q : ℕ → Finset CriticalZeros → Prop := fun n F =>
    S ⊆ F ∧ K n ⊆ F ∧ (∀ τ ∈ F, reflectedZero τ ∈ F) ∧
    ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ F}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht F‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht F‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht F)
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ F then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)
  have hQ : ∀ n U, ∃ F : Finset CriticalZeros, U ⊆ F ∧ Q n F := by
    intro n U
    obtain ⟨F, hUF, hSF, hclosed, hrec⟩ :=
      uniform_band_fixed_selected_enlargement T hT S (U ∪ K n) (ε n) (μ n) (ε n)
        (hε n) (hμ n) (hε n) (hε1 n)
    exact ⟨F, Finset.subset_union_left.trans hUF, hSF,
      Finset.subset_union_right.trans hUF, hclosed, hrec⟩
  obtain ⟨F, hmono, hF⟩ := nested_finite_choice Q hQ
  refine ⟨F, hmono, (fun n => ⟨(hF n).1, (hF n).2.1, (hF n).2.2.1⟩),
    (fun n => (hF n).2.2.2), ?_⟩
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hεlim).2 δ hδ)
  refine ⟨N, ?_⟩
  intro n hn t ht htT
  have heδ : ε n < δ := hN n hn
  obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := (hF n).2.2.2 t ht htT
  have htail : ‖canonicalTailCovariance t ht (F n)‖ < ε n :=
    (le_add_of_nonneg_left (norm_nonneg (Ptail ∘L Ptail.adjoint))).trans_lt hsmall
  refine ⟨htail.trans heδ, ?_, ?_⟩
  · intro ν hν
    exact (hband ν hν).2.2.2.trans_lt heδ
  · intro g hg hx
    exact ((hactual g hg hx).2).trans heδ
