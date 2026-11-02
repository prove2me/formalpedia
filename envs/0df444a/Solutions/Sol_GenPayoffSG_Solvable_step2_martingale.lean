-- Prove2me | solution 1 for GenPayoffSG.Solvable.step2_martingale
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:34:49.661897+00:00
-- url     : https://prove2.me/submissions/b97d3d00-324d-4640-9fd5-06ae805b2a77

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_Game

open MeasureTheory ProbabilityTheory Filter Topology GenPayoffSG.Solvable

set_option linter.unusedSectionVars false

namespace GPSGStep2

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

lemma measurable_hist (n : ℕ) {β : Type*} [MeasurableSpace β] (g : Hist I S A n → β) :
    Measurable g := measurable_of_countable g

lemma stronglyMeasurable_piLE (n : ℕ) (g : Hist I S A n → ℝ) :
    StronglyMeasurable[Filtration.piLE n] (fun r : Run I S A => g (Preorder.frestrictLe n r)) := by
  apply Measurable.stronglyMeasurable
  rw [Filtration.piLE_eq_comap_frestrictLe]
  exact (measurable_hist n g).comp (comap_measurable _)

lemma pi_le_iSup_piLE :
    (MeasurableSpace.pi : MeasurableSpace (Run I S A)) ≤ ⨆ n, Filtration.piLE (X := Coord I S A) n := by
  refine iSup_le fun a => ?_
  refine le_iSup_of_le a ?_
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have : (fun b : Run I S A => b a) =
      (fun x : (∀ k : Finset.Iic a, Coord I S A k) => x ⟨a, Finset.mem_Iic.2 le_rfl⟩) ∘
        Preorder.frestrictLe a := by
    funext b; rfl
  rw [this, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono
    (measurable_pi_apply (⟨a, Finset.mem_Iic.2 le_rfl⟩ : Finset.Iic a)).comap_le

end GPSGStep2

open GPSGStep2

theorem solution {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
  (G : Game I S A) (σ : Profile G) (s : S) (i : I) :
    Martingale (fun n r => payoff G σ n (Preorder.frestrictLe n r) i) Filtration.piLE
        (playMeasure G σ 0 (initHist s)) ∧
      ∀ᵐ r ∂(playMeasure G σ 0 (initHist s)),
        Tendsto (fun n => payoff G σ n (Preorder.frestrictLe n r) i) atTop (𝓝 (G.f i r)) := by
  set μ := playMeasure G σ 0 (initHist s) with hμ
  haveI : IsProbabilityMeasure μ := by rw [hμ]; unfold playMeasure; infer_instance
  have hfm : Measurable (G.f i) := G.f_meas i
  obtain ⟨C, hC⟩ := G.f_bdd
  have hint : Integrable (G.f i) μ :=
    Integrable.of_bound hfm.aestronglyMeasurable C (ae_of_all _ fun r => by
      simpa [Real.norm_eq_abs] using hC i r)
  have hce : ∀ n, μ[G.f i | Filtration.piLE n] =ᵐ[μ]
      fun r => payoff G σ n (Preorder.frestrictLe n r) i := by
    intro n
    exact Kernel.condExp_traj (κ := stepKernel G σ) (Nat.zero_le n) hint
  refine ⟨⟨fun n => stronglyMeasurable_piLE n (fun h => payoff G σ n h i), fun m n hmn => ?_⟩, ?_⟩
  · refine (condExp_congr_ae (hce n).symm).trans ?_
    refine (condExp_condExp_of_le (Filtration.piLE.mono hmn) (Filtration.piLE.le n)).trans ?_
    exact hce m
  · have hmeas : StronglyMeasurable[⨆ n, Filtration.piLE (X := Coord I S A) n] (G.f i) :=
      (hfm.mono pi_le_iSup_piLE le_rfl).stronglyMeasurable
    have ht := hint.tendsto_ae_condExp hmeas
    have hall : ∀ᵐ r ∂μ, ∀ n, μ[G.f i | Filtration.piLE n] r =
        payoff G σ n (Preorder.frestrictLe n r) i := ae_all_iff.2 hce
    filter_upwards [ht, hall] with r hr hr2
    exact hr.congr hr2
