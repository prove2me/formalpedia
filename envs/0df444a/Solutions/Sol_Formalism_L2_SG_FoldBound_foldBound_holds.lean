-- Prove2me | solution 1 for Formalism.L2.SG.FoldBound.foldBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:47.754798+00:00
-- url     : https://prove2.me/submissions/7724b099-f470-49fb-83ae-b423a5254713

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Theorems.Thm_Formalism_L2_SG_FoldBound_tsum_transversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.FoldBound
namespace Formalism.L2.SG.FoldBound
theorem _root_.solution (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] : FoldBound G μ := by
  intro Γ S hΓ hSΓ Ω hΩ a Ph hPh hS hbd F hF D hD x
  classical
  haveI := hΓ
  haveI : Countable Γ := by
    obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense Γ
    have hu : s = Set.univ := by
      have := hd.closure_eq
      rwa [closure_discrete] at this
    rw [hu] at hs
    exact Set.countable_univ_iff.mp hs
  haveI : Countable D := ((Set.countable_range ((↑) : Γ → G)).mono
    (show D ⊆ Set.range ((↑) : Γ → G) from fun y hy => ⟨⟨y, hD.1 hy⟩, rfl⟩)).to_subtype
  haveI : Countable S := ((Set.countable_range ((↑) : Γ → G)).mono
    (show (S : Set G) ⊆ Set.range ((↑) : Γ → G) from fun y hy => ⟨⟨y, hSΓ hy⟩, rfl⟩)).to_subtype
  set ind : G → ℝ≥0∞ := Ω.indicator (fun _ => 1) with hind
  have hindm : Measurable ind := measurable_const.indicator hΩ
  set Fd : G → G → ℝ≥0∞ := fun g y => ind (g⁻¹ * y) * ‖Ph y‖ₑ with hFd
  have hFdm : ∀ g, Measurable (Fd g) := fun g =>
    (hindm.comp (measurable_const_mul _)).mul hPh.enorm

  have step1 : ∀ g : G, ‖Ph g‖ₑ ≤ (a : ℝ≥0∞) * ∫⁻ y, Fd g y ∂μ := by
    intro g
    refine (hbd g).trans (le_of_eq ?_)
    congr 1
    have e1 : ∫⁻ y, Fd g y ∂μ = ∫⁻ ω, Fd g (g * ω) ∂μ := (lintegral_mul_left_eq_self (Fd g) g).symm
    rw [e1, ← lintegral_indicator hΩ]
    refine lintegral_congr fun ω => ?_
    by_cases hω : ω ∈ Ω <;> simp [hFd, hind, hω]
  have step2 : ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ ≤
      (a : ℝ≥0∞) * ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ := by
    rw [lintegral_tsum (fun δ => (hFdm _).aemeasurable), ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun δ => step1 _

  have step3 : ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ =
      ∫⁻ y in F, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ∂μ := by
    refine (hF.lintegral_eq_tsum'' _).trans (lintegral_tsum fun s => ?_).symm
    exact (Measurable.ennreal_tsum fun δ => (hFdm _).comp (measurable_const_mul _)).aemeasurable

  have step4 : ∀ y, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ≤
      mult Γ Ω x * ‖Ph y‖ₑ := by
    intro y
    have e : ∀ (s : S) (δ : D), Fd ((δ : G) * x) ((s : G) * y) =
        ind (x⁻¹ * (((δ : G)⁻¹ * (s : G)) * y)) * ‖Ph y‖ₑ := by
      intro s δ
      simp only [hFd, hS s s.2 y, mul_inv_rev, mul_assoc]
    simp_rw [e, ENNReal.tsum_mul_right]
    have ht := tsum_transversal Γ S hSΓ D hD (fun g => ind (x⁻¹ * (g * y)))
    beta_reduce at ht
    rw [ENNReal.tsum_comm, ht]
    gcongr
    have hsum : ∑' γ : Γ, ind (x⁻¹ * ((γ : G) * y)) =
        ((({γ : Γ | x⁻¹ * ((γ : G) * y) ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞) := by
      rw [← ENNReal.tsum_set_one, tsum_subtype _ (fun _ : Γ => (1 : ℝ≥0∞))]
      congr 1
    rw [hsum]
    exact le_iSup (fun y' => ((({γ : Γ | x⁻¹ * ((γ : G) * y') ∈ Ω} : Set Γ).encard : ℕ∞) : ℝ≥0∞)) y
  calc ∑' δ : D, ‖Ph ((δ : G) * x)‖ₑ
      ≤ (a : ℝ≥0∞) * ∫⁻ y, ∑' δ : D, Fd ((δ : G) * x) y ∂μ := step2
    _ = (a : ℝ≥0∞) * ∫⁻ y in F, ∑' s : S, ∑' δ : D, Fd ((δ : G) * x) ((s : G) * y) ∂μ := by
        rw [step3]
    _ ≤ (a : ℝ≥0∞) * ∫⁻ y in F, mult Γ Ω x * ‖Ph y‖ₑ ∂μ := by
        gcongr with y
        exact step4 y
    _ = (a : ℝ≥0∞) * mult Γ Ω x * quotientLIntegral μ F Ph := by
        unfold quotientLIntegral
        rw [lintegral_const_mul _ hPh.enorm, mul_assoc]
end Formalism.L2.SG.FoldBound
