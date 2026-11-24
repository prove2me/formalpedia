-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B3.ae_eq_of_tests
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:46:15.400234+00:00
-- url     : https://prove2.me/submissions/bf116e23-e0ec-45fc-adc5-9c4930375202

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_isTest
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_measurableSet_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_box_tendsto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B3
theorem _root_.solution {f g : ℝ × ℝ → ℝ≥0∞} (hf : AEMeasurable f (volume.restrict Quad))
    (hg : AEMeasurable g (volume.restrict Quad)) (hfin : FinT f)
    (H : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * f τ ∂(volume.restrict Quad)) =
        ∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * g τ ∂(volume.restrict Quad)) :
    f =ᵐ[volume.restrict Quad] g := by
  have hgfin : FinT g := fun w₁ w₂ h₁ h₂ p₁ p₂ => by
    rw [← H w₁ w₂ h₁ h₂ p₁ p₂]
    exact hfin w₁ w₂ h₁ h₂ p₁ p₂
  have box_eq : ∀ a₁ b₁ a₂ b₂ : ℝ, 0 < a₁ → 0 < a₂ →
      ((volume.restrict Quad).withDensity f) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) =
        ((volume.restrict Quad).withDensity g) (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) := by
    intro a₁ b₁ a₂ b₂ h₁ h₂
    refine tendsto_nhds_unique (box_tendsto hf hfin b₁ b₂ h₁ h₂) ?_
    refine (box_tendsto hg hgfin b₁ b₂ h₁ h₂).congr fun n => ?_
    exact (H _ _ (pl_isTest h₁ (Nat.cast_nonneg n)) (pl_isTest h₂ (Nat.cast_nonneg n))
      (pl_nonneg _ _ _) (pl_nonneg _ _ _)).symm
  have hcompl : ∀ h : ℝ × ℝ → ℝ≥0∞, ((volume.restrict Quad).withDensity h) Quadᶜ = 0 := by
    intro h
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply measurableSet_Quad.compl, compl_inter_self, measure_empty]
  let B : ℕ → Set (ℝ × ℝ) := fun n => Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Ioo (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have key : (volume.restrict Quad).withDensity f = (volume.restrict Quad).withDensity g := by
    refine Measure.ext_of_generateFrom_of_cover (T := insert Quadᶜ (range B))
      (generateFrom_eq_prod (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm)
        (Real.borel_eq_generateFrom_Ioo_rat ▸ (BorelSpace.measurable_eq (α := ℝ)).symm)
        (Real.finiteSpanningSetsInIooRat volume).isCountablySpanning
        (Real.finiteSpanningSetsInIooRat volume).isCountablySpanning).symm
      ((countable_range B).insert _) (Real.isPiSystem_Ioo_rat.prod Real.isPiSystem_Ioo_rat) ?_ ?_ ?_ ?_
    · refine eq_univ_of_forall fun τ => ?_
      by_cases hτ : τ ∈ Quad
      · obtain ⟨n, hn⟩ := exists_nat_gt (max (max (1 / τ.1) (1 / τ.2)) (max τ.1 τ.2))
        simp only [max_lt_iff] at hn
        obtain ⟨⟨n1, n2⟩, n3, n4⟩ := hn
        have h1 : 0 < τ.1 := hτ.1
        have h2 : 0 < τ.2 := hτ.2
        have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        refine mem_sUnion.mpr ⟨B n, Or.inr ⟨n, rfl⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · exact (one_div_lt h1 hn0).mp (by linarith)
        · linarith
        · exact (one_div_lt h2 hn0).mp (by linarith)
        · linarith
      · exact mem_sUnion.mpr ⟨Quadᶜ, Or.inl rfl, hτ⟩
    · rintro t (rfl | ⟨n, rfl⟩)
      · rw [hcompl]; exact ENNReal.zero_ne_top
      · exact box_fin hfin _ _ (hpos n) (hpos n)
    · rintro t (rfl | ⟨n, rfl⟩) s hs
      · rw [measure_mono_null inter_subset_right (hcompl f), measure_mono_null inter_subset_right (hcompl g)]
      · obtain ⟨s₁, hs₁, s₂, hs₂, rfl⟩ := hs
        simp only [mem_iUnion, mem_singleton_iff] at hs₁ hs₂
        obtain ⟨l₁, u₁, -, rfl⟩ := hs₁
        obtain ⟨l₂, u₂, -, rfl⟩ := hs₂
        simp only [B]
        rw [prod_inter_prod, Ioo_inter_Ioo, Ioo_inter_Ioo]
        exact box_eq _ _ _ _ (lt_max_of_lt_right (hpos n)) (lt_max_of_lt_right (hpos n))
    · rintro t (rfl | ⟨n, rfl⟩)
      · rw [hcompl, hcompl]
      · exact box_eq _ _ _ _ (hpos n) (hpos n)
  exact (withDensity_eq_iff_of_sigmaFinite hf hg).mp key
end Formalism.FourierDecayAlt.P.B3
