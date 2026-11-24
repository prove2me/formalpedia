-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.compactConjFromUnique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:50.634799+00:00
-- url     : https://prove2.me/submissions/3ed33541-e661-455d-ac1a-fbb9590dceea

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_exists_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_conjM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjM_inv_conjM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjugation_pair_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_conjugation_continuous_on_invertible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution : CompactConjFromUnique := by
  intro HU CH k r U K μ hU hKg hKc hnorm hμ a ha
  have hau : IsUnit a.det := hKg.unit a ha
  have hm := (conjM_cont a).measurable
  have hnorm' : ∀ u ∈ U, a⁻¹ * u * a ∈ U := by
    intro u hu
    have := hnorm a⁻¹ (hKg.inv_mem a ha) u hu
    rwa [Matrix.nonsing_inv_nonsing_inv a hau] at this
  have hH : IsHaarOn U (μ.map (conjM a)) := CH k r U μ a hU hau (hnorm a ha) hnorm' hμ
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map (conjM a)) hU hμ hH.conc hH.left hH.finite_compact
  obtain ⟨C, hC, hC0⟩ := exists_pos μ hμ.ne_zero

  set S : Set (Mt k r) := conj2 '' ((K : Set (Mt k r)) ×ˢ C) with hS
  have hSc : IsCompact S :=
    (IsCompact.prod (show IsCompact (K : Set (Mt k r)) from hKc) hC).image_of_continuousOn
      (conjugation_continuous_on_invertible.mono fun p hp => (hKg.unit p.1 hp.1).ne_zero)
  have hCS : C ⊆ S := by
    intro x hx
    refine ⟨(((1 : Mat k r) : Mt k r), x), ⟨hKg.one_mem, hx⟩, ?_⟩
    rw [conjugation_pair_eq]
    show (1 : Mat k r) * Matrix.of x * (1 : Mat k r)⁻¹ = x
    rw [inv_one, Matrix.one_mul, Matrix.mul_one]; rfl
  have hpre : (conjM a : Mt k r → Mt k r) ⁻¹' S = S := by
    ext x
    constructor
    · rintro ⟨⟨b, y⟩, ⟨hb, hy⟩, hby⟩
      refine ⟨(((a⁻¹ * (Matrix.of b : Mat k r) : Mat k r) : Mt k r), y), ⟨hKg.mul_mem _ (hKg.inv_mem a ha) _ hb, hy⟩, ?_⟩
      rw [conjugation_pair_eq, ← conjM_conjM, ← conjM_inv_conjM a hau x]
      congr 1
    · rintro ⟨⟨b, y⟩, ⟨hb, hy⟩, rfl⟩
      refine ⟨(((a * (Matrix.of b : Mat k r) : Mat k r) : Mt k r), y), ⟨hKg.mul_mem _ ha _ hb, hy⟩, ?_⟩
      rw [conjugation_pair_eq, ← conjM_conjM]; rfl
  have hS0 : μ S ≠ 0 := fun h => hC0 (measure_mono_null hCS h)
  have hSt : μ S ≠ ∞ := (hμ.finite_compact S hSc).ne
  have h4 := congrArg (fun ν : Measure (Mt k r) => ν S) hc
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h4
  rw [Measure.map_apply hm hSc.isClosed.measurableSet, hpre] at h4
  have h5 : ((c : ℝ≥0) : ℝ≥0∞) * μ S = 1 * μ S := by rw [one_mul]; exact h4.symm
  have h6 : ((c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hS0 hSt).mp h5
  have h7 : c = 1 := by exact_mod_cast h6
  rw [hc, h7, one_smul]
end Formalism.FourierDecayAlt.P.B2x1
