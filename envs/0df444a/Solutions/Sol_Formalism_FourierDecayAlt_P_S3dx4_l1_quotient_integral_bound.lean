-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3dx4.l1_quotient_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:44:56.475316+00:00
-- url     : https://prove2.me/submissions/f2eb5283-d036-44a2-840e-23ac91075ee4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMemMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L1QuotientIntegralBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_prod_ae
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_ae_UH_of_quot
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_muSof_facts
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_coef_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3dx4_uh_mem_measurableSet
import Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_FourierDecayAlt_P_WeakDominationMajorants_Orb_key
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3dx4
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.S3dx4
theorem _root_.solution {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx k r → (H →L[ℂ] H)} (hds : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (hGm : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq)
    {x v : H} {C a : ℝ}
    (hC : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), ‖⟪v, σ y x⟫_ℂ‖ ≤ C * B.gN y ^ (-a))
    (hI : Integrable (fun y : Formalism.QuantumDeterminants.Mt k r => B.gN (Matrix.of y) ^ (-a)) μG) :
    ∫⁻ g, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) ∂νq < ⊤ := by
  obtain ⟨e, he, hee⟩ := coef_ext hds v x
  set U : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)} with hU
  set f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := U.indicator (fun y => ‖e (Matrix.of y)‖ₑ) with hf
  have hfm : Measurable f := by
    have hc : Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of y)) :=
      he.comp (show Continuous (fun y : Formalism.QuantumDeterminants.Mt k r => (Matrix.of y : Mx k r)) from continuous_id)
    have : Measurable (fun y : Formalism.QuantumDeterminants.Mt k r => ‖e (Matrix.of y)‖ₑ) := hc.measurable.enorm
    exact this.indicator uh_mem_measurableSet
  have hφ : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j : Formalism.QuantumDeterminants.Mt k r)) := by
    have h1 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mx k r)) := continuous_fst
    have h2 : Continuous (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mx k r)) := continuous_snd
    exact h1.matrix_mul h2
  have hmul : ∀ g : Formalism.QuantumDeterminants.Mt k r, Measurable (fun s : Formalism.QuantumDeterminants.Mt k r =>
      f (fun i j => (Matrix.of s * Matrix.of g) i j)) := by
    intro g
    have : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r =>
        (fun i j => (Matrix.of s * Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r)) := by
      have h1 : Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mx k r)) := continuous_id
      exact h1.matrix_mul continuous_const
    exact hfm.comp this.measurable
  have hfacts := DDSmoothness.muSof_facts hW hN
  have hae := DDSmoothness.ae_UH_of_quot hGm.2.2.1 hfacts.1 hfacts.2 hq

  have step1 : ∀ᵐ g ∂νq, (∫⁻ p, ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ ∂(μW.prod μN)) =
      ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of g) i j) ∂(muSof μW μN) := by
    filter_upwards [hae] with g hg
    unfold muSof
    rw [lintegral_map (hmul g) hφ.measurable]
    apply lintegral_congr_ae
    filter_upwards [prod_ae hW hN] with p hp
    have hhn : Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := DDSmoothness.uh_mul hp.1.1 hp.2.1
    have hin : Matrix.of p.1 * Matrix.of p.2 * Matrix.of g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
      DDSmoothness.uh_mul hhn hg
    have key : (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) *
        Matrix.of g) i j : Formalism.QuantumDeterminants.Mt k r) ∈ U := hin
    show ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g) x⟫_ℂ‖ₑ =
      f (fun i j => (Matrix.of (fun i j => (Matrix.of p.1 * Matrix.of p.2) i j) * Matrix.of g) i j)
    rw [hf, Set.indicator_of_mem key]
    show _ = ‖e (Matrix.of p.1 * Matrix.of p.2 * Matrix.of g)‖ₑ
    rw [hee _ hin]
  rw [lintegral_congr_ae step1, ← hq f hfm]

  have hb : ∀ᵐ y ∂μG, f y ≤ ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ := by
    have hGc : ∀ᵐ y ∂μG, Matrix.of y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
      rw [ae_iff]; simpa using hGm.2.2.1
    filter_upwards [hGc] with y hy
    simp only [hf]
    rw [Set.indicator_of_mem (show y ∈ U from hy), hee _ hy, ← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal ((hC _ hy).trans (le_abs_self _) |>.trans (le_of_eq (Real.norm_eq_abs _).symm))
  calc ∫⁻ y, f y ∂μG ≤ ∫⁻ y, ‖C * B.gN (Matrix.of y) ^ (-a)‖ₑ ∂μG := lintegral_mono_ae hb
    _ < ⊤ := (hI.const_mul C).hasFiniteIntegral
end Formalism.FourierDecayAlt.P.S3dx4
