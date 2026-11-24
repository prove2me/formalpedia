-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RankOneEmbeddings.In.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:06:26.411778+00:00
-- url     : https://prove2.me/submissions/9d1c4d34-f868-49b6-bf0e-daeb99bd51bd

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_R1_ae_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_uw_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_first_coordinate_map_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_swap_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_mp_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RankOneEmbeddings Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
theorem _root_.solution {z z' : Vc k r} {μW μN μW' : Measure (Mt k r)} [SFinite μW] [SFinite μN] [SFinite μW']
    (UF : UWbFacts) (hW : IsHaarOn (UWset k r z) μW) (hW' : IsHaarOn (UWset k r z') μW')
    (hc : ∀ h ∈ UWset k r z, μN.map (conjM h) = μN) (hc' : ∀ h ∈ UWset k r z', μN.map (conjM h) = μN)
    (g0 E : Mt k r) (hcomm : ∀ m ∈ UWb k r, m * (Matrix.of g0 : Mat k r) = (Matrix.of g0 : Mat k r) * m)
    (f : Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ nn : Mt k r × Mt k r, ∫⁻ hh : Mt k r × Mt k r,
        f (mulM (mulM (mulM (invM nn.1, g0), mulM (mulM (invM hh.1, E), hh.2)), nn.2)) ∂(μW.prod μW') ∂(μN.prod μN) =
      ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) := by
  let Γ : Mt k r × Mt k r → ℝ≥0∞ := fun ab => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2))
  have hΓ : Measurable Γ := by
    show Measurable fun ab : Mt k r × Mt k r => f (mulM (mulM (invM ab.1, mulM (g0, E)), ab.2))
    fun_prop
  have r1 : ∫⁻ p : SS k r, f (sgF (p, mulM (g0, E))) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    refine lintegral_congr fun p => congrArg f ?_
    show (Matrix.of p.1.1 : Mat k r)⁻¹ * (Matrix.of p.1.2 : Mat k r)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
        Matrix.of p.2.2 * Matrix.of p.2.1 =
      ((Matrix.of p.1.2 : Mat k r) * Matrix.of p.1.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
        ((Matrix.of p.2.2 : Mat k r) * Matrix.of p.2.1)
    rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc _ (Matrix.of p.2.2 : Mat k r)]
  have r2 : ∫⁻ p : SS k r, Γ (Prod.map m1 m1 p) ∂((μW.prod μN).prod (μW'.prod μN)) =
      ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN)) := by
    rw [← lintegral_map hΓ (first_coordinate_map_measurable.prodMap first_coordinate_map_measurable), ← lintegral_map hΓ (mulM_meas.prodMap mulM_meas),
      ← Measure.map_prod_map _ _ first_coordinate_map_measurable first_coordinate_map_measurable, ← Measure.map_prod_map _ _ mulM_meas mulM_meas,
      swap_meas hW hc, swap_meas hW' hc']
  have hΓ2 : Measurable fun p : SS k r => Γ (Prod.map mulM mulM p) := hΓ.comp (mulM_meas.prodMap mulM_meas)
  have r3 : ∫⁻ x : (Mt k r × Mt k r) × (Mt k r × Mt k r), Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2)))
        ∂((μN.prod μN).prod (μW.prod μW')) =
      ∫⁻ p : SS k r, Γ (Prod.map mulM mulM p) ∂((μW.prod μN).prod (μW'.prod μN)) :=
    (mp_perm μN μN μW μW').lintegral_comp hΓ2
  rw [r1, r2, ← r3, lintegral_prod
    (fun x : (Mt k r × Mt k r) × (Mt k r × Mt k r) => Γ (Prod.map mulM mulM ((x.2.1, x.1.1), (x.2.2, x.1.2))))
    (hΓ2.comp (mp_perm μN μN μW μW').measurable).aemeasurable]
  refine lintegral_congr fun nn => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μW) (ν := μW')).ae (ae_mem hW)] with hh h1
  refine congrArg f ?_
  show (Matrix.of nn.1 : Mat k r)⁻¹ * (Matrix.of g0 : Mat k r) *
        ((Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of E * Matrix.of hh.2) * Matrix.of nn.2 =
    ((Matrix.of hh.1 : Mat k r) * Matrix.of nn.1)⁻¹ * ((Matrix.of g0 : Mat k r) * Matrix.of E) *
      ((Matrix.of hh.2 : Mat k r) * Matrix.of nn.2)
  have hu := uw_unit h1
  have e1 : (Matrix.of g0 : Mat k r) * (Matrix.of hh.1 : Mat k r)⁻¹ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0 := by
    have e0 := hcomm _ ((UF k r).2.1 z h1)
    calc (Matrix.of g0 : Mat k r) * (Matrix.of hh.1 : Mat k r)⁻¹
        = (Matrix.of hh.1 : Mat k r)⁻¹ * ((Matrix.of hh.1 : Mat k r) * Matrix.of g0) * (Matrix.of hh.1 : Mat k r)⁻¹ := by
          rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
      _ = (Matrix.of hh.1 : Mat k r)⁻¹ * Matrix.of g0 := by
          rw [e0, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.of g0 : Mat k r) (Matrix.of hh.1 : Mat k r)⁻¹, e1]
  simp only [Matrix.mul_assoc]
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
