-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.Xop_eq_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:38:23.828795+00:00
-- url     : https://prove2.me/submissions/b23be04f-1b3d-4cac-b4ce-aca096142ef3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_integrable_fY
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_yv_eq_integral
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_inner_integral_left
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_op_ext_basis
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_Yop_apply_basis
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_inner_sand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
private theorem rk1A_apply (u : V) (v : V') (x : V') : Formalism.L2.SG.Pf.EnergyAbs.rk1A u v x = ⟪v, x⟫_ℂ • u := by
  rfl
private theorem inner_kG_apply_eq (σ : G → (HH →L[ℂ] HH)) (d : ℝ) (w : HH) (W : G → V) (W' : G → V')
    (γ : G) (a : V) (b : V') (p p' : G × G) :
    ⟪a, kG σ d w W W' γ (φinv p, φinv p') b⟫_ℂ =
      (d : ℂ) * ⟪fY σ w W a p, σ γ (fY σ w W' b p')⟫_ℂ := by
  unfold kG fY φinv
  simp only [ContinuousLinearMap.smul_apply, rk1A_apply, inner_smul_right, inner_smul_left,
    map_smul, inner_conj_symm]
  ring
private theorem integrable_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (b : V') : Integrable (fun x => F x b) m := by
  exact hF.apply_continuousLinearMap b
private theorem integrable_inner_apply_of_integrable_clm {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : Integrable (fun x => ⟪a, F x b⟫_ℂ) m := by
  exact (integrable_apply_of_integrable_clm hF b).const_inner a
private theorem inner_integral_clm_apply_eq_integral {α : Type*} [MeasurableSpace α] {m : Measure α} {F : α → (V' →L[ℂ] V)}
    (hF : Integrable F m) (a : V) (b : V') : ⟪a, (∫ x, F x ∂m) b⟫_ℂ = ∫ x, ⟪a, F x b⟫_ℂ ∂m := by
  have happ : (∫ x, F x ∂m) b = ∫ x, F x b ∂m := by
    exact ContinuousLinearMap.integral_apply hF b
  rw [happ]
  exact (integral_inner (integrable_apply_of_integrable_clm hF b) a).symm
end Formalism.L2.S.Pv.EnergyAbs
end
end

set_option autoImplicit false
noncomputable section
open MeasureTheory Measure
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ μS ν μS' ν' : Measure G} [SFinite ν]
    [SFinite μS] [SFinite ν'] [SFinite μS'] {d : ℝ} {w : HH} {S S' : Set G} {τ : G → (V →L[ℂ] V)}
    {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') {A A' : Set G} (hA : MeasurableSet A)
    (hAS : A ⊆ S) (hAf : μS A < ⊤) (hA' : MeasurableSet A') (hAS' : A' ⊆ S') (hAf' : μS' A' < ⊤) (γ : G)
    (hK : Integrable (fun q : (G × G) × (G × G) => kG σ d w W W' γ (φinv q.1, φinv q.2))
      ((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A')))) :
    Xop μS ν μS' ν' σ d w W W' A A' γ =
      ∫ q, kG σ d w W W' γ (φinv q.1, φinv q.2) ∂((ν.prod (μS.restrict A)).prod (ν'.prod (μS'.restrict A'))) := by
  refine op_ext_basis _ _ (fun i j => ?_)
  have hf := integrable_fY hσ hW hinv hA hAS hAf (stdOrthonormalBasis ℂ V i)
  have hf' := integrable_fY hσ hW' hinv' hA' hAS' hAf' (stdOrthonormalBasis ℂ V' j)
  have hL : ⟪stdOrthonormalBasis ℂ V i,
      Xop μS ν μS' ν' σ d w W W' A A' γ (stdOrthonormalBasis ℂ V' j)⟫_ℂ =
      ∫ p, ∫ p', (d : ℂ) * ⟪fY σ w W (stdOrthonormalBasis ℂ V i) p,
        σ γ (fY σ w W' (stdOrthonormalBasis ℂ V' j) p')⟫_ℂ
          ∂(ν'.prod (μS'.restrict A')) ∂(ν.prod (μS.restrict A)) := by
    rw [Xop, ContinuousLinearMap.smul_apply, inner_smul_right, inner_sand,
      Yop_apply_basis, Yop_apply_basis,
      yv_eq_integral hσ hW hinv hA hAS hAf,
      yv_eq_integral hσ hW' hinv' hA' hAS' hAf',
      ← (σ γ).integral_comp_comm hf', inner_integral_left hf, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    try dsimp only
    rw [integral_const_mul, integral_inner ((σ γ).integrable_comp hf')]
  rw [hL, inner_integral_clm_apply_eq_integral hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j),
    integral_prod _ (integrable_inner_apply_of_integrable_clm hK (stdOrthonormalBasis ℂ V i) (stdOrthonormalBasis ℂ V' j))]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  try dsimp only
  refine integral_congr_ae (ae_of_all _ fun p' => ?_)
  try dsimp only
  exact (inner_kG_apply_eq σ d w W W' γ _ _ p p').symm
end Formalism.L2.S.Pv.EnergyAbs
