-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.isSchur_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:41.33723+00:00
-- url     : https://prove2.me/submissions/89e45551-b129-409c-a7ca-20693bedf55a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_isSchur_of_dense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_pure
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_span
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_isUnitRep_tens


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs' : Type} [NormedAddCommGroup Hs'] [InnerProductSpace ℂ Hs']
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs' : (∀ v, G v) → (Hs' →L[ℂ] Hs')} {tens : (∀ v, H v) → Hs'}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution [OpensMeasurableSpace (∀ v, G v)] (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)]
    (d : ι → ℝ) (hσ : ∀ v, IsUnitRep (σ v)) (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs' tens) :
    IsSchur (Measure.pi μ) σs' (∏ v, d v) := by
  have hU := isUnitRep_tens hσ h
  obtain ⟨-, -, -, hcont⟩ := hU
  have hh := h
  obtain ⟨-, -, hdense⟩ := hh
  have hD : 0 < ∏ v, d v := Finset.prod_pos fun v _ => by
    obtain ⟨hd, -⟩ := hS v
    exact hd
  have hE : ∀ a ∈ Set.range tens, ∀ b ∈ Set.range tens, ∀ a' ∈ Set.range tens, ∀ b' ∈ Set.range tens,
      SP (Measure.pi μ) σs' (∏ v, d v) a b a' b' := by
    rintro _ ⟨α, rfl⟩ _ ⟨β, rfl⟩ _ ⟨α', rfl⟩ _ ⟨β', rfl⟩
    exact SP_pure μ d hS h α β α' β'
  exact isSchur_of_dense hcont hD (Submodule.span ℂ (Set.range tens)) hdense
    (SP_span hE)
end Formalism.L2.S.Pv.SchurTens
