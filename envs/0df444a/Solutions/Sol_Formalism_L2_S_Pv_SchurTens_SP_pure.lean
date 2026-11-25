-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.SP_pure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:29.685374+00:00
-- url     : https://prove2.me/submissions/0b97a76b-0a2a-46a9-9f33-e90a6aec5dc6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (μ : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] (d : ι → ℝ)
    (hS : ∀ v, IsSchur (μ v) (σ v) (d v)) (h : IsTensAbs σ σs tens) (α β α' β' : ∀ v, H v) :
    SP (Measure.pi μ) σs (∏ v, d v) (tens α) (tens β) (tens α') (tens β') := by
  have hf : (fun x => ⟪tens β, σs x (tens α)⟫_ℂ * conj ⟪tens β', σs x (tens α')⟫_ℂ) =
      fun x => ∏ v, (⟪β v, σ v (x v) (α v)⟫_ℂ * conj ⟪β' v, σ v (x v) (α' v)⟫_ℂ) := by
    funext x
    rw [h.2.1, h.2.1, h.1, h.1, map_prod, ← Finset.prod_mul_distrib]
  refine ⟨?_, ?_⟩
  · rw [hf]
    exact Integrable.fintype_prod_dep fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).1
  · rw [hf, integral_fintype_prod_eq_prod (fun v y => ⟪β v, σ v y (α v)⟫_ℂ * conj ⟪β' v, σ v y (α' v)⟫_ℂ)]
    simp only [fun v => ((hS v).2 (α v) (β v) (α' v) (β' v)).2]
    rw [h.1, h.1, Finset.prod_div_distrib, Finset.prod_mul_distrib, Complex.ofReal_prod]
end Formalism.L2.S.Pv.SchurTens
