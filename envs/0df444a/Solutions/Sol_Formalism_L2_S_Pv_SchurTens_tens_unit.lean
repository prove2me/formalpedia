-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.tens_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:27:57.072575+00:00
-- url     : https://prove2.me/submissions/628521ca-0f27-4a9f-a791-90ebb527dad1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensRep

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
  {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs : (∀ v, G v) → (Hs →L[ℂ] Hs)} {tens : (∀ v, H v) → Hs}
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (hσ : ∀ v, IsUnitRep (σ v)) (h : IsTensAbs σ σs tens) (g : ∀ v, G v) (a : Hs) (x : ∀ v, H v) :
    ⟪σs g (tens x), σs g a⟫_ℂ = ⟪tens x, a⟫_ℂ := by
  have hS : ∀ b ∈ Submodule.span ℂ (Set.range tens), ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨y, rfl⟩ := hb
      rw [h.2.1, h.2.1, h.1, h.1]
      exact Finset.prod_congr rfl fun v _ => (hσ v).2.2.1 (g v) (x v) (y v)
    | zero => simp
    | add b c _ _ hb hc => rw [map_add, inner_add_right, inner_add_right, hb, hc]
    | smul c b _ hb => rw [map_smul, inner_smul_right, inner_smul_right, hb]
  have hcl : IsClosed {b : Hs | ⟪σs g (tens x), σs g b⟫_ℂ = ⟪tens x, b⟫_ℂ} :=
    isClosed_eq (continuous_const.inner (σs g).continuous) (continuous_const.inner continuous_id)
  have hsub := closure_minimal (fun b hb => hS b hb) hcl
  rw [h.2.2.closure_eq] at hsub
  exact hsub (Set.mem_univ a)
end Formalism.L2.S.Pv.SchurTens
