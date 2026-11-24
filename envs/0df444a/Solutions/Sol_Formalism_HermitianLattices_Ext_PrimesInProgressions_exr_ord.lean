-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exr_ord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:35.643819+00:00
-- url     : https://prove2.me/submissions/598eee4d-8d3f-4cdc-8561-3801386266bb

import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LandauLocalOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplRectA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (f h : ℂ → ℂ) (Zb : Finset ℂ) (m : ℂ → ℕ) (S : Set ℂ) (hS : IsOpen S)
    (hh : DifferentiableOn ℂ h S) (hfac : ∀ z ∈ S, f z = (∏ ρ ∈ Zb, (z - ρ) ^ m ρ) * h z)
    (ρ : ℂ) (hρ : ρ ∈ Zb) (hρS : ρ ∈ S) (hhρ : h ρ ≠ 0) : analyticOrderNatAt f ρ = m ρ := by
  classical
  have hne : ∀ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ' ≠ 0 := fun ρ' h' =>
    pow_ne_zero _ (sub_ne_zero.2 fun e => (Finset.ne_of_mem_erase h') e.symm)
  have hgD : DifferentiableOn ℂ (fun z => (∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) S :=
    (DifferentiableOn.fun_finset_prod fun ρ' _ => (differentiableOn_id.sub_const ρ').pow _).mul hh
  have hgA := hgD.analyticAt (hS.mem_nhds hρS)
  have hg0 : (∏ ρ' ∈ Zb.erase ρ, (ρ - ρ') ^ m ρ') * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 hne) hhρ
  have heq : ∀ z ∈ S, f z = (z - ρ) ^ m ρ * ((∏ ρ' ∈ Zb.erase ρ, (z - ρ') ^ m ρ') * h z) := by
    intro z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Zb (fun ρ' => (z - ρ') ^ m ρ') hρ, mul_assoc]
  have hfA : AnalyticAt ℂ f ρ :=
    (((analyticAt_id.sub analyticAt_const).pow (m ρ)).mul hgA).congr
      (Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => (heq z hz).symm)
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hfA.analyticOrderAt_eq_natCast]
    exact ⟨_, hgA, hg0, Filter.eventually_of_mem (hS.mem_nhds hρS) fun z hz => by rw [heq z hz, smul_eq_mul]⟩
  simp [analyticOrderNatAt, hord]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
