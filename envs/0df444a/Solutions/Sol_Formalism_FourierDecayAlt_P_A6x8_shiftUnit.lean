-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.shiftUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:43.385849+00:00
-- url     : https://prove2.me/submissions/3e9d38db-d4de-4884-a1b3-2406e6981df6

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_adic_of_datum
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_unit_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_shift_small

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
namespace Formalism.FourierDecayAlt.P.A6x8
theorem _root_.solution : ShiftUnit := by
  intro K _ _ _ R ψ hD hn Sg
  obtain ⟨ϖ, h⟩ := adic_of_datum hD hn
  obtain ⟨V, hV, hVs⟩ := h.shift_small Sg ϖ
  refine ⟨V, hV, fun t ht σ hσ => ?_⟩
  have hj := hVs _ ht σ hσ
  obtain ⟨v, hv, e⟩ := h.unit_one _ hj
  have hjR : 1 + σ * (t : K) ∈ R := by
    obtain ⟨r, hr, e'⟩ := hj
    rw [e']; exact R.add_mem R.one_mem (R.mul_mem h.mem hr)
  have hx : ((t⁻¹ : Kˣ) : K) + σ = ((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K)) := by
    have : ((t⁻¹ : Kˣ) : K) * (t : K) = 1 := by simp
    linear_combination -σ * this
  rw [hx]
  refine ⟨(Units.isUnit _).mul (isUnit_iff_exists_inv.2 ⟨v, e⟩), ?_⟩
  have : mulR R (((t⁻¹ : Kˣ) : K) * (1 + σ * (t : K))) = mulR R ((t⁻¹ : Kˣ) : K) := by
    ext y
    simp only [mulR, AddSubgroup.mem_map, Subring.mem_toAddSubgroup, AddMonoidHom.coe_mulLeft]
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(1 + σ * (t : K)) * r, R.mul_mem hjR hr, by ring⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨v * r, R.mul_mem hv hr, by linear_combination ((t⁻¹ : Kˣ) : K) * r * e⟩
  unfold modK
  rw [this]
end Formalism.FourierDecayAlt.P.A6x8
