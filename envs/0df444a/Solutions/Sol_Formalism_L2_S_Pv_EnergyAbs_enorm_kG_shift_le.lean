-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.enorm_kG_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:50.913662+00:00
-- url     : https://prove2.me/submissions/4402280c-2da6-4675-8a11-baf3798cb43c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsRep
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsInt
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_coef_shift
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_norm_W_shift
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_enorm_rk1A_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {μ ν ν' : Measure G} {d : ℝ} {w : HH}
    {S S' : Set G} {τ : G → (V →L[ℂ] V)} {τ' : G → (V' →L[ℂ] V')} {W : G → V} {W' : G → V'}
    (hW : IsWAbs μ σ d w S τ ν W) (hW' : IsWAbs μ σ d w S' τ' ν' W')
    (hinv : ∀ a ∈ S, a⁻¹ ∈ S) (hinv' : ∀ a ∈ S', a⁻¹ ∈ S') (γ z u z' u' : G) (hu : u ∈ S) (hu' : u' ∈ S') :
    ‖kG σ d w W W' γ (u⁻¹ * z, u'⁻¹ * z')‖ₑ ≤ ‖(d : ℂ)‖ₑ * bInt σ w W W' γ z z' u u' := by
  have e1 : ‖W (u⁻¹ * z)‖ₑ = ‖W z‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW) hinv hu z)
  have e2 : ‖W' (u'⁻¹ * z')‖ₑ = ‖W' z'‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    congr 1
    exact NNReal.eq ((norm_W_shift hW') hinv' hu' z')
  have hR : ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ ≤ ‖W z‖ₑ * ‖W' z'‖ₑ := by
    rw [← e1, ← e2]
    exact enorm_rk1A_le _ _
  simp only [kG, bInt]
  rw [coef_shift hσ, enorm_smul, enorm_mul]
  calc ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * ‖Formalism.L2.SG.Pf.EnergyAbs.rk1A (W (u⁻¹ * z)) (W' (u'⁻¹ * z'))‖ₑ
      ≤ ‖(d : ℂ)‖ₑ * ‖⟪σ z w, σ (u * γ * u'⁻¹) (σ z' w)⟫_ℂ‖ₑ * (‖W z‖ₑ * ‖W' z'‖ₑ) := by gcongr
    _ = _ := by simp only [mul_assoc]
end Formalism.L2.S.Pv.EnergyAbs
