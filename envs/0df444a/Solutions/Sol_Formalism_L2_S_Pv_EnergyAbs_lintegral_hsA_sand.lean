-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.lintegral_hsA_sand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:52.898362+00:00
-- url     : https://prove2.me/submissions/d2d75a85-8366-4f1c-b0ad-034133a0cc48

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_hsA_sand
import Theorems.Thm_Formalism_L2_S_Pv_EnergyAbs_schur_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} {σ : G → (HH →L[ℂ] HH)} {d : ℝ} (hS : IsSchur μ σ d)
    (Y : V →L[ℂ] HH) (Y' : V' →L[ℂ] HH) :
    ∫⁻ γ, ENNReal.ofReal (hsA (sand σ Y Y' γ)) ∂μ =
      ENNReal.ofReal ((∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d) := by
  have hterm : ∀ j i,
      Integrable (fun γ => ‖⟪Y (stdOrthonormalBasis ℂ V i),
        σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ ∧
      ∫ γ, ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
        ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d :=
    fun j i => schur_sq hS _ _
  have hInt : Integrable (fun γ => ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2) μ :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1
  have hrow : ∀ j, ∫ γ, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      ∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2 * ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2 / d := by
    intro j
    rw [integral_finsetSum _ fun i _ => (hterm j i).1]
    exact Finset.sum_congr rfl fun i _ => (hterm j i).2
  have hval : ∫ γ, ∑ j, ∑ i,
      ‖⟪Y (stdOrthonormalBasis ℂ V i), σ γ (Y' (stdOrthonormalBasis ℂ V' j))⟫_ℂ‖ ^ 2 ∂μ =
      (∑ i, ‖Y (stdOrthonormalBasis ℂ V i)‖ ^ 2) *
        (∑ j, ‖Y' (stdOrthonormalBasis ℂ V' j)‖ ^ 2) / d := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ => (hterm j i).1]
    rw [Finset.sum_congr rfl fun j _ => hrow j]
    simp only [Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_comm
  simp_rw [hsA_sand]
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ fun γ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun i _ => sq_nonneg _), hval]
end Formalism.L2.S.Pv.EnergyAbs
