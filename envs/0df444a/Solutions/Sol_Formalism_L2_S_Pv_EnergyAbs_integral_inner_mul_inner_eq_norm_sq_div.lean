-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.integral_inner_mul_inner_eq_norm_sq_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:01:03.358474+00:00
-- url     : https://prove2.me/submissions/aa8a787e-015a-4f48-9166-b1cbc43e2dda

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerExp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsFolnerLim

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
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {μ : Measure G} [μ.IsMulLeftInvariant] {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {d : ℝ}
    (hd : 0 < d) {w : HH} {S : Set G} {τ : G → (V →L[ℂ] V)} {ν : Measure G} {W : G → V}
    (hW : IsWAbs μ σ d w S τ ν W) (z : G) :
    ∫ x, ⟪W x, W z⟫_ℂ * ⟪σ z w, σ x w⟫_ℂ ∂μ = ((‖W z‖ ^ 2 / d : ℝ) : ℂ) := by
  obtain ⟨hint, heq⟩ := hW.2.2.2.2.2.1 z
  rw [← integral_mul_left_eq_self _ z]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hpt : ∀ y, ⟪W (z * y), W z⟫_ℂ * ⟪σ z w, σ (z * y) w⟫_ℂ =
      conj (((1 / d : ℝ) : ℂ) * ⟪W z, ((d : ℂ) * conj ⟪w, σ y w⟫_ℂ) • W (z * y)⟫_ℂ) := by
    intro y
    rw [hσ.2.1 z y, ContinuousLinearMap.mul_apply, hσ.2.2.1, inner_smul_right]
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, inner_conj_symm]
    push_cast
    first | (field_simp; ring) | field_simp | ring
  simp_rw [hpt]
  have hself : ⟪W z, W z⟫_ℂ = ((‖W z‖ ^ 2 : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · first
        | simp [inner_self_eq_norm_sq]
        | (rw [Complex.ofReal_re]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (W z))
    · first
        | simp
        | (rw [Complex.ofReal_im]; exact inner_self_im (𝕜 := ℂ) (W z))
  rw [integral_conj, integral_const_mul, integral_inner hint, heq, hself, ← Complex.ofReal_mul,
    Complex.conj_ofReal]
  congr 1
  ring
end Formalism.L2.S.Pv.EnergyAbs
