-- Prove2me | solution 1 for Formalism.L2.S.Pv.EnergyAbs.tendsto_energy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:25.203827+00:00
-- url     : https://prove2.me/submissions/fbc7908a-76a6-4acb-b5c7-1455d51927f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsBasic
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsDefs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsSchur
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsTrunc
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_EnergyAbsEnergy

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
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.EnergyAbs
open Formalism.L2.SG.Pf.EnergyAbs
variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V V' : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
namespace Formalism.L2.S.Pv.EnergyAbs
theorem _root_.solution {d : ℝ} (hd : 0 < d) {a b : ℕ → ℝ≥0∞} (ha : ∀ n, 0 < a n ∧ a n < ⊤)
    (hb : ∀ n, 0 < b n ∧ b n < ⊤) {N N' : ℕ → ℝ}
    (hN : Tendsto (fun n => N n / (a n).toReal) atTop (𝓝 (1 / d)))
    (hN' : Tendsto (fun n => N' n / (b n).toReal) atTop (𝓝 (1 / d))) :
    Tendsto (fun n => (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n)) atTop (𝓝 (ENNReal.ofReal (1 / d))) := by
  have key : ∀ n, (a n * b n)⁻¹ * ENNReal.ofReal (d * N n * N' n) =
      ENNReal.ofReal (d * (N n / (a n).toReal) * (N' n / (b n).toReal)) := by
    intro n
    obtain ⟨ha0, hat⟩ := ha n
    obtain ⟨hb0, hbt⟩ := hb n
    have ha' : 0 < (a n).toReal := ENNReal.toReal_pos ha0.ne' hat.ne
    have hb' : 0 < (b n).toReal := ENNReal.toReal_pos hb0.ne' hbt.ne
    have hab : (a n * b n)⁻¹ = ENNReal.ofReal (((a n).toReal * (b n).toReal)⁻¹) := by
      rw [ENNReal.ofReal_inv_of_pos (mul_pos ha' hb'), ← ENNReal.toReal_mul,
        ENNReal.ofReal_toReal (ENNReal.mul_ne_top hat.ne hbt.ne)]
    rw [hab, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos ha' hb').le)]
    congr 1
    field_simp
  simp_rw [key]
  apply ENNReal.tendsto_ofReal
  have hlim := (hN.const_mul d).mul hN'
  rwa [show d * (1 / d) * (1 / d) = 1 / d by field_simp] at hlim
end Formalism.L2.S.Pv.EnergyAbs
