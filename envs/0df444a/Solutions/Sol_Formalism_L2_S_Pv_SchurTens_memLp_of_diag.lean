-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.memLp_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:58:20.031284+00:00
-- url     : https://prove2.me/submissions/f3042a42-314f-40b4-8545-e5dd30080920

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_continuous_coeff
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_norm_sq_of_mul_conj
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_enorm_sq_eq
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_memLp_two_of_lintegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
namespace Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}
private theorem integrable_norm_sq_coeff_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    Integrable (fun x => ‖coeff σs a b x‖ ^ 2) m := by
  obtain ⟨hi, -⟩ := h
  exact hi.norm.congr (ae_of_all _ fun x => norm_sq_of_mul_conj (coeff σs a b x))
private theorem lintegral_enorm_sq_coeff_eq_ofReal_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (∫ x, ‖coeff σs a b x‖ ^ 2 ∂m) := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_coeff_of_SP h)
    (ae_of_all _ fun x => sq_nonneg _)]
  exact lintegral_congr fun x => enorm_sq_eq _
section Tens
variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, MeasurableSpace (G v)] {H : ι → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
  {Hs' : Type} [NormedAddCommGroup Hs'] [InnerProductSpace ℂ Hs']
  {σ : ∀ v, G v → (H v →L[ℂ] H v)} {σs' : (∀ v, G v) → (Hs' →L[ℂ] Hs')} {tens : (∀ v, H v) → Hs'}
end Tens
end Formalism.L2.S.Pv.SchurTens
end
end

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
namespace Formalism.L2.S.Pv.SchurTens
theorem _root_.solution (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) {a b : Hs} (h : SP m σs D a b a b) :
    MemLp (coeff σs a b) 2 m :=
  memLp_two_of_lintegral (continuous_coeff hstr a b).aestronglyMeasurable
    (by rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h]; exact ENNReal.ofReal_lt_top)
end Formalism.L2.S.Pv.SchurTens
