-- Prove2me | solution 1 for Formalism.L2.S.Pv.SchurTens.lintegral_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:30:59.922211+00:00
-- url     : https://prove2.me/submissions/5bade4cc-b947-45d6-9b14-41c8a12d01d7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_norm_sq_of_mul_conj
import Theorems.Thm_Formalism_L2_S_Pv_SchurTens_enorm_sq_eq

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
private theorem mul_conj_eq_ofReal_norm_sq_complex (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
private theorem integral_norm_sq_coeff_eq_of_SP {a b : Hs} (h : SP m σs D a b a b) :
    ∫ x, ‖coeff σs a b x‖ ^ 2 ∂m = ‖a‖ ^ 2 * ‖b‖ ^ 2 / D := by
  obtain ⟨-, h2⟩ := h
  have e1 : (fun x => ⟪b, σs x a⟫_ℂ * conj ⟪b, σs x a⟫_ℂ) =
      fun x => ((‖coeff σs a b x‖ ^ 2 : ℝ) : ℂ) :=
    funext fun x => mul_conj_eq_ofReal_norm_sq_complex _
  rw [e1] at h2
  rw [integral_complex_ofReal] at h2
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ((∫ x, ‖coeff σs a b x‖ ^ 2 ∂m : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖b‖ ^ 2 / D : ℝ) : ℂ) := by
    rw [h2]
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
    rfl
  exact Complex.ofReal_injective h3
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
    ∫⁻ x, ‖coeff σs a b x‖ₑ ^ 2 ∂m = ENNReal.ofReal (‖a‖ ^ 2 * ‖b‖ ^ 2 / D) := by
  rw [lintegral_enorm_sq_coeff_eq_ofReal_of_SP h, integral_norm_sq_coeff_eq_of_SP h]
end Formalism.L2.S.Pv.SchurTens
