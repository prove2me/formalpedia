-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.exists_ideal_element_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:29:49.586385+00:00
-- url     : https://prove2.me/submissions/27ccd4ca-8795-4c97-b0af-e5a669910173

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution : ∃ t β : 𝓞 I.E, t ∈ w.asIdeal ∧ t ≠ 0 ∧ (∀ a ∈ w.asIdeal, ∃ g, β * a = t * g) ∧
    β ∉ w.asIdeal := by
  have hne : w.asIdeal ^ 2 ≠ w.asIdeal := by
    intro h
    have h0 : w.asIdeal ≠ 0 := by rw [Ideal.zero_eq_bot]; exact w.ne_bot
    have : w.asIdeal * w.asIdeal = w.asIdeal * 1 := by rw [mul_one, ← sq, h]
    have h1 := mul_left_cancel₀ h0 this
    exact w.isPrime.ne_top (by rw [h1, Ideal.one_eq_top])
  have hlt : w.asIdeal ^ 2 < w.asIdeal := lt_of_le_of_ne (Ideal.pow_le_self two_ne_zero) hne
  obtain ⟨t, htw, ht2⟩ := SetLike.exists_of_lt hlt
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (zero_mem _)
  obtain ⟨w', hw'⟩ : w.asIdeal ∣ Ideal.span {t} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 htw)
  have hw'w : ¬ w' ≤ w.asIdeal := by
    intro h
    apply ht2
    have : Ideal.span {t} ≤ w.asIdeal ^ 2 := by rw [hw', sq]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self t)
  obtain ⟨β, hβ, hβw⟩ := SetLike.not_le_iff_exists.1 hw'w
  refine ⟨t, β, htw, ht0, fun a ha => ?_, hβw⟩
  have : a * β ∈ Ideal.span {t} := by rw [hw']; exact Ideal.mul_mem_mul ha hβ
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.1 this
  exact ⟨g, by rw [mul_comm β, ← hg, mul_comm]⟩
end Formalism.L2.SG.Pf.RedBasicsPf
