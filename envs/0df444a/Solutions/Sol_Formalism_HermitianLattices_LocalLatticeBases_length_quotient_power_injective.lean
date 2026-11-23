-- Prove2me | solution 1 for Formalism.HermitianLattices.LocalLatticeBases.length_quotient_power_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:30:13.237422+00:00
-- url     : https://prove2.me/submissions/72c33394-6efe-4a6f-b4fc-7f82b96c0356

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_FourierTransformKernelSurjective
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FourierCommutesHeckeScalar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LocalLatticeBases
open Finset
namespace Formalism.HermitianLattices.LocalLatticeBases
theorem _root_.solution : LengthQuotientPowerInjective := by
  intro R _ M _ _ U hU m
  induction m with
  | zero =>
    have : LinearMap.range ((U:Module.End R M)^0) = ⊤ := by rw [pow_zero]; exact LinearMap.range_id
    rw [this, zero_smul]
    exact Module.length_eq_zero
  | succ m ih =>
    have h1 : LinearMap.range (U^m) ≤ (LinearMap.range (U^(m+1))).comap U := by
      rintro _ ⟨y, rfl⟩; exact ⟨y, by rw [pow_succ']; rfl⟩
    have h2 : LinearMap.range (U^(m+1)) ≤ (LinearMap.range U).comap LinearMap.id := by
      rintro _ ⟨y, rfl⟩; exact ⟨(U^m) y, by rw [pow_succ']; rfl⟩
    have key := Module.length_eq_add_of_exact (Submodule.mapQ _ _ U h1) (Submodule.mapQ _ _ LinearMap.id h2) ?_ ?_ ?_
    · rw [key, ih, succ_nsmul]
    · rw [injective_iff_map_eq_zero]
      intro a
      induction a using Submodule.Quotient.induction_on with
      | H x =>
        intro hx
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
        obtain ⟨y, hy⟩ := hx
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨y, hU ?_⟩
        rw [← hy, pow_succ']; rfl
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x => exact ⟨Submodule.Quotient.mk x, by simp⟩
    · intro b
      induction b using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
        constructor
        · rintro ⟨y, hy⟩
          exact ⟨Submodule.Quotient.mk y, by rw [Submodule.mapQ_apply]; simp at hy; rw [hy]⟩
        · rintro ⟨a, ha⟩
          induction a using Submodule.Quotient.induction_on with
          | H y =>
            rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
            obtain ⟨z, hz⟩ := ha
            refine ⟨y - (U^m) z, ?_⟩
            have : (U^(m+1)) z = U ((U^m) z) := by rw [pow_succ']; rfl
            simp only [LinearMap.id_coe, id_eq, map_sub]
            rw [← this, hz]; abel
end Formalism.HermitianLattices.LocalLatticeBases
