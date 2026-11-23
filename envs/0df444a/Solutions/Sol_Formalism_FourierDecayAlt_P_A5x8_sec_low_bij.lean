-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x8.sec_low_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:57:15.112344+00:00
-- url     : https://prove2.me/submissions/22ca5a5f-c877-444d-973c-2669ef7a32f2

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AddedBlockKernelSupport
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_cX_outV
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_cX_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_surj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_lowJ_int
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x8
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x8
theorem _root_.solution (h : Point K) (c : Kˣ) :
    Function.Bijective (fun p : Quotient (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2))) ×
        (Fin h.1.sum → KR R) =>
      (Quotient.mk (QuotientGroup.rightRel
        (intSub R (lowW K (addBlock h 1 c).1 (addBlock h 1 c).2)))
        (sec_lowJ h c p.1.out (outV R p.2)))) := by
  refine sec_fib (Quotient.mk (QuotientGroup.rightRel (intSub R (lowW K h.1 h.2)))) Quotient.out
    Quotient.out_eq (sec_cX R) (outV R) (sec_cX_outV R) _ Quotient.mk_surjective (sec_lowJ h c)
    (sec_lowJ_surj h c) ?_ ?_ ?_
  · intro a x a' x' e
    obtain ⟨g, hg, e1⟩ := (sec_right_eq _ _ _).1 e
    obtain ⟨a0, ρ, rfl⟩ := sec_lowJ_surj h c g
    rw [sec_lowJ_mul] at e1
    exact (sec_right_eq _ _ _).2 ⟨a0, ((sec_lowJ_int R h c a0 ρ).1 hg).1, (sec_lowJ_inj h c e1).1⟩
  · intro a x x'
    rw [sec_cX_eq]
    constructor
    · intro e
      obtain ⟨g, hg, e1⟩ := (sec_right_eq _ _ _).1 e
      obtain ⟨a0, ρ, rfl⟩ := sec_lowJ_surj h c g
      rw [sec_lowJ_mul] at e1
      obtain ⟨e2, e3⟩ := sec_lowJ_inj h c e1
      have ha0 : a0 = 1 := by simpa using e2.symm
      subst ha0
      have e4 : x' = ρ + x := by
        rw [e3]
        change ρ + x ᵥ* (1 : Matrix (Fin h.1.sum) (Fin h.1.sum) K)⁻¹ = _
        simp
      intro j
      rw [e4]
      simpa using ((sec_lowJ_int R h c 1 ρ).1 hg).2 j
    · intro hx
      refine (sec_right_eq _ _ _).2 ⟨sec_lowJ h c 1 (x' - x),
        (sec_lowJ_int R h c 1 _).2 ⟨Subgroup.one_mem _, hx⟩, ?_⟩
      rw [sec_lowJ_mul, one_mul]
      congr 1
      change x' = x' - x + x ᵥ* (1 : Matrix (Fin h.1.sum) (Fin h.1.sum) K)⁻¹
      simp
  · intro a a' e x
    obtain ⟨a0, ha0, rfl⟩ := (sec_right_eq _ _ _).1 e
    refine ⟨0 + x ᵥ* (sec_m a0)⁻¹, (sec_right_eq _ _ _).2 ⟨sec_lowJ h c a0 0,
      (sec_lowJ_int R h c a0 0).2 ⟨ha0, fun _ => R.zero_mem⟩, ?_⟩⟩
    rw [sec_lowJ_mul]
end Formalism.FourierDecayAlt.P.A5x8
