-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.lu_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:47:10.755243+00:00
-- url     : https://prove2.me/submissions/1d0ebaca-324b-4c44-b550-69f841d62d34

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_co_EE
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_g_m
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_lu_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x7_lu_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (R : Subring K) (n : ℕ) (v : Pr n → K) :
    ∃! q : upUniG K n ⧸ intSub R (upUniG K n), ∃ r : Pr n → K, (∀ p, r p ∈ R) ∧
      v = lu_co (sec_m (Quotient.out q)) + lu_M (sec_m (Quotient.out q)) *ᵥ r := by
  refine ⟨((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)), ?_, ?_⟩
  · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (intSub R (upUniG K n)) (lu_g v)
    have hh' : Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) =
        lu_g v * h := hh
    set u := Quotient.out ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) with hu
    have hg : lu_g v = u * (h : upUniG K n)⁻¹ := by rw [hh']; group
    have hinv : ((h : upUniG K n)⁻¹) ∈ intSub R (upUniG K n) := (intSub R (upUniG K n)).inv_mem h.2
    have hr0U : IsUpUni (sec_m ((h : upUniG K n)⁻¹)) := ((h : upUniG K n)⁻¹).2
    have hr0I : IsInt R (sec_m ((h : upUniG K n)⁻¹)) := hinv.1
    refine ⟨lu_co (sec_m ((h : upUniG K n)⁻¹)), fun p => hr0I _ _, ?_⟩
    have e1 : sec_m (lu_g v) = sec_m u * sec_m ((h : upUniG K n)⁻¹) :=
      congrArg (fun g : upUniG K n => sec_m g) hg
    rw [lu_g_m, ← lu_eq hr0U, lu_mul u.2] at e1
    have e2 := congrArg lu_co e1
    rwa [lu_co_EE, lu_co_EE] at e2
  · rintro q ⟨r, hr, hv⟩
    have e1 : lu_g v = Quotient.out q * lu_g r := by
      apply sec_m_ext
      have : sec_m (Quotient.out q * lu_g r) = sec_m (Quotient.out q) * sec_m (lu_g r) := rfl
      rw [this, lu_g_m, lu_g_m, lu_mul (Quotient.out q).2, ← hv]
    have hmem : lu_g r ∈ intSub R (upUniG K n) :=
      (sec_mem_int R (lu_g r) (isUpUni_det K (lu_up r))).2 (lu_int hr)
    have e2 : ((Quotient.out q : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) =
        ((lu_g v : upUniG K n) : upUniG K n ⧸ intSub R (upUniG K n)) :=
      (sec_left_eq _ _ _).2 ⟨lu_g r, hmem, e1⟩
    rw [← e2]
    exact (QuotientGroup.out_eq' q).symm
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
