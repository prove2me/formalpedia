-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.top_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:36.824612+00:00
-- url     : https://prove2.me/submissions/a397ed46-045c-48b9-ab07-1d7a86a60caf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_inv_bounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_one_add
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (ψ : AddChar K ℂ) (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) :
    ∃ ϖ : Kˣ, (ϖ : K) ∈ R ∧ (∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) ∧
      (∀ r ∈ R, ∃ y ∈ R, (1 + (ϖ : K) * r) * y = 1) ∧
      ∀ Q : Set K, IsCompact Q → (∀ d ∈ Q, IsUnit d) →
        ∃ k : ℕ, ∀ d ∈ Q, (ϖ : K) ^ k * Ring.inverse d ∈ R := by
  obtain ⟨ϖ, hϖ, hex⟩ := hD.unif
  have hpq : (ϖ : K) * ((ϖ⁻¹ : Kˣ) : K) = 1 := by simp
  refine ⟨ϖ, hϖ, hex, fun r hr => ?_, fun Q hQ hu => ?_⟩
  · obtain ⟨w, h1, _, h3⟩ := A6x4.one_add hD hn hpq hϖ hex hr
    exact ⟨w, h3, h1⟩
  · exact A6x4.inv_bounded hD hn hpq hϖ hex hQ hu
end Formalism.FourierDecayAlt.P.TwoBlockPoint
