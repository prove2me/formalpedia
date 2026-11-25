-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.En.stab_fix_gq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:50:29.622954+00:00
-- url     : https://prove2.me/submissions/3ec4c51c-c5c2-4eac-bd96-b3489569b5c0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutEnFibMem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_bigCellFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_uWbFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res



set_option autoImplicit false
open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.En
namespace Formalism.FourierDecayAlt.P.CutMP.En
theorem _root_.solution {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (q : (Fin r → ℂ) × ℂ) {p : Q.Mx k r × Q.Mx k r} (hp : p ∈ NF.Stab k r z z' μsec q.2) :
    p.1 * bigCell k r q.1 (μsec q.2) * p.2 = bigCell k r q.1 (μsec q.2) := by
  obtain ⟨h1, -, h3⟩ := hp
  obtain ⟨-, hsub, hcomm⟩ := Formalism.FourierDecayAlt.P.TwoByOneBlock.uWbFacts k r
  have hc := hcomm q.1 p.1 (hsub z h1)
  have hf := (Formalism.FourierDecayAlt.P.TwoByOneBlock.bigCellFactor k r q.1 (μsec q.2)).1
  have h3' : p.1 * B2.embWb k r (μsec q.2) * p.2 = B2.embWb k r (μsec q.2) := h3
  rw [hf]
  calc p.1 * (bigCell k r q.1 1 * B2.embWb k r (μsec q.2)) * p.2
      = (p.1 * bigCell k r q.1 1) * B2.embWb k r (μsec q.2) * p.2 := by simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * (p.1 * B2.embWb k r (μsec q.2) * p.2) := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = bigCell k r q.1 1 * B2.embWb k r (μsec q.2) := by rw [h3']
end Formalism.FourierDecayAlt.P.CutMP.En
