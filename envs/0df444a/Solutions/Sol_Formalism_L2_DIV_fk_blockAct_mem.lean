-- Prove2me | solution 1 for Formalism.L2.DIV.fk_blockAct_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:41.09024+00:00
-- url     : https://prove2.me/submissions/1904084f-b5c5-4996-aed3-71ce3502b823

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_C_mem
import Theorems.Thm_Formalism_L2_DIV_fk_X_mem
import Theorems.Thm_Formalism_L2_DIV_blockAct_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K0)
    {P : MvPolynomial (ι × Fin n × Fin n) K} (hP : P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact fk_C_mem K0 a.2
  | add p q hp hq =>
    rw [map_add (map K0.subtype), map_add]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (map K0.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (fk_C_mem K0 (hU _ _ _)) (fk_X_mem K0 _))
end Formalism.L2.DIV
