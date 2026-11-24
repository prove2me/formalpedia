-- Prove2me | solution 1 for Formalism.L2.DIV.lvlOpSpec_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.600463+00:00
-- url     : https://prove2.me/submissions/2352b216-5f61-4658-bcf7-92390ec68f5c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_group_action_matrix_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution (h1 : CutOrthProj) (h2 : LvlIdemSpec) : LvlOpSpec := by
  intro K _ _ _ v0 hv S hpos G _ _ r hr P ψ a ha
  obtain ⟨⟨hI, hS, -, -⟩, -⟩ := h2 K v0 hv G P ψ
  obtain ⟨⟨hPE, -⟩, hEP⟩ := h1 K v0 hv S hpos G r hr (lvlIdem P ψ) hI hS
  have hmul := (group_action_matrix_hom K S G r).2
  have hcomm : S.gaMat r a * S.gaMat r (lvlIdem P ψ) = S.gaMat r (lvlIdem P ψ) * S.gaMat r a := by
    rw [← hmul, ← hmul, ha]
  unfold CSD.lvlOp CSD.lvlE CSD.lvlPr
  set E := S.cutE r (lvlIdem P ψ)
  set Pr := S.cutPr r (lvlIdem P ψ)
  set F := S.gaMat r (lvlIdem P ψ)
  have hFE : F * E = E := by rw [← hEP, Matrix.mul_assoc, hPE, Matrix.mul_one]
  constructor
  · calc E * (Pr * S.gaMat r a * E) = E * Pr * S.gaMat r a * E := by simp only [Matrix.mul_assoc]
      _ = F * S.gaMat r a * E := by rw [hEP]
      _ = S.gaMat r a * F * E := by rw [hcomm]
      _ = S.gaMat r a * (F * E) := Matrix.mul_assoc _ _ _
      _ = S.gaMat r a * E := by rw [hFE]
  · intro b
    rw [hmul]
    symm
    calc Pr * S.gaMat r b * E * (Pr * S.gaMat r a * E) = Pr * S.gaMat r b * (E * Pr) * S.gaMat r a * E := by
          simp only [Matrix.mul_assoc]
      _ = Pr * S.gaMat r b * F * S.gaMat r a * E := by rw [hEP]
      _ = Pr * S.gaMat r b * (F * S.gaMat r a) * E := by simp only [Matrix.mul_assoc]
      _ = Pr * S.gaMat r b * (S.gaMat r a * F) * E := by rw [hcomm]
      _ = Pr * (S.gaMat r b * S.gaMat r a) * (F * E) := by simp only [Matrix.mul_assoc]
      _ = Pr * (S.gaMat r b * S.gaMat r a) * E := by rw [hFE]
end Formalism.L2.DIV
