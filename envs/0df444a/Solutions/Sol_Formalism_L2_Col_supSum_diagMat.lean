-- Prove2me | solution 1 for Formalism.L2.Col.supSum_diagMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:54:52.899701+00:00
-- url     : https://prove2.me/submissions/9bb610fb-31ba-4dad-8bf8-ec5dd63a9cff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (S : Finset ℕ) (g : Matrix (Fin s) (Fin s) κ) :
    supSum a S (diagMat s n g) = supSum a S g := by
  unfold supSum
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
  · intro i hi
    have his : s ≤ i.val := by
      by_contra hh
      exact hi ⟨⟨i.val, by omega⟩, rfl⟩
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hc
    have := hc.1
    have := hc.2.1
    omega
  · intro i
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro j hj
      have hjs : s ≤ j.val := by
        by_contra hh
        exact hj ⟨⟨j.val, by omega⟩, rfl⟩
      rw [if_neg]
      intro hc
      have := hc.2.1
      omega
    · intro j
      simp only [Fin.coe_castLE]
      split_ifs
      · simp [diagMat]
      · rfl
end Formalism.L2.Col
