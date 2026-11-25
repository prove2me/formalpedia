-- Prove2me | solution 1 for Formalism.L2.Col.HXm_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:04.762877+00:00
-- url     : https://prove2.me/submissions/7e807d92-0933-42f3-a2bd-7fa78fe04c6d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_HXm_eq_map

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
theorem _root_.solution (r t m : ℕ) :
    (HXm κ (r + m * t + 1) r t m).comap (diagEmb κ (Nat.le_succ (r + m * t))) = HJ κ (r + m * t) r t m := by
  have h1 : ∀ (X : GL (Fin (r + m * t)) κ) (i j : Fin (r + m * t)),
      ((diagEmb κ (Nat.le_succ (r + m * t)) X : GL (Fin (r + m * t + 1)) κ) : Matrix (Fin (r + m * t + 1)) (Fin (r + m * t + 1)) κ) i.castSucc j.castSucc =
        (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i j := by
    intro X i j
    show diagMat (r + m * t) (r + m * t + 1) (X : Matrix (Fin (r + m * t)) (Fin (r + m * t)) κ) i.castSucc j.castSucc = _
    simp [diagMat]
  have inj : Function.Injective (diagEmb κ (Nat.le_succ (r + m * t))) := by
    intro g g' he
    apply Units.ext
    ext i j
    rw [← h1 g i j, ← h1 g' i j, he]
  rw [HXm_eq_map, Subgroup.comap_map_eq_self_of_injective inj]
end Formalism.L2.Col
