-- Prove2me | solution 1 for Formalism.L2.Col.diagEmb_mulVec_snoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:07.170821+00:00
-- url     : https://prove2.me/submissions/d068cabf-d3cc-45ae-84ca-d044eb78a496

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
variable {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution {n : ℕ} (h : GL (Fin n) κ) (v : Fin n → κ) (c : κ) :
    (diagEmb κ (Nat.le_succ n) h).1.mulVec (Fin.snoc (α := fun _ => κ) v c) =
      Fin.snoc (α := fun _ => κ) (h.1.mulVec v) c := by
  show (diagMat n (n + 1) (h : Matrix (Fin n) (Fin n) κ)).mulVec (Fin.snoc (α := fun _ => κ) v c) = Fin.snoc (α := fun _ => κ) ((h : Matrix (Fin n) (Fin n) κ).mulVec v) c
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, diagMat, Matrix.one_apply, (Fin.castSucc_lt_last i).ne]
end Formalism.L2.Col
