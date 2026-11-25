-- Prove2me | solution 1 for Formalism.L2.Col.lamXm_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:24:08.269482+00:00
-- url     : https://prove2.me/submissions/56f1fd58-22b5-4331-8d77-e19f602e682f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_lamXm_diagEmb

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
theorem _root_.solution (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) (n' r t m : ℕ) (hn : n' = r + m * t) (h : ↥(HJ κ n' r t m))
    (hm : diagEmb κ (Nat.le_succ n') h.1 ∈ HXm κ (n' + 1) r t m) :
    lamXm ψ χ (n' + 1) r t m ⟨_, hm⟩ = lamJ ψ χ n' r t m h := by
  subst hn
  exact lamXm_diagEmb ψ χ r t m h
end Formalism.L2.Col
