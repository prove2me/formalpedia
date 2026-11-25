-- Prove2me | solution 1 for Formalism.L2.Col.lamJ_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:07:11.584389+00:00
-- url     : https://prove2.me/submissions/ba26b727-0705-4287-80d9-9439dd1a4865

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
theorem _root_.solution {ψ : AddChar κ K} (hψ : ψ ≠ 1) (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (t j : ℕ) (hr : 2 ≤ r) (hn : r ≤ n) :
    lamJ ψ χ n r t j ≠ 1 := by
  unfold lamJ
  exact lamGen_ne_one hψ χ _ (i₀ := 0) (Finset.mem_range.mpr (by omega)) (by omega) hn
end Formalism.L2.Col
