-- Prove2me | solution 1 for Eden.blockRotation_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:08.169507+00:00
-- url     : https://prove2.me/submissions/987a15e4-ce83-4e2f-9ac9-47d98ddd94f0

import Definitions.Def_Eden_Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Eden_OrthogonalFrames

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (a b d e : ℝ) (h₁ : a ^ 2 + b ^ 2 = 1)
    (h₂ : d ^ 2 + e ^ 2 = 1) (v : PhaseSpace) :
    blockRotation a b d e h₁ h₂ v = rotateBlocks a b d e v := rfl
end Eden
