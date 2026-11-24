-- Prove2me | solution 1 for Formalism.REAL.complexified_derivative_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:40.615808+00:00
-- url     : https://prove2.me/submissions/91aef3ba-f9c1-4dc2-bd7e-502f68411be3

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_real_part_sub
import Theorems.Thm_Formalism_REAL_imaginary_part_sub
import Theorems.Thm_Formalism_REAL_right_derivative_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.REAL
theorem _root_.solution (hc : CpartMem) (hl : RdLin) {n : ℕ} {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → ℂ} {g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnG ε f)
    (hg : inUJ ε g) (Z W : Matrix (Fin n) (Fin n) ℂ) :
    Ec ε (Z - W) f g = Ec ε Z f g - Ec ε W f g := by
  obtain ⟨hZ1, hZ2, -, -⟩ := hc n ε Z
  obtain ⟨hW1, hW2, -, -⟩ := hc n ε W
  unfold Ec
  rw [real_part_sub, imaginary_part_sub, right_derivative_sub hl hf hZ1 hW1 hg, right_derivative_sub hl hf hZ2 hW2 hg]
  ring
end Formalism.REAL
