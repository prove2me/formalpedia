-- Prove2me | solution 1 for Formalism.REAL.complexified_derivative_commutator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:57:39.87012+00:00
-- url     : https://prove2.me/submissions/aa3925cd-221d-4d87-8dd4-7592defc6ccb

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Theorems.Thm_Formalism_REAL_lie_algebra_bracket_mem
import Theorems.Thm_Formalism_REAL_lie_algebra_add_mem_matrix
import Theorems.Thm_Formalism_REAL_lie_algebra_sub_mem
import Theorems.Thm_Formalism_REAL_complex_parts_unique
import Theorems.Thm_Formalism_REAL_commutator_complex_expand
import Theorems.Thm_Formalism_REAL_right_derivative_add
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
theorem _root_.solution (hc : CpartMem) (hl : RdLin) (hb : RdBracket) (hs : RdSmooth) {n : ℕ}
    (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (Z W g : Matrix (Fin n) (Fin n) ℂ)
    (hf : SmoothOnG ε f) (hg : inUJ ε g) :
    Ec ε Z (Ec ε W f) g - Ec ε W (Ec ε Z f) g = Ec ε (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2, hZ, -⟩ := hc n ε Z
  obtain ⟨hY1, hY2, hW, -⟩ := hc n ε W
  have hEc : ∀ (Z' : Matrix (Fin n) (Fin n) ℂ) (f' : Matrix (Fin n) (Fin n) ℂ → ℂ),
      Ec ε Z' f' g = Rd (cpart1 ε Z') f' g + Complex.I * Rd (cpart2 ε Z') f' g := fun _ _ => rfl
  have hE : ∀ V, inG ε V → ∀ W' : Matrix (Fin n) (Fin n) ℂ,
      Rd V (Ec ε W' f) g = Rd V (Rd (cpart1 ε W') f) g + Complex.I * Rd V (Rd (cpart2 ε W') f) g :=
    fun V hV W' => (hl n ε _ _ V V 0 Complex.I g (hs n ε f _ hf (hc n ε W').1)
      (hs n ε f _ hf (hc n ε W').2.1) hV hV hg).2.2
  have hZW := commutator_complex_expand (cpart1 ε Z) (cpart2 ε Z) (cpart1 ε W) (cpart2 ε W)
  rw [← hZ, ← hW] at hZW
  have hP := lie_algebra_sub_mem (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2)
  have hQ := lie_algebra_add_mem_matrix (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1)
  obtain ⟨h1, h2⟩ := complex_parts_unique hP hQ
  rw [hEc Z, hEc W, hE _ hX1, hE _ hX2, hE _ hY1, hE _ hY2, hZW, hEc, h1, h2,
    right_derivative_sub hl hf (lie_algebra_bracket_mem hX1 hY1) (lie_algebra_bracket_mem hX2 hY2) hg,
    right_derivative_add hl hf (lie_algebra_bracket_mem hX1 hY2) (lie_algebra_bracket_mem hX2 hY1) hg,
    ← hb n ε f _ _ g hf hX1 hY1 hg, ← hb n ε f _ _ g hf hX2 hY2 hg,
    ← hb n ε f _ _ g hf hX1 hY2 hg, ← hb n ε f _ _ g hf hX2 hY1 hg]
  linear_combination (Rd (cpart2 ε Z) (Rd (cpart2 ε W) f) g -
    Rd (cpart2 ε W) (Rd (cpart2 ε Z) f) g) * Complex.I_mul_I
end Formalism.REAL
