-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GLRed.red_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:18.923101+00:00
-- url     : https://prove2.me/submissions/07eb446d-670d-45a1-8e06-52b3cccd3af1

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_red_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GLRed_nontriv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Set Pointwise
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.GLRed
variable {F : Type} [Field F] (O : Subring F) {a : ℕ}
variable (a)
variable (ϖ : F) (hϖ : ϖ ∈ O)
variable {a}
variable (a)
namespace Formalism.DoubleCosetMeasures.P.GLRed
theorem _root_.solution (hloc : IsLocalAt O ϖ) : Function.Surjective (red O a ϖ hϖ) := by
  intro gb
  have := nontriv O ϖ hϖ hloc
  let G0 : Matrix (Fin a) (Fin a) O := fun i j => (Ideal.Quotient.mk_surjective (gb.val i j)).choose
  have hG0 : ∀ i j, Ideal.Quotient.mk _ (G0 i j) = gb.val i j := fun i j =>
    (Ideal.Quotient.mk_surjective (gb.val i j)).choose_spec
  have hG0' : G0.map (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)})) = gb.val := by
    ext i j; exact hG0 i j
  have hdet : Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) G0.det = gb.val.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hG0']
  have hdetu : IsUnit (Ideal.Quotient.mk (Ideal.span {(⟨ϖ, hϖ⟩ : O)}) G0.det) := by
    rw [hdet]; exact (Matrix.isUnit_iff_isUnit_det _).mp gb.isUnit
  have hnot : G0.det ∉ Ideal.span {(⟨ϖ, hϖ⟩ : O)} := fun h => by
    rw [← Ideal.Quotient.eq_zero_iff_mem] at h; rw [h] at hdetu; exact not_isUnit_zero hdetu
  have hnot' : ∀ o ∈ O, (G0.det : F) ≠ ϖ * o := by
    intro o ho he; apply hnot; rw [Ideal.mem_span_singleton']
    exact ⟨⟨o, ho⟩, Subtype.ext (by simp [he, mul_comm])⟩
  have hinv : (G0.det : F)⁻¹ ∈ O := hloc.2 _ G0.det.2 hnot'
  have hne : (G0.det : F) ≠ 0 := by simpa using hnot' 0 O.zero_mem
  have hu : IsUnit G0.det :=
    ⟨⟨G0.det, ⟨_, hinv⟩, Subtype.ext (by simp [hne]), Subtype.ext (by simp [hne])⟩, rfl⟩
  let U : GL (Fin a) O := ((Matrix.isUnit_iff_isUnit_det G0).mpr hu).unit
  let g : GL (Fin a) F := Matrix.GeneralLinearGroup.map O.subtype U
  have hg : g ∈ GLint O a := by
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact ((U : Matrix (Fin a) (Fin a) O) i j).2
    · rw [← map_inv]; exact (((U⁻¹ : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) i j).2
  refine ⟨⟨g, hg⟩, ?_⟩
  apply Units.ext; ext i j
  rw [red_val]
  exact hG0 i j
end Formalism.DoubleCosetMeasures.P.GLRed
