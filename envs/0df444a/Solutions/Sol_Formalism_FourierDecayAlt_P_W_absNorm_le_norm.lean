-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.absNorm_le_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:59.716416+00:00
-- url     : https://prove2.me/submissions/8878016d-9a03-4834-a6fc-1f7760dded4a

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
namespace Formalism.FourierDecayAlt.P.W
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hb : b ≠ 0) (l : E) (hl : l ∈ b) (hl0 : l ≠ 0) :
    (FractionalIdeal.absNorm b : ℝ) ≤ |(Algebra.norm ℚ l : ℝ)| := by
  have hsp : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hl
  have hs0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hl0
  have hbc : b * (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l := by
    rw [← mul_assoc, mul_inv_cancel₀ hb, one_mul]
  have hc1 : b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ 1 := by
    calc b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l ≤ b⁻¹ * b := by
          first
          | exact FractionalIdeal.mul_left_mono _ hsp
          | exact mul_le_mul_left' hsp _
          | exact mul_le_mul' le_rfl hsp
          | exact mul_le_mul_left hsp _
          | (rw [← FractionalIdeal.coe_le_coe, FractionalIdeal.coe_mul, FractionalIdeal.coe_mul]
             exact Submodule.mul_le_mul_right (FractionalIdeal.coe_le_coe.mpr hsp))
      _ = 1 := inv_mul_cancel₀ hb
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hc1
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hs0
    rw [← hbc, ← hI]
    simp
  have key : FractionalIdeal.absNorm b * FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) = |Algebra.norm ℚ l| := by
    rw [← map_mul, hbc, FractionalIdeal.absNorm_span_singleton]
  have hx : (1 : ℚ) ≤ FractionalIdeal.absNorm
      (b⁻¹ * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) l) := by
    rw [← hI, FractionalIdeal.coeIdeal_absNorm]
    have : Ideal.absNorm I ≠ 0 := fun h0 => hI0 (Ideal.absNorm_eq_zero_iff.mp h0)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  have ha : (0 : ℚ) ≤ FractionalIdeal.absNorm b := FractionalIdeal.absNorm_nonneg b
  have hq : (FractionalIdeal.absNorm b : ℚ) ≤ |Algebra.norm ℚ l| := by
    calc (FractionalIdeal.absNorm b : ℚ) = FractionalIdeal.absNorm b * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hx ha
      _ = _ := key
  exact_mod_cast hq
end Formalism.FourierDecayAlt.P.W
