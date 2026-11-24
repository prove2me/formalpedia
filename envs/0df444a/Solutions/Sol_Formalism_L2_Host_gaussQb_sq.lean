-- Prove2me | solution 1 for Formalism.L2.Host.gaussQb_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:57:13.945364+00:00
-- url     : https://prove2.me/submissions/e83f0ce5-d33c-4336-b7ef-c7202b615c67

import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_Lemmas
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IntermediateField NumberField
open Formalism Formalism.L2 Formalism.L2.Host
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable (q : ℕ) [Fact q.Prime]
variable {q}
namespace Formalism.L2.Host
theorem _root_.solution (hq : q % 4 = 3) {w : Qb} (hw : IsPrimitiveRoot w q) :
    gaussQb q hw ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  have hq2 : ringChar (ZMod q) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]; rintro rfl; omega
  have hχ₁ : chiQb q ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hq2
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    show ((quadraticChar (ZMod q) a : ℤ) : Qb) ≠ 1
    rw [ha]; norm_num
  have hχ₂ : (chiQb q).IsQuadratic := MulChar.IsQuadratic.comp (quadraticChar_isQuadratic (ZMod q)) _
  have hψ : (psiQb q hw).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root q hw
  have h := gaussSum_sq hχ₁ hχ₂ hψ
  unfold gaussQb
  rw [h, ZMod.card]
  show ((quadraticChar (ZMod q) (-1) : ℤ) : Qb) * _ = _
  rw [quadraticChar_neg_one hq2, ZMod.card, ZMod.χ₄_nat_three_mod_four hq]
  push_cast; ring
end Formalism.L2.Host
