-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.UnipotentSums.mX_apply_Xs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:41.521246+00:00
-- url     : https://prove2.me/submissions/0ac05f23-fb22-4668-8722-e91479543d7d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.UnipotentSums
theorem _root_.solution (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (esI k r c) j = if hj : r + k < j.val then (vXᴴ)⁻¹ c ⟨2 * r + k - j.val, by omega⟩ else 0 := by
  have hc := c.isLt
  have h1 : ¬ (esI k r c).val < r := by show ¬ 2 * r + k - c.val < r; omega
  have h2 : r + k < (esI k r c).val := by show r + k < 2 * r + k - c.val; omega
  simp only [C2.mX]
  rw [dif_neg h1, dif_pos h2]
  by_cases hj : r + k < j.val
  · rw [dif_pos hj, dif_pos hj]
    have e : (⟨2 * r + k - (esI k r c).val, by omega⟩ : Fin r) = c :=
      Fin.ext (by show 2 * r + k - (2 * r + k - c.val) = c.val; omega)
    rw [e]
  · rw [dif_neg hj, dif_neg hj]
end Formalism.FourierDecayAlt.P.UnipotentSums
