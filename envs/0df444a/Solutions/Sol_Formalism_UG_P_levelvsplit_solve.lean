-- Prove2me | solution 1 for Formalism.UG.P.levelvsplit_solve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:55.454921+00:00
-- url     : https://prove2.me/submissions/941d48e8-ad04-4185-a6a0-63b92503a27a

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
variable {B K : Type} [CommRing B] [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (A Ainv P1 P1i P2 : Matrix n n K) (hA : A * Ainv = 1)
    (hP : P1 * P1i = 1) (hrel : P2ᵀ * A * P1 = A) : P2 = (A * P1i * Ainv)ᵀ := by
  have h1 : P2ᵀ * A = A * P1i := by
    calc P2ᵀ * A = P2ᵀ * A * (P1 * P1i) := by rw [hP, Matrix.mul_one]
      _ = P2ᵀ * A * P1 * P1i := by simp only [Matrix.mul_assoc]
      _ = A * P1i := by rw [hrel]
  have h2 : P2ᵀ = A * P1i * Ainv := by
    calc P2ᵀ = P2ᵀ * (A * Ainv) := by rw [hA, Matrix.mul_one]
      _ = P2ᵀ * A * Ainv := by rw [Matrix.mul_assoc]
      _ = A * P1i * Ainv := by rw [h1]
  rw [← h2, Matrix.transpose_transpose]
end Formalism.UG.P
