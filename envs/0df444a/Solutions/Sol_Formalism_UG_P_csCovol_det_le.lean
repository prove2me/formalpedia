-- Prove2me | solution 1 for Formalism.UG.P.csCovol_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:09.255964+00:00
-- url     : https://prove2.me/submissions/beeb0e04-4c03-4d97-9285-62cbd0ed2d5a

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {N : ℕ} (G : Matrix (Fin N) (Fin N) ℚ) (hG : 0 < G.det) (D : ℤ) (hD0 : D ≠ 0)
    (P : Matrix (Fin N) (Fin N) ℤ) (hP : G * P.map (Int.cast : ℤ → ℚ) = (D : ℚ) • 1) :
    G.det ≤ (|D| : ℚ) ^ N := by
  have hdet := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hPd : ((P.det : ℤ) : ℚ) = (P.map (Int.cast : ℤ → ℚ)).det := (Int.castRingHom ℚ).map_det P
  rw [← hPd] at hdet
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, Int.cast_zero, mul_zero] at hdet
    exact pow_ne_zero N (Int.cast_ne_zero.mpr hD0) hdet.symm
  have h1 : (1 : ℚ) ≤ |(P.det : ℚ)| := by
    have : (1 : ℤ) ≤ |P.det| := Int.one_le_abs hP0
    exact_mod_cast this
  have habs := congrArg abs hdet
  rw [abs_mul, abs_of_pos hG, abs_pow] at habs
  have key : G.det ≤ |(D : ℚ)| ^ N :=
    calc G.det = G.det * 1 := (mul_one _).symm
      _ ≤ G.det * |(P.det : ℚ)| := mul_le_mul_of_nonneg_left h1 hG.le
      _ = |(D : ℚ)| ^ N := habs
  simpa using key
end Formalism.UG.P
