-- Prove2me | solution 1 for Formalism.UG.P.levelv_nsmul_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:55.782502+00:00
-- url     : https://prove2.me/submissions/64c6c45e-93c0-4ef9-abc0-7b640430430f

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain NumberField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution {N : ℕ} (hN : N ≠ 0) (y y' : n → E ⊗[F] v.adicCompletion F)
    (h : N • y = N • y') : y = y' := by
  funext j
  have hj := congr_fun h j
  simp only [Pi.smul_apply] at hj
  have hu : IsUnit ((N : E ⊗[F] v.adicCompletion F)) := by
    have h0 : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)) N]
    exact (IsUnit.mk0 _ h0).map _
  rw [nsmul_eq_mul, nsmul_eq_mul] at hj
  exact hu.mul_left_cancel hj
end Formalism.UG.P
