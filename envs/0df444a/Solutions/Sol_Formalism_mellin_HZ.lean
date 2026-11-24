-- Prove2me | solution 1 for Formalism.mellin_HZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:33:29.832799+00:00
-- url     : https://prove2.me/submissions/78eeb071-d585-43d8-910b-12927a3b378e

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_mellin_Gz_n
import Theorems.Thm_Formalism_cint_of_abs
import Theorems.Thm_Formalism_int_abs_rpow
import Theorems.Thm_Formalism_mellin_Gz


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution (h3 : MellinSgen) (h5 : MellinElem) {ε C θ : ℝ} (hθ : θ < 1)
    {s : ℂ} (hs : 1 < s.re) :
    IZ ε C θ s = ε * nZ s / (s * (s - 1)) + C / (s - θ) := by
  have iz := (mellin_Gz h3 h5 hs).1
  have i4 : IntegrableOn (fun x : ℝ => ((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) :=
    cint_of_abs _ (by fun_prop) s (int_abs_rpow h5 (by linarith))
  have hfun : (fun x : ℝ => ((HZ ε C θ x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) = fun x =>
      (ε : ℂ) * ((Gz x : ℂ) * (x : ℂ) ^ (-s - 1))
        + (C : ℂ) * (((x ^ θ : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [HZ]
    push_cast
    ring
  unfold IZ
  rw [hfun, integral_add (Integrable.const_mul iz _) (Integrable.const_mul i4 _),
    integral_const_mul, integral_const_mul, mellin_Gz_n h3 h5 hs, h5.2.2.1 θ s (by linarith)]
  ring
end Formalism
