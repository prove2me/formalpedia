-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_iter_pderiv_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:14:48.531814+00:00
-- url     : https://prove2.me/submissions/3f69eef6-58b2-4562-8c4e-53340d376dff

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : s - Finsupp.single i t - Finsupp.single i 1 = s - Finsupp.single i (t + 1) := by
      ext j
      first
        | (simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp [Finsupp.single_apply]; split_ifs <;> omega)
    have h2 : (s - Finsupp.single i t) i = s i - t := by
      first
        | simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        | simp
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial, h1, h2,
      Nat.descFactorial_succ]
    congr 1
    push_cast
    ring
end Formalism.L2.Pj.Crude
