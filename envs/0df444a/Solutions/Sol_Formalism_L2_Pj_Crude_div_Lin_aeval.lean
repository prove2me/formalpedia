-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.div_Lin_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:30:46.213355+00:00
-- url     : https://prove2.me/submissions/0f9e645b-684c-43c0-b034-7dfd5a591cb8

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_add
import Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_div_Lin_C

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
theorem _root_.solution {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (Q : MvPolynomial ι k) :
    Lin (cp l) (u l) (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ (MvPolynomial.pderiv l Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, MvPowerSeries.algebraMap_apply]
    simpa using div_Lin_C (cp l) (u l) a
  | add p q hp hq => rw [map_add, div_Lin_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, div_Lin_mul, hp, MvPolynomial.aeval_X, hl, Derivation.leibniz, MvPolynomial.pderiv_X]
    by_cases h : l = i
    · subst h
      simp
      ring
    · simp [h, Pi.single_apply]
      ring
end Formalism.L2.Pj.Crude
