-- Prove2me | solution 1 for Formalism.DivisionValues.second_step_refined_weak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:27.31884+00:00
-- url     : https://prove2.me/submissions/c20b4505-2d0c-4f22-9354-c8ba8814599c

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Theorems.Thm_Formalism_DivisionValues_weak_form_b
import Theorems.Thm_Formalism_DivisionValues_lemmaRb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
namespace Formalism.DivisionValues
theorem _root_.solution : StepBRW := by
  intro K _ _ _ _ K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J _ d XW hXW
    M hM HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG n H hH hHpos P hP
    hQ Mt hMt hLamP hGR R hR hRloc
  have hLB0 : ∀ w, IsLocBasis (matLat P Mt) w (e μ0 w) := fun w => hLamP ▸ hLB μ0 w
  have hRb := (lemmaRb K K0 hK0 v0 hv0 n D H hH hHpos P hP (XQ μ0) hQ Mt hMt (e μ0) hLB0).2
  have hbase : lcv (XQ μ0) (abelian₂ μ0) ≤ ∑ᶠ w, lw w * (vw w (G μ0 w) : ℝ) := by
    rw [hLamP]
    simpa only [hGR] using hRb
  exact weak_form_b K K0 hK0 v0 hv0 D XE hXE Tup μ0 μ hμc hμfin XQ hXQ abelian₂ hLam ι hι J d XW hXW M hM
    HT XT hHT0 hHTw T hT θ hθ κ hκ ρ ρr hρr hρ0 hρpos hρv hdet0 hdet G e hLB hG hbase R hR hRloc
end Formalism.DivisionValues
