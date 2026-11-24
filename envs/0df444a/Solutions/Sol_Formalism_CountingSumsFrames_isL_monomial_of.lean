-- Prove2me | solution 1 for Formalism.CountingSumsFrames.isL_monomial_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:19.870819+00:00
-- url     : https://prove2.me/submissions/38f5327f-a531-4620-9fcb-447bed15fe89

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (j0 : ℕ) (b : Fin N × Fin r →₀ ℕ) (hb : ∀ v : Fin N × Fin r, (v.1 : ℕ) < j0 → b v = 0) (a : ℚ_[p]) :
    IsL (fsj N r j0) (monomial b a) := by
  intro m hm v hv hlt
  have e := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at e
  subst e
  exact hv (hb v hlt)
end Formalism.CountingSumsFrames
