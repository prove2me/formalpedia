-- Prove2me | solution 1 for Formalism.CountingSumsFrames.ycond_glStable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:17.514321+00:00
-- url     : https://prove2.me/submissions/5ff9a05a-4317-4b81-add2-888f2388344e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ YCond p (r := r) LL j Mt, glAct p LL j c d x ∈ YCond p (r := r) LL j Mt := by
  unfold YCond
  intro x hx
  have : sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S} ≤
      (sSup {S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) |
      S ≤ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧ GlStable p LL j S}).comap
        (glAct p LL j c d) :=
    sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
  exact this hx
end Formalism.CountingSumsFrames
