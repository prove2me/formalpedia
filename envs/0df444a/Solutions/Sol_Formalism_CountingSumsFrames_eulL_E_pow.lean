-- Prove2me | solution 1 for Formalism.CountingSumsFrames.eulL_E_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:31.331101+00:00
-- url     : https://prove2.me/submissions/aabb20c9-6158-4686-aeb0-989434684edf

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
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.CountingSumsFrames
theorem _root_.solution {σ : Type} {r : ℕ} (t w e : Fin r → σ) (h : ∀ (g : MvPolynomial σ ℚ_[p]) (α : ℚ_[p]),
    ProjS.eulL t g = α • g → ProjS.eulL t ((∑ d, X (w d) * X (e d)) * g) = (α + 1) • ((∑ d, X (w d) * X (e d)) * g))
    (g : MvPolynomial σ ℚ_[p]) (α : ℚ_[p]) (hg : ProjS.eulL t g = α • g) (l : ℕ) :
    ProjS.eulL t ((tieE w e ^ l) g) = (α + l) • (tieE w e ^ l) g := by
  induction l with
  | zero => simpa using hg
  | succ l ih =>
    rw [pow_succ', Module.End.mul_apply]
    show ProjS.eulL t ((∑ d, X (w d) * X (e d)) * (tieE w e ^ l) g) = _
    rw [h _ _ ih]
    push_cast; rw [add_assoc]; rfl
end Formalism.CountingSumsFrames
