-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.xi_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:58.77528+00:00
-- url     : https://prove2.me/submissions/14cff9f6-93b7-4347-be5b-e95a3de5c7c3

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M
open scoped Pointwise
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)
variable {p D}
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m2 : BVar N r D.T.t →₀ ℕ} (hm2 : m2 ∈ g.support) :
    (∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0) ∧ ∑ c, m2 (xiVar N r D.T.t c) = b := by
  have h1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h1
  have h2 := h1 hm2
  refine ⟨fun v hv => ?_, h2.2⟩
  by_contra hne
  obtain ⟨c, hc⟩ := h2.1 v (Finsupp.mem_support_iff.mpr hne)
  exact hv c hc
end Formalism.InvariantFactorPaths.KP.LL
