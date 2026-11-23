-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.supp_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:55.371746+00:00
-- url     : https://prove2.me/submissions/68de8cbf-3ee3-4849-a11d-b1358bb50dc8

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LetterAtSuccVal
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Theorems.Thm_Formalism_InvariantFactorPaths_KP_LL_chainEmb_inj

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
theorem _root_.solution {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]}
    {mon : BVar N r D.T.t →₀ ℕ} (hm : mon ∈ (rename (chainEmb N r D.T.t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, mon = Finsupp.mapDomain (chainEmb N r D.T.t) m1 + m2 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  rw [MvPolynomial.support_rename_of_injective chainEmb_inj] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩
end Formalism.InvariantFactorPaths.KP.LL
