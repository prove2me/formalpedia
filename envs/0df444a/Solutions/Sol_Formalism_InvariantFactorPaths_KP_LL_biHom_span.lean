-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.biHom_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:45.966901+00:00
-- url     : https://prove2.me/submissions/c31c3c5e-24b7-4ddc-b646-1e55b2fc4be9

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_ChainEmbInj
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_BiHomPlus

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}
omit [NeZero r]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxS => exact h x hxS
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h' | h'
    · exact hx m h'
    · exact hy m h'
  | smul a x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)
end Formalism.InvariantFactorPaths.KP.LL
