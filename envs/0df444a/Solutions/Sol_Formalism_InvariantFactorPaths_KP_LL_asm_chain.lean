-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.asm_chain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:48.786299+00:00
-- url     : https://prove2.me/submissions/4cd2ac18-1ff5-4d82-b68f-f4a88bd7256b

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LevelLatticeOf

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
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (M : ℕ → Submodule ℤ_[p] V) (u t : ℕ)
    (h : ∀ k < t, (∀ v ∈ M (k + 1), (p : ℚ_[p]) ^ u • v ∈ M k) ∧ (∀ v ∈ M k, (p : ℚ_[p]) ^ u • v ∈ M (k + 1))) :
    ∀ k ≤ t, (∀ v ∈ M k, (p : ℚ_[p]) ^ (k * u) • v ∈ M 0) ∧ (∀ v ∈ M 0, (p : ℚ_[p]) ^ (k * u) • v ∈ M k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨s1, s2⟩ := h k (by omega)
    constructor
    · intro v hv
      have := i1 _ (s1 v hv)
      rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
    · intro v hv
      have := s2 _ (i2 v hv)
      rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this
end Formalism.InvariantFactorPaths.KP.LL
