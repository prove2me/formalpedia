-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.asm_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:51.85584+00:00
-- url     : https://prove2.me/submissions/17f87b3f-da21-4e62-9b5e-bb7ae1238cee

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
    (A B : Submodule ℤ_[p] V) (K : ℕ) (h : ∀ v ∈ A, (p : ℚ_[p]) ^ K • v ∈ B) :
    Submodule.span ℚ_[p] (A : Set V) ≤ Submodule.span ℚ_[p] (B : Set V) := by
  have hp : ((p : ℚ_[p]) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [Submodule.span_le]
  intro x hx
  have h1 : (p : ℚ_[p]) ^ K • x ∈ Submodule.span ℚ_[p] (B : Set V) := Submodule.subset_span (h x hx)
  have h2 := Submodule.smul_mem _ (((p : ℚ_[p]) ^ K)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h2
end Formalism.InvariantFactorPaths.KP.LL
