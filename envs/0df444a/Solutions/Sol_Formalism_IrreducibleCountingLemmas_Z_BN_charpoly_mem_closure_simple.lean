-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.charpoly_mem_closure_simple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:11:41.589873+00:00
-- url     : https://prove2.me/submissions/37fa9f38-8df7-431a-93b7-456f48bd9b8e

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {k A : Type} [Field k] [Ring A] [Algebra k A] :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module k V] [Module A V] [IsScalarTower k A V]
      [FiniteDimensional k V], Module.finrank k V = n →
      (cp k V : A → k[X]) ∈ Submonoid.closure (simpleCps k A) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ _ _ hn
  by_cases h0 : Module.finrank k V = 0
  · have : (cp k V : A → k[X]) = 1 := by
      funext a
      have hm : (cp k V a).Monic := LinearMap.charpoly_monic _
      have hd : (cp k V a).natDegree = 0 := by
        unfold cp; rw [LinearMap.charpoly_natDegree, h0]
      exact (Polynomial.Monic.natDegree_eq_zero hm).mp hd
    rw [this]; exact one_mem _
  · have hnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := k) (Nat.pos_of_ne_zero h0)
    have hart : IsArtinian A V := isArtinian_of_tower k inferInstance
    obtain ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule A V)
    have hsimp : IsSimpleModule A S := isSimpleModule_iff_isAtom.mpr hS
    have h1 : (cp k V : A → k[X]) = cp k S * cp k (V ⧸ S) := funext (cp_quot S)
    have hlt : Module.finrank k (V ⧸ S) < n := by
      have h2 := congrArg Polynomial.natDegree (congrFun h1 0)
      have hnS : Nontrivial S := IsSimpleModule.nontrivial A S
      have hpos : 0 < Module.finrank k S := Module.finrank_pos
      rw [Pi.mul_apply] at h2
      unfold cp at h2
      rw [Polynomial.Monic.natDegree_mul (LinearMap.charpoly_monic _)
        (LinearMap.charpoly_monic _), LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree,
        LinearMap.charpoly_natDegree] at h2
      omega
    rw [h1]
    exact mul_mem (Submonoid.subset_closure ⟨S, _, _, _, _, _, hsimp, rfl⟩) (ih _ hlt (V ⧸ S) rfl)
end Formalism.IrreducibleCountingLemmas.Z.BN
