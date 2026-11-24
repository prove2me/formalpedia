-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_par_bij
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.441941+00:00
-- url     : https://prove2.me/submissions/ff2722cb-1f22-4651-abd0-0758e2321d92

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {i N : ℕ} : Function.Bijective (qc_par (i := i) (N := N)) := by
  constructor
  · rintro ⟨⟨S, hS⟩, σ⟩ ⟨⟨T, hT⟩, τ⟩ h
    have hST : S = T := by
      have h1 : ∀ (S : Finset (Fin N)) (hS : S.card = i) (σ : Equiv.Perm (Fin i)),
          univ.map (qc_par ⟨⟨S, hS⟩, σ⟩) = S := by
        intro S hS σ
        ext x
        simp only [qc_par, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.trans_apply,
          Equiv.coe_toEmbedding, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨a, rfl⟩
          exact Finset.orderEmbOfFin_mem S hS _
        · intro hx
          have : x ∈ Set.range (S.orderEmbOfFin hS) := by
            rw [Finset.range_orderEmbOfFin]; exact hx
          obtain ⟨b, rfl⟩ := this
          exact ⟨σ.symm b, by simp⟩
      rw [← h1 S hS σ, ← h1 T hT τ, h]
    subst hST
    have : σ = τ := by
      ext a
      have h2 := DFunLike.congr_fun h a
      simp only [qc_par, Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        RelEmbedding.coe_toEmbedding] at h2
      exact congrArg Fin.val ((S.orderEmbOfFin hS).injective h2)
    subst this
    rfl
  · intro f
    have hS : (univ.map f).card = i := by simp
    have hmem : ∀ a, f a ∈ Set.range ((univ.map f).orderEmbOfFin hS) := by
      intro a
      rw [Finset.range_orderEmbOfFin]; simp
    choose τ hτ using hmem
    have hinj : Function.Injective τ := by
      intro a b hab
      apply f.injective
      rw [← hτ a, ← hτ b, hab]
    refine ⟨⟨⟨univ.map f, hS⟩, Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hinj)⟩, ?_⟩
    ext a
    simp [qc_par, hτ]
end Formalism.InvariantFactorPaths.ColumnFamilies
