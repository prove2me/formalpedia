-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.BQuot.quot_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:06:53.699247+00:00
-- url     : https://prove2.me/submissions/2ec1ec78-1723-49d7-9075-f9d7c9e834f4

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ReductionQuotient
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_IdxDet
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_ql_le_of_map
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_BQuot_mem_span_basisFun
import Theorems.Thm_Formalism_LatticeIndexTer_LatticeIndexDeterminant_len_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Module
open Formalism.LatticeBaseChangeAlt.BQuot
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.LatticeBaseChangeAlt.BQuot
theorem _root_.solution (ϖ : O) (hϖ : Irreducible ϖ) (n : ℕ) (c : V →ₗ[K] (Fin n → K))
    (N : Submodule K V) (hN : LinearMap.ker c ≤ N) (X : Submodule O V) (e be : ℕ)
    (th : Fin n → V)
    (hX : ∀ x ∈ X, ∀ i, ∃ a : O,
      c x i = (algebraMap O K ϖ) ^ ((e : ℤ) - (be : ℤ)) * algebraMap O K a)
    (hth : ∀ j, (algebraMap O K ϖ) ^ e • th j ∈ X)
    (a a' : O) (ha : a ≠ 0)
    (hdet : algebraMap O K a = (Matrix.of fun i j => c (th j) i).det * algebraMap O K a') :
    ql X ((X ⊓ N.restrictScalars O) ⊔
        Submodule.span O (Set.range fun j => (algebraMap O K ϖ) ^ e • th j)) +
      IsDiscreteValuationRing.addVal O a' ≤
      IsDiscreteValuationRing.addVal O a + ((n * be : ℕ) : ℕ∞) := by
  set p : K := algebraMap O K ϖ with hp
  have hp0 : p ≠ 0 := by
    rw [hp]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  set Tj : Submodule O V := Submodule.span O (Set.range fun j => p ^ e • th j) with hTj
  have hTX : Tj ≤ X := Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact hth j)
  let b := Pi.basisFun K (Fin n)
  let f : V →ₗ[O] (Fin n → K) := ((p ^ ((be : ℤ) - (e : ℤ))) • c).restrictScalars O
  have hf : ∀ x, f x = p ^ ((be : ℤ) - (e : ℤ)) • c x := fun x => rfl
  let w : Fin n → (Fin n → K) := fun j => f (p ^ e • th j)
  have hw' : ∀ j, w j = p ^ be • c (th j) := by
    intro j
    show f (p ^ e • th j) = _
    rw [hf, map_smul, smul_smul, ← zpow_natCast p e, ← zpow_add₀ hp0, sub_add_cancel,
      zpow_natCast]
  have hfX : ∀ x ∈ X, f x ∈ Submodule.span O (Set.range b) := by
    intro x hx
    apply mem_span_basisFun
    intro i
    obtain ⟨u, hu⟩ := hX x hx i
    refine ⟨u, ?_⟩
    rw [hf, Pi.smul_apply, hu, smul_eq_mul, ← mul_assoc, ← zpow_add₀ hp0]
    simp
  have hmat : b.toMatrix w = p ^ be • (Matrix.of fun i j => c (th j) i) := by
    ext i j
    rw [Basis.toMatrix_apply, hw']
    simp [b]
  have hC0 : (Matrix.of fun i j => c (th j) i).det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdet
    exact ha ((map_eq_zero_iff _ (IsFractionRing.injective O K)).1 hdet)
  have hdw : (b.toMatrix w).det = (p ^ be) ^ n * (Matrix.of fun i j => c (th j) i).det := by
    rw [hmat, Matrix.det_smul, Fintype.card_fin]
  have hdw0 : (b.toMatrix w).det ≠ 0 := by
    rw [hdw]
    exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp0)) hC0
  obtain ⟨e0, he0, hlen⟩ := Formalism.LatticeIndexTer.LatticeIndexDeterminant.len_span (O := O) b w
    (fun j => hfX _ (hth j)) hdw0
  have hle : ql X ((X ⊓ N.restrictScalars O) ⊔ Tj) ≤ IsDiscreteValuationRing.addVal O e0 := by
    rw [← hlen]
    refine ql_le_of_map (f ∘ₗ X.subtype) (fun x => hfX _ x.2) ?_
    intro x hx
    have hx' : f (x : V) ∈ Submodule.span O (Set.range w) := hx
    have hmap : Submodule.span O (Set.range w) = Tj.map f := by
      rw [hTj, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [hmap] at hx'
    obtain ⟨t, ht, htx⟩ := hx'
    have hker : (x : V) - t ∈ LinearMap.ker c := by
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero]
      rw [hf, hf] at htx
      exact (smul_right_injective _ (zpow_ne_zero _ hp0) htx).symm
    have : (x : V) = ((x : V) - t) + t := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨X.sub_mem x.2 (hTX ht), hN hker⟩ ht
  have hrel : e0 * a' = ϖ ^ (n * be) * a := by
    apply IsFractionRing.injective O K
    rw [map_mul, map_mul, map_pow, he0, hdw, hdet, ← hp, ← pow_mul, mul_comm be n]
    ring
  have hval : IsDiscreteValuationRing.addVal O e0 + IsDiscreteValuationRing.addVal O a' =
      IsDiscreteValuationRing.addVal O a + ((n * be : ℕ) : ℕ∞) := by
    rw [← IsDiscreteValuationRing.addVal_mul, hrel, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, add_comm]
    simp
  rw [← hval]
  exact add_le_add hle le_rfl
end Formalism.LatticeBaseChangeAlt.BQuot
