-- Prove2me | solution 1 for Formalism.LatticeIndexTer.subgroupData.qlen_ne_top_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:16:12.188219+00:00
-- url     : https://prove2.me/submissions/b60d72e9-15ac-485e-99d3-b40e46db8444

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Pointwise
noncomputable section
open Formalism Formalism.LatticeIndexTer Formalism.LatticeIndexTer.subgroupData
variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
namespace Formalism.LatticeIndexTer.subgroupData
theorem _root_.solution {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] [Module.IsTorsionFree O X] (ϖ : O) (hϖ : Irreducible ϖ) (k : ℕ)
    (A B : Submodule O X) (hA : A.FG) (hk : ∀ a ∈ A, ϖ ^ k • a ∈ B) : qlen O X A B ≠ ⊤ := by
  show Module.length O (A ⧸ B.comap A.subtype) ≠ ⊤
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := A)
  let ψ : (Fin n → O) →ₗ[O] A ⧸ B.comap A.subtype :=
    (B.comap A.subtype).mkQ ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective _).comp b.equivFun.symm.surjective
  let P : Submodule O (Fin n → O) := Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ k})
  have hP : P ≤ LinearMap.ker ψ := by
    intro x hx
    choose y hy using fun i =>
      Ideal.mem_span_singleton.mp (Submodule.mem_pi.mp hx i (Set.mem_univ i))
    have hxy : x = ϖ ^ k • y := funext fun i => by simp [hy i]
    rw [LinearMap.mem_ker, hxy, map_smul]
    set m : A := b.equivFun.symm y
    rw [show ψ y = Submodule.Quotient.mk m from rfl, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    simp only [Submodule.coe_subtype, SetLike.val_smul]
    exact hk _ m.2
  have hsurj : Function.Surjective (P.liftQ ψ hP) := by
    intro z
    obtain ⟨w, hw⟩ := hψ z
    exact ⟨Submodule.Quotient.mk w, hw⟩
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)
  rw [(Submodule.quotientPi (fun _ : Fin n => Ideal.span {ϖ ^ k})).length_eq, Module.length_pi]
  have : Ideal.span {ϖ ^ k} = IsLocalRing.maximalIdeal O ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ne_eq]
  rw [← Nat.cast_mul]
  exact ENat.natCast_ne_top _
end Formalism.LatticeIndexTer.subgroupData
