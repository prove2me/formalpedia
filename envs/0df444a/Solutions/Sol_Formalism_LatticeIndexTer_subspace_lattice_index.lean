-- Prove2me | solution 1 for Formalism.LatticeIndexTer.subspace_lattice_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:18:13.561312+00:00
-- url     : https://prove2.me/submissions/30133988-028e-461e-aa70-2e7e55f23bb9

import Definitions.Def_Formalism_LogFactorialIndices_StatementIdx
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ChainLength
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsPowSmulMem
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_SubspaceLatticeIndex
import Theorems.Thm_P2M_Formalism_LatticeIndexTer_subgroupData_length_chain__bd85a5aaefa7
import Theorems.Thm_Formalism_LatticeIndexTer_subgroupData_length_le_of_le

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
open Formalism Formalism.LatticeIndexTer
open Formalism.LatticeIndexTer.subgroupData
namespace Formalism.LatticeIndexTer
theorem _root_.solution : SubspaceIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ F M Θ hM hΘ W MW ΘW
  have hΘM : Θ ≤ M := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hx)
    exact M.smul_mem _ hy
  have hMW : MW ≤ M := inf_le_left
  have h1 : Θ ≤ Θ ⊔ MW := le_sup_left
  have h2 : Θ ⊔ MW ≤ M := sup_le hΘM hMW
  rw [length_chain' h1 h2]
  have hA : Module.length O (MW ⧸ ΘW.comap MW.subtype) ≤
      Module.length O (↥(Θ ⊔ MW) ⧸ Θ.comap (Θ ⊔ MW).subtype) :=
    length_le_of_le le_sup_right inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  refine add_le_add hA ?_

  have : Module.IsTorsionFree O (X ⧸ W) := .trans_faithfulSMul O K (X ⧸ W)
  let q : X →ₗ[O] X ⧸ W := W.mkQ.restrictScalars O
  let N : Submodule O (X ⧸ W) := M.map q
  have : Module.Finite O N := Module.Finite.iff_fg.mpr (hM.1.map q)
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := N)
  have hNle : ∀ y : N, (y : X ⧸ W) ∈ Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) := by
    intro y
    rw [← b.sum_repr y]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨x, rfl⟩ := W.mkQ_surjective z
    have hx : x ∈ Submodule.span K (M : Set X) := hM.2 ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hNle ⟨q y, Submodule.mem_map_of_mem hy⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  have hd : Module.finrank K X - Module.finrank K W ≤ n := by
    have e1 := Submodule.finrank_quotient_add_finrank W
    have e2 := finrank_range_le_card (R := K) (fun i => ((b i : N) : X ⧸ W))
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at e2
    omega

  let I : Ideal O := Ideal.span {ϖ ^ F}
  let φ : M →ₗ[O] N := q.submoduleMap M
  let π : (Fin n → O) →ₗ[O] (Fin n → O ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ LinearMap.proj i
  let ψ : M →ₗ[O] (Fin n → O ⧸ I) := π ∘ₗ b.equivFun.toLinearMap ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro y
    choose c hc using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨m, hm⟩ := LinearMap.submoduleMap_surjective q M (b.equivFun.symm c)
    refine ⟨m, ?_⟩
    have hm' : φ m = b.equivFun.symm c := hm
    funext i
    simp only [ψ, LinearMap.comp_apply, hm', LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp only [π, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.mkQ_apply]
    exact hc i
  have hker : (Θ ⊔ MW).comap M.subtype ≤ LinearMap.ker ψ := by
    intro m hm
    rw [Submodule.mem_comap] at hm
    obtain ⟨θ, hθ, w, hw, hsum⟩ := Submodule.mem_sup.mp hm
    have hm' : m = ⟨θ, hΘM hθ⟩ + ⟨w, hMW hw⟩ := Subtype.ext (by simp [hsum])
    rw [LinearMap.mem_ker, hm', map_add]
    have hw0 : φ ⟨w, hMW hw⟩ = 0 := by
      apply Subtype.ext
      simp only [φ, ZeroMemClass.coe_zero]
      exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_inf.mp hw).2
    have hw0' : ψ ⟨w, hMW hw⟩ = 0 := by
      simp only [ψ, LinearMap.comp_apply, hw0, map_zero]
    have hθ0 : ψ ⟨θ, hΘM hθ⟩ = 0 := by
      obtain ⟨y, hy, hyθ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hθ)
      have hsm : (⟨θ, hΘM hθ⟩ : M) = ϖ ^ F • ⟨y, hy⟩ := Subtype.ext hyθ.symm
      rw [hsm, map_smul]
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply]
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective I (ψ ⟨y, hy⟩ i)
      rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [hθ0, hw0', add_zero]
  have hsurj : Function.Surjective (((Θ ⊔ MW).comap M.subtype).liftQ ψ hker) := by
    intro z
    obtain ⟨m, hm⟩ := hψ z
    exact ⟨Submodule.Quotient.mk m, hm⟩
  have hlen : Module.length O (Fin n → O ⧸ I) = ((n * F : ℕ) : ℕ∞) := by
    rw [Module.length_pi]
    have : I = IsLocalRing.maximalIdeal O ^ F := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  refine le_trans ?_ (Module.length_le_of_surjective _ hsurj)
  rw [hlen]
  exact_mod_cast (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left F hd)
end Formalism.LatticeIndexTer
