-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:20.787812+00:00
-- url     : https://prove2.me/submissions/3c5436c0-8682-4828-b610-002414b219d9

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdempotent
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CentralIdempotentsSumOne
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_CISum_centralIdem_act
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_CISum_isIrr_of_isIrreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_central_idempotent_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open CISum
set_option backward.isDefEq.respectTransparency false
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : CentralIdemSumOne := by
  intro G I _ _ _ V _ _ _ ρ hirr hne hfull
  classical
  set z : MonoidAlgebra ℂ G := ∑ i, centralIdem (ρ i) with hz
  have hcentral : ∀ x : MonoidAlgebra ℂ G, z * x = x * z := by
    intro x
    rw [hz, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (hirr i).1
    exact (central_idempotent_holds G (V i) (ρ i) (hirr i).2).2 x

  have hact : ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (σ : Representation ℂ G W), IsIrr σ → σ.asAlgebraHom z = 1 := by
    intro W _ _ _ σ hσ
    obtain ⟨i₀, φ, hφ⟩ := hfull W σ hσ
    rw [hz, map_sum, Finset.sum_eq_single i₀]
    · rw [centralIdem_act (ρ i₀) σ (hirr i₀) hσ, if_pos]
      exact ⟨(Representation.Equiv.mk φ (fun g => LinearMap.ext fun x => hφ g x)).symm⟩
    · intro i _ hi
      rw [centralIdem_act (ρ i) σ (hirr i) hσ, if_neg]
      rintro ⟨ψ⟩
      apply hi
      apply hne
      refine ⟨ψ.toLinearEquiv.trans φ, fun g x => ?_⟩
      have h1 : ψ (ρ i g x) = σ g (ψ x) := LinearMap.congr_fun (ψ.isIntertwining' g) x
      simp only [LinearEquiv.trans_apply]
      erw [h1]
      exact hφ g _
    · intro h; exact absurd (Finset.mem_univ _) h
  have : NeZero (Nat.card G : ℂ) :=
    ⟨by rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero⟩
  let N : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {x | z * x = x}
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [mul_add, hx, hy]
      zero_mem' := by simp
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_ofPred_eq, smul_eq_mul] at hx ⊢
        rw [← mul_assoc, hcentral a, mul_assoc, hx] }
  have hN : N = ⊤ := by
    rw [eq_top_iff, ← IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ G)
      (MonoidAlgebra ℂ G)]
    apply sSup_le
    intro S hS x hx
    have hS' : IsSimpleModule (MonoidAlgebra ℂ G) S := hS
    have hirrS := (Representation.isSimpleModule_iff_irreducible_ofModule (k := ℂ) (G := G) S).mp hS'
    have hfd : FiniteDimensional ℂ (RestrictScalars ℂ (MonoidAlgebra ℂ G) S) := by
      let ι : RestrictScalars ℂ (MonoidAlgebra ℂ G) S →ₗ[ℂ] MonoidAlgebra ℂ G :=
        { toFun := fun y => ((RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S y : S) :
            MonoidAlgebra ℂ G)
          map_add' := by intro a b; simp
          map_smul' := by
            intro c y
            simp [RestrictScalars.addEquiv_map_smul, Algebra.smul_def] }
      refine Module.Finite.of_injective ι ?_
      intro a b hab
      exact (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).injective (Subtype.ext hab)
    have h1 := hact _ (Representation.ofModule S) (isIrr_of_isIrreducible _ hirrS)
    have h2 := LinearMap.congr_fun h1 ((RestrictScalars.addEquiv _ _ _).symm ⟨x, hx⟩)
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at h2
    have h3 := (RestrictScalars.addEquiv ℂ (MonoidAlgebra ℂ G) S).symm.injective h2
    have h4 : z * x = x := by simpa using congrArg Subtype.val h3
    exact h4
  have h1 : (1 : MonoidAlgebra ℂ G) ∈ N := hN ▸ Submodule.mem_top
  have h2 : z * 1 = 1 := h1
  rwa [mul_one] at h2
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
