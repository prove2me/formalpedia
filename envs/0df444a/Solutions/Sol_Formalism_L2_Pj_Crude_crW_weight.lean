-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crW_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:42.740575+00:00
-- url     : https://prove2.me/submissions/7a648774-1cc9-4d86-9a42-de74e6db6973

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (m : Letter T r n →₀ ℕ) (σ : T) (i : Fin (r σ)) :
    Finsupp.weight (crW (r := r) (n := n) σ i.val) m = ∑ b : Fin n, m ⟨σ, i, b⟩ := by
  classical
  have hinj : Function.Injective (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)) := by
    intro b b' h
    exact (Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).2
  have hw : ∀ ℓ : Letter T r n, crW (r := r) (n := n) σ i.val ℓ =
      if ℓ ∈ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)) then 1 else 0 := by
    rintro ⟨τ, x, y⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, crW]
    by_cases h : τ = σ
    · subst h
      by_cases hx : x = i
      · subst hx
        rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨y, rfl⟩]
      · rw [if_neg (by simp [Fin.val_inj, hx]), if_neg]
        rintro ⟨b, hb⟩
        exact hx ((Prod.mk.inj (eq_of_heq (Sigma.mk.inj hb).2)).1).symm
    · rw [if_neg (by simp [h]), if_neg]
      rintro ⟨b, hb⟩
      exact h (Sigma.mk.inj hb).1.symm
  rw [Finsupp.weight_apply, Finsupp.sum]
  simp only [hw, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  have hsub : ∑ ℓ ∈ m.support ∩ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)), m ℓ =
      ∑ ℓ ∈ Finset.univ.image (fun b : Fin n => (⟨σ, i, b⟩ : Letter T r n)), m ℓ := by
    refine Finset.sum_subset Finset.inter_subset_right fun ℓ hℓS hℓ => ?_
    by_contra h0
    exact hℓ (Finset.mem_inter.mpr ⟨Finsupp.mem_support_iff.mpr h0, hℓS⟩)
  rw [hsub, Finset.sum_image (fun b _ b' _ h => hinj h)]
end Formalism.L2.Pj.Crude
