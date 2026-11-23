-- Prove2me | solution 1 for Formalism.CyclotomicNorms.PrismSpan.off_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:05:22.87106+00:00
-- url     : https://prove2.me/submissions/6099fecb-6fd0-4ab6-a493-1a4f568605db

import Definitions.Def_Formalism_CyclotomicNorms_StatementA
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_SpanQuadraticOfImage
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_diag_mem
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_pi_smul_single
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_alg_smul_eq
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_proj_surj
import Theorems.Thm_Formalism_CyclotomicNorms_PrismSpan_exists_end

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.CyclotomicNorms
open Formalism.CyclotomicNorms.PrismSpan
variable {k G : Type} [Field k] [Group G] {a : ℕ} {W : Fin a → Type}
  [∀ i, AddCommGroup (W i)] [∀ i, Module k (W i)]
variable (ρ : ∀ i, Representation k G (W i))
variable {ρ}
namespace Formalism.CyclotomicNorms.PrismSpan
theorem _root_.solution (hspan : ∀ i, Submodule.span k (Set.range (ρ i)) = ⊤)
    (hne : ∀ i j, i ≠ j → ¬ ∃ T : W i ≃ₗ[k] W j, ∀ g x, T (ρ i g x) = ρ j g (T x))
    (φ : (∀ j, W j) →ₗ[alg ρ] (∀ j, W j)) {i j : Fin a} (hij : i ≠ j) (w : W i) :
    φ (Pi.single i w) j = 0 := by
  let ψ : W i →ₗ[k] W j :=
    { toFun := fun w => φ (Pi.single i w) j
      map_add' := fun x y => by
        show φ (Pi.single i (x + y)) j = φ (Pi.single i x) j + φ (Pi.single i y) j
        rw [Pi.single_add, map_add]; rfl
      map_smul' := fun c x => by
        show φ (Pi.single i (c • x)) j = c • φ (Pi.single i x) j
        rw [Pi.single_smul, ← alg_smul_eq ρ c, φ.map_smul, alg_smul_eq]; rfl }
  have hint : ∀ r ∈ alg ρ, ∀ x, ψ (r i x) = r j (ψ x) := by
    intro r hr x
    show φ (Pi.single i (r i x)) j = r j (φ (Pi.single i x) j)
    rw [← pi_smul_single r i x]
    exact congrFun (φ.map_smul ⟨r, hr⟩ (Pi.single i x)) j
  by_contra hw
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro u hu
    by_contra hu0
    obtain ⟨X, hX⟩ := exists_end (k := k) hu0 w
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan i X
    apply hw
    show ψ w = 0
    rw [← hX, hint r hr, LinearMap.mem_ker.mp hu, map_zero]
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨Y, hY⟩ := exists_end (k := k) (show ψ w ≠ 0 from hw) y
    obtain ⟨r, hr, rfl⟩ := proj_surj hspan j Y
    exact ⟨r i w, by rw [hint r hr, hY]⟩
  exact hne i j hij ⟨LinearEquiv.ofBijective ψ ⟨hinj, hsurj⟩,
    fun g x => hint _ (diag_mem ρ g) x⟩
end Formalism.CyclotomicNorms.PrismSpan
