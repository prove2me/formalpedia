-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_mem_harmK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:54.78714+00:00
-- url     : https://prove2.me/submissions/4d3451b2-a3c5-4796-9293-47939d9a85df

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_mem_supported
import Theorems.Thm_Formalism_L2_Pj_Crude_crPderiv_supported
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
section Part1
variable {r n}
private theorem crPderiv_zero_lemma {R : Type} [CommRing R] {s : Set (Letter T r n)} (i : Letter T r n)
    (hi : i ∉ s) {p : MvPolynomial (Letter T r n) R} (hp : p ∈ supported R s) : pderiv i p = 0 := by
  classical
  have hp' : p ∈ Algebra.adjoin R ((X : Letter T r n → MvPolynomial (Letter T r n) R) '' s) := hp
  clear hp
  induction hp' using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply, if_neg]
    rintro rfl
    exact hi hj
  | algebraMap c => exact Derivation.map_algebraMap _ _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
end Part1
section Part2
variable {r n}
end Part2
section Part3
variable {r n}
end Part3
section Part4
variable {r n}
end Part4
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
end Formalism.L2.Pj.Crude
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (cc : T → T)
    (isX : T → Prop) (hcc : ∀ τ, isX τ → cc τ ≠ τ) (hβ : Function.Injective β) :
    crP r n k β a ∈ harmK r n k cc isX (fun _ => 1) := by
  unfold harmK lap
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, Derivation.coeFn_coe]
  intro τ hτ x x'
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
  by_cases hbb : b = b'
  · subst hbb
    have hsup := crPderiv_supported ⟨cc τ, (x', b)⟩ (crP_mem_supported k β a)
    by_cases hg : (⟨τ, (x, b)⟩ : Letter T r n) ∈ GoodL r n β
    · have hg' : (⟨cc τ, (x', b)⟩ : Letter T r n) ∉ GoodL r n β := by
        rintro ⟨j, hj⟩
        obtain ⟨i0, hi0⟩ := hg
        have := hβ (hi0.trans hj.symm)
        exact hcc τ hτ (Sigma.mk.inj this).1.symm
      rw [crPderiv_zero_lemma _ hg' (crP_mem_supported k β a), map_zero, smul_zero]
    · rw [crPderiv_zero_lemma _ hg hsup, smul_zero]
  · rw [Matrix.one_apply_ne hbb, zero_smul]
end Formalism.L2.Pj.Crude
