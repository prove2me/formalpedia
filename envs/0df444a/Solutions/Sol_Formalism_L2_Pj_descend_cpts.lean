-- Prove2me | solution 1 for Formalism.L2.Pj.descend_cpts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:35:26.329591+00:00
-- url     : https://prove2.me/submissions/d9501d06-79b5-460e-894c-ed30bf840314

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ReadAlg
import Theorems.Thm_Formalism_L2_Pj_cvalR_algebraMap
import Theorems.Thm_Formalism_L2_Pj_linIndep_cpts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPolynomial
variable {K : Type} [Field K]
namespace Formalism.L2.Pj
theorem _root_.solution [CharZero K] (σ : K →+* ℂ) (p : TRing K) {r : ℕ} (a : Fin r → p.R) (w : Fin r → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ j, w j * cvalR σ (ψ (a j)) = 0) (θ : Module.Dual K (CAt σ)) :
    ∑ j, θ (toCAt σ (w j)) • a j = 0 := by
  classical
  let S : Submodule K p.R := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let e := Module.finBasis K S
  let t : Fin r → Fin (Module.finrank K S) → K := fun j l => e.repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  have hat : ∀ j, a j = ∑ l, t j l • (e l : p.R) := by
    intro j
    have := e.sum_repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩
    have h2 := congrArg (fun x : S => (x : p.R)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hind : LinearIndependent K (fun l => (e l : p.R)) :=
    e.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have key := linIndep_cpts σ p (fun l => (e l : p.R)) hind (fun l => ∑ j, σ (t j l) * w j) fun ψ => by
    rw [← h ψ]
    simp_rw [hat, map_sum, map_smul, Algebra.smul_def, map_mul, cvalR_algebraMap, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hk : ∀ l, ∑ j, t j l • toCAt σ (w j) = 0 := by
    intro l
    have := congrFun key l
    simp only [Pi.zero_apply] at this
    exact this
  calc ∑ j, θ (toCAt σ (w j)) • a j = ∑ l, θ (∑ j, t j l • toCAt σ (w j)) • (e l : p.R) := by
        simp_rw [hat, Finset.smul_sum, map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = 0 := by simp [hk]
end Formalism.L2.Pj
