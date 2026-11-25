-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.generic_section_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:43.909349+00:00
-- url     : https://prove2.me/submissions/5762854b-3e1a-47cd-b175-d59b230e7930

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
import Theorems.Thm_Formalism_L2_Pj_GenSect_Phi_algebraMap
import Theorems.Thm_Formalism_L2_Pj_GenSect_gs_indep
import Theorems.Thm_Formalism_L2_Pj_GenSect_ker_Phi
import Theorems.Thm_Formalism_L2_Pj_GenSect_psi_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
variable {K Ω Kl K'} {D m : ℕ}
omit [Field Kl] [Field K'] [Algebra K Kl] [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution [CharZero K] (htr : Algebra.trdeg K Ω = D) (x : Fin m → Ω) (k₀ : Fin m) (hx₁ : x k₀ = 1)
    (halg : ∀ ω : Ω, IsAlgebraic (Algebra.adjoin K (Set.range (rr x k₀))) ω) :
    algebraMap (ΩT Ω D m) (RS K Ω D m) (∑ k, X ((0 : Fin (D + 1)), k) * C (x k)) ∉ Is K x := by
  classical
  have hx₀ : x k₀ ≠ 0 := by rw [hx₁]; exact one_ne_zero
  have hind := gs_indep (K := K) (D := D) x k₀ hx₀ htr halg
  have hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x k₀) q ≠ 0 := fun q hq h =>
    hq (hind (h.trans (map_zero _).symm))
  rw [ker_Phi x k₀ hx₀ hinj, RingHom.mem_ker, Phi_algebraMap]
  intro h
  have h2 : psi x k₀ (∑ k, X ((0 : Fin (D + 1)), k) * C (x k)) = 0 :=
    IsFractionRing.injective (CT Ω D k₀) (FractionRing (CT Ω D k₀)) (h.trans (map_zero _).symm)
  have hz : ∀ k : Fin m, ¬ Zs k₀ ((0 : Fin (D + 1)), k) := fun k hk => hk.1 rfl
  have hg : ∀ k : Fin m, gs x k₀ ((0 : Fin (D + 1)), k) = X ⟨((0 : Fin (D + 1)), k), hz k⟩ := by
    intro k
    simp only [gs, xv, if_neg (hz k), dif_neg (hz k)]
  have h2' : ∑ k, X ⟨((0 : Fin (D + 1)), k), hz k⟩ * C (x k) = (0 : CT Ω D k₀) := by
    rw [← h2, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, psi_X, hg]
    congr 1
    exact ((psi x k₀).commutes (x k)).symm
  have h3 := congrArg (MvPolynomial.eval
    (fun q : {p : Fin (D + 1) × Fin m // ¬ Zs k₀ p} =>
      if q.1 = ((0 : Fin (D + 1)), k₀) then (1 : Ω) else 0)) h2'
  simp only [map_sum, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, map_zero] at h3
  rw [Finset.sum_eq_single k₀] at h3
  · simp [hx₁] at h3
  · intro b _ hb
    simp [hb]
  · intro hk
    exact absurd (Finset.mem_univ _) hk
end Formalism.L2.Pj.GenSect
