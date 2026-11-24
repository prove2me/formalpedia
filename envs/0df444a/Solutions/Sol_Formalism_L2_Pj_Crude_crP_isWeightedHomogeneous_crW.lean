-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_isWeightedHomogeneous_crW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:31:41.46993+00:00
-- url     : https://prove2.me/submissions/722c4f32-7242-48cd-adf6-690dd30c11cd

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crMinor_hom
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous
import Theorems.Thm_Formalism_L2_Pj_Crude_crRowSum
import Theorems.Thm_Formalism_L2_Pj_Crude_crExpSum

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
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    IsWeightedHomogeneous (crW (r := r) (n := n) σ i.val) (crP r n R β a) (a σ i) := by
  have hD : ∀ τ (kk : Fin (r τ)), IsWeightedHomogeneous (crW (r := r) (n := n) σ i.val)
      (crMinor r n R β τ kk).det (if τ = σ ∧ (i : ℕ) < (kk : ℕ) + 1 then 1 else 0) := by
    intro τ kk
    apply crMinor_hom
    intro π
    rw [← crRowSum τ σ ((kk : ℕ) + 1) (i : ℕ)]
    rw [← Equiv.sum_comp π (fun j : Fin ((kk : ℕ) + 1) => if τ = σ ∧ (j : ℕ) = (i : ℕ) then 1 else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [crW]
  have h := crP_isWeightedHomogeneous R β a _ _ hD
  convert h using 1
  rw [Finset.sum_eq_single σ]
  · rw [← crExpSum a ha σ i]
    refine Finset.sum_congr rfl fun kk _ => ?_
    by_cases hk : (i : ℕ) < (kk : ℕ) + 1
    · simp [hk]
    · simp [hk]
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro kk _
    simp [hτ]
  · intro h
    exact absurd (Finset.mem_univ σ) h
end Formalism.L2.Pj.Crude
