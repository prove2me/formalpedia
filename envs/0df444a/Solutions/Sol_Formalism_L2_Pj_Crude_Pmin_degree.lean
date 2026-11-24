-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.Pmin_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:32:04.818674+00:00
-- url     : https://prove2.me/submissions/c2435c63-4362-4dc8-9899-5902858b0901

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_map
import Theorems.Thm_Formalism_L2_Pj_Crude_crMinor_hom
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous
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
variable (k : Type) [Field k] [CharZero k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (ha : Dom r a) (m : Letter T r n →₀ ℕ)
    (hm : m ∈ (MvPolynomial.map (Int.castRingHom k) (Pmin r n β a)).support) :
    m.degree = ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
  rw [crP_map] at hm
  have hD : ∀ τ (kk : Fin (r τ)), IsWeightedHomogeneous (fun _ : Letter T r n => (1 : ℕ))
      (crMinor r n k β τ kk).det ((kk : ℕ) + 1) := by
    intro τ kk
    apply crMinor_hom
    intro π
    simp
  have h : Finsupp.weight (fun _ : Letter T r n => (1 : ℕ)) m =
      ∑ τ, ∑ kk : Fin (r τ), crExp r a τ kk • ((kk : ℕ) + 1) :=
    crP_isWeightedHomogeneous k β a _ _ hD (MvPolynomial.mem_support_iff.mp hm)
  have hsum : (∑ τ, ∑ kk : Fin (r τ), crExp r a τ kk • ((kk : ℕ) + 1)) =
      ∑ σ : T, ∑ i : Fin (r σ), a σ i := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hx : ∀ i : Fin (r τ), a τ i =
        ∑ kk : Fin (r τ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a τ kk else 0 :=
      fun i => (crExpSum a ha τ i).symm
    rw [Finset.sum_congr rfl fun i _ => hx i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun kk _ => ?_
    have hcard : (Finset.univ.filter fun i : Fin (r τ) => (i : ℕ) < (kk : ℕ) + 1).card = (kk : ℕ) + 1 := by
      rw [show (Finset.univ.filter fun i : Fin (r τ) => (i : ℕ) < (kk : ℕ) + 1) = Finset.Iic kk by
        ext i
        rw [Finset.mem_filter, Finset.mem_Iic]
        constructor
        · intro h
          exact Fin.le_def.mpr (by have := h.2; omega)
        · intro h
          exact ⟨Finset.mem_univ _, by have := Fin.le_def.mp h; omega⟩]
      exact Fin.card_Iic kk
    rw [← Finset.sum_filter, Finset.sum_const, hcard, smul_eq_mul, smul_eq_mul, mul_comm]
  rw [← hsum, ← h]
  rw [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum]
  simp
end Formalism.L2.Pj.Crude
