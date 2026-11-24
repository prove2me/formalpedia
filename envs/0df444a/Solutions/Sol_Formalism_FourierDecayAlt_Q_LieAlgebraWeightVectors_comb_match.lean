-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.comb_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:55:13.116369+00:00
-- url     : https://prove2.me/submissions/0032bd5d-44fe-416a-9683-8f3794a9f9c6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_eq_of_prod_eq
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_ofIcc
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_anti
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_ty_ext
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_exists_ty
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_lo_int
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_int
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_int_sub
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_Pp_OK
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_Pq_OK
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_lo_le_of
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_le_hi_of
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_lo_Pp_le
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_hi_le_Pp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {P : M.Par} (hP : P.OK) :
    ∃ f : M.Ty P → M.Ty (Pp P), Function.Injective f ∧ (∀ (ρ : M.Ty P) (Y : ℂ), M.xC (Pp P) (f ρ) Y = M.xC P ρ Y) ∧
      ∀ (σ : M.Ty (Pp P)) (ρ : M.Ty (Pq P)), (∀ Y : ℂ, M.xC (Pp P) σ Y = M.xC (Pq P) ρ Y) → σ ∈ Set.range f := by
  have gP : ∀ i ∈ Icc 1 (P.k - 1), P.lo i ≤ P.hi i := hP.gap
  have gPp : ∀ i ∈ Icc 1 ((Pp P).k - 1), (Pp P).lo i ≤ (Pp P).hi i := (Pp_OK hP).gap
  have gPq : ∀ i ∈ Icc 1 ((Pq P).k - 1), (Pq P).lo i ≤ (Pq P).hi i := (Pq_OK hP).gap
  have hu : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have hu' : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.u' (j.1 + 1 + 1) - P.u 1 = n := fun j =>
    hP.int_u' _ (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
  have zP : ∀ j : Fin (P.k - 1), ∃ n : ℤ, P.lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int P _ _ (hu j) (hu' j)
  have zPp : ∀ j : Fin (P.k - 1), ∃ n : ℤ, (Pp P).lo (j.1 + 1) - (P.u 1 + 1 / 2) = n := fun j =>
    cb_lo_int (Pp P) _ _ (hu' j) (hu' j)
  have hf : ∀ ρ : M.Ty P, ∃ σ : M.Ty (Pp P),
      ∀ j : Fin (P.k - 1), M.rho (Pp P) σ (j.1 + 1) = M.rho P ρ (j.1 + 1) := by
    intro ρ
    refine cb_exists_ty (Pp P) (fun i => M.rho P ρ i) (fun j => ⟨?_, ?_, ?_⟩)
    · exact (cb_lo_Pp_le P _).trans (cb_rho_bounds P gP ρ j).1
    · exact (cb_rho_bounds P gP ρ j).2.trans (cb_hi_le_Pp P _)
    · exact cb_int_sub (cb_rho_int P _ ρ j (zP j)) (zPp j)
  choose f hf using hf
  refine ⟨f, ?_, ?_, ?_⟩
  · intro ρ ρ' h
    apply cb_ty_ext P
    intro j
    rw [← hf ρ j, ← hf ρ' j, h]
  · intro ρ Y
    unfold M.xC
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    obtain ⟨j, rfl⟩ := cb_ofIcc (n := P.k - 1) hi.1 hi.2
    rw [hf ρ j]
  · intro σ τ hx
    have hst : ∀ i ∈ Icc 1 (P.k - 1), M.rho (Pp P) σ i = M.rho (Pq P) τ i :=
      cb_eq_of_prod_eq (n := P.k - 1) (cb_rho_anti (Pp P) gPp σ) (cb_rho_anti (Pq P) gPq τ) (fun Y => hx Y)
    obtain ⟨ρ, hρ⟩ := cb_exists_ty P (fun i => M.rho (Pp P) σ i) (fun j => by
      have e := hst (j.1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by have := j.2; omega⟩)
      have bσ := cb_rho_bounds (Pp P) gPp σ j
      have bτ := cb_rho_bounds (Pq P) gPq τ j
      rw [← e] at bτ
      refine ⟨cb_lo_le_of P _ _ bσ.1 bτ.1, cb_le_hi_of P _ _ bσ.2 bτ.2, ?_⟩
      exact cb_int_sub (cb_rho_int (Pp P) _ σ j (zPp j)) (zP j))
    refine ⟨ρ, cb_ty_ext (Pp P) (fun j => ?_)⟩
    rw [hf ρ j, hρ j]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
