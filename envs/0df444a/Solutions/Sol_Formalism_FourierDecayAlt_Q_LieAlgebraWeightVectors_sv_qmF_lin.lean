-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.sv_qmF_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:12:42.296862+00:00
-- url     : https://prove2.me/submissions/38171782-88de-4f66-be1a-35497c825058

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_SmoothVec
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_sv_foldr_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution {X : Type*} [AddCommGroup X] [Module ℂ X] {n t : ℕ} (Eop : Fin n → Fin n → X → X)
    (hE : ∀ a b, IsLinearMap ℂ (Eop a b)) (a b : Fin t → Fin n) (u : ℂ) : IsLinearMap ℂ (qmF Eop a b u) := by
  have hfac : ∀ σ : Equiv.Perm (Fin t), IsLinearMap ℂ (fun x : X =>
      (List.ofFn fun k : Fin t => fun y : X =>
        (if a (σ k) = b k then (u - ((k : ℕ) : ℂ)) • y else 0) + Eop (a (σ k)) (b k) y).foldr
        (fun T h => T h) x) := by
    intro σ
    apply sv_foldr_lin
    intro T hT
    rw [List.mem_ofFn] at hT
    obtain ⟨j, rfl⟩ := hT
    have hl := hE (a (σ j)) (b j)
    constructor
    · intro x y
      split_ifs <;> simp only [hl.map_add, smul_add] <;> abel
    · intro c x
      split_ifs <;> simp only [hl.map_smul, smul_add, zero_add, smul_comm c]
  constructor
  · intro x y
    unfold qmF
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_add]
    exact congrArg _ ((hfac σ).map_add x y)
  · intro c x
    unfold qmF
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_comm c]
    exact congrArg _ ((hfac σ).map_smul c x)
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
