-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.exists_isometric_ext_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:09:14.839269+00:00
-- url     : https://prove2.me/submissions/efa756fc-7890-4496-ab14-ef521fbb085e

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WChain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (K0 : Type) [i0 : NormedField K0] [IsUltrametricDist K0]
    [CharZero K0] [CompleteSpace K0] (p : ℕ) (hp : p.Prime) (hn : ‖(p : K0)‖ = (p : ℝ)⁻¹) :
    ∃ (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K) (j : K0 →+* K)
      (ϖ : K), (∀ a, ‖j a‖ = ‖a‖) ∧ ϖ ^ (p ^ 2 - 1) = (p : K) := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  let nt : NontriviallyNormedField K0 :=
    { i0 with
      non_trivial := ⟨(p : K0)⁻¹, by rw [norm_inv, hn, inv_inv]; exact h1⟩ }
  let nK : NormedField (AlgebraicClosure K0) := spectralNorm.normedField K0 (AlgebraicClosure K0)
  have hnorm : ∀ x : AlgebraicClosure K0, ‖x‖ = spectralNorm K0 (AlgebraicClosure K0) x :=
    fun _ => rfl
  have hpos : 0 < p ^ 2 - 1 := by
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    omega
  obtain ⟨ϖ, hϖ⟩ := IsAlgClosed.exists_pow_nat_eq (p : AlgebraicClosure K0) hpos
  refine ⟨AlgebraicClosure K0, nK, ?_, ?_, algebraMap K0 (AlgebraicClosure K0), ϖ, ?_, hϖ⟩
  · exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_spectralNorm x y
  · exact charZero_of_injective_algebraMap (algebraMap K0 (AlgebraicClosure K0)).injective
  · intro a
    rw [hnorm]
    exact spectralNorm_extends a
end Formalism.InvariantFactorPaths.G7
