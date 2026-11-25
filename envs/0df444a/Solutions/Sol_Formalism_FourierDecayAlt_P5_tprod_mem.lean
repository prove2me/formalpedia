-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.tprod_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:09:15.2702+00:00
-- url     : https://prove2.me/submissions/377d7253-c145-4397-8a78-dcdcae7a46b3

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FsvMulFsvNeg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtFsvOther
import Theorems.Thm_Formalism_FourierDecayAlt_P5_Ts_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate ContDiff
open Filter Topology
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Tc : Subalgebra ℂ (Pr (RadSp k r z z' π π')))
    (l : ℕ) (hs : ∀ l' : Fin r, l < l'.val → L.p l' ∈ Tc ∧ L.c l' ∈ Tc ∧ L.ci l' ∈ Tc) (Y : ℂ) (i : ℕ)
    (hi : l < i) : ∀ a b, tprod L Y i a b ∈ Tc := by
  suffices H : ∀ n : ℕ, ∀ j : ℕ, r - j = n → l < j → ∀ a b, tprod L Y j a b ∈ Tc from H _ i rfl hi
  intro n
  induction n with
  | zero =>
    intro j hn hj a b
    rw [tprod, dif_neg (by omega), Matrix.one_apply]
    split_ifs
    · exact Tc.one_mem
    · exact Tc.zero_mem
  | succ n ih =>
    intro j hn hj a b
    rw [tprod, dif_pos (by omega), Matrix.mul_apply]
    refine Subalgebra.sum_mem _ fun c _ => Subalgebra.mul_mem _ (ih (j + 1) (by omega) (by omega) a c) ?_
    have hh := hs ⟨j, by omega⟩ hj
    exact Ts_mem _ Y hh.1 hh.2.1 hh.2.2 c b
end Formalism.FourierDecayAlt.P5
