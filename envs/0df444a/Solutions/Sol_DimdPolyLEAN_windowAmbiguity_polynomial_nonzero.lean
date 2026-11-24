-- Prove2me | solution 1 for DimdPolyLEAN.windowAmbiguity_polynomial_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:55:14.19737+00:00
-- url     : https://prove2.me/submissions/d56af3c8-737d-4be2-a713-026950f8a157

module
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ImportedAnalyticInputs
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_TensorBasis
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_ExactModulusRecovery
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


section
@[expose] public section
noncomputable section
namespace DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
private lemma complexHermite_self_zero (k : Nat) :
    complexHermite k k 0 = (-1 : ℂ) ^ k * (Nat.factorial k : ℂ) := by
  unfold complexHermite
  simp only [Nat.min_self]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjne
    have hjlt : j < k := by
      have hjle : j < k + 1 := Finset.mem_range.mp hj
      omega
    have hpos : 0 < k - j := Nat.sub_pos_of_lt hjlt
    simp [hpos.ne']
  · simp_all only [Finset.mem_range, lt_add_iff_pos_right, Order.lt_one_iff, not_true_eq_false,
      Nat.choose_self, Nat.cast_one, mul_one, tsub_self, pow_zero, star_zero, mul_eq_zero,
      pow_eq_zero_iff', neg_eq_zero, one_ne_zero, ne_eq, true_and, Nat.cast_eq_zero,
      IsEmpty.forall_iff]
private lemma phi1D_self_zero_ne (k : Nat) : phi1D k k 0 ≠ 0 := by
  rw [phi1D, complexHermite_self_zero]
  apply mul_ne_zero
  · apply inv_ne_zero
    norm_num [Nat.factorial_ne_zero]
  · apply mul_ne_zero
    · simp
    · exact_mod_cast Nat.factorial_ne_zero k
private lemma Phi_self_zero_ne {d : Nat} (kappa : MultiIndex d) :
    Phi kappa kappa (0 : Cd d) ≠ 0 := by
  unfold Phi
  apply Finset.prod_ne_zero_iff.mpr
  intro q _hq
  exact phi1D_self_zero_ne (kappa q)
private lemma TKappa_zero {d : Nat} :
    TKappa ((0, 0) : PhaseSpace d) = 0 := by
  ext q
  simp [TKappa]
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open DimdPolyLEAN
open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform RealInnerProductSpace SchwartzMap ComplexConjugate Nat Topology
namespace DimdPolyLEAN
theorem _root_.solution
    {d : Nat} (hd : 0 < d) (kappa : MultiIndex d) :
    PKappa kappa ≠ 0 := by
  let _ := hd
  intro hzero
  have hval := congrFun hzero ((0, 0) : PhaseSpace d)
  have hnonzero : PKappa kappa ((0, 0) : PhaseSpace d) ≠ 0 := by
    simp [PKappa, TKappa_zero, Phi_self_zero_ne]
  exact hnonzero hval
end DimdPolyLEAN
