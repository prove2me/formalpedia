-- Prove2me | solution 1 for DimdPolyLEAN.windowAmbiguity_dense_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:49:30.638801+00:00
-- url     : https://prove2.me/submissions/1ba7421f-0ee6-4e18-825d-df8612d0cb9b

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
public import Theorems.Thm_DimdPolyLEAN_PKappa_isPolynomial
public import Theorems.Thm_DimdPolyLEAN_windowAmbiguity_factorization
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
private lemma dense_ne_zero_of_phaseSpace_polynomial
    {d : Nat} {P : PhaseSpace d -> ℂ}
    (hpoly : IsPhaseSpacePolynomial P)
    (hne : ∃ ξ0, P ξ0 ≠ 0) :
    Dense {ξ : PhaseSpace d | P ξ ≠ 0} := by
  classical
  rcases hpoly with ⟨p, hp⟩
  rcases hne with ⟨ξ0, hξ0⟩
  rw [Metric.dense_iff]
  intro ξ ε hε
  let line : ℝ -> PhaseSpace d := fun t =>
    (ξ.1 + t • (ξ0.1 - ξ.1), ξ.2 + t • (ξ0.2 - ξ.2))
  let affineCoord : (Fin d ⊕ Fin d) -> Polynomial ℂ
    | Sum.inl q => Polynomial.C (ξ.1 q : ℂ) +
        Polynomial.C (((ξ0.1 q - ξ.1 q : ℝ) : ℂ)) * Polynomial.X
    | Sum.inr q => Polynomial.C (ξ.2 q : ℂ) +
        Polynomial.C (((ξ0.2 q - ξ.2 q : ℝ) : ℂ)) * Polynomial.X
  let qpoly : Polynomial ℂ := MvPolynomial.eval₂Hom Polynomial.C affineCoord p
  have hqeval : ∀ t : ℝ, qpoly.eval (t : ℂ) = P (line t) := by
    intro t
    calc
      qpoly.eval (t : ℂ) =
          MvPolynomial.eval (fun s => Polynomial.eval (t : ℂ) (affineCoord s)) p := by
            change (Polynomial.evalRingHom (t : ℂ))
                ((MvPolynomial.eval₂Hom Polynomial.C affineCoord) p) = _
            rw [MvPolynomial.map_eval₂Hom]
            have hC : (Polynomial.evalRingHom (t : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
              ext z
              simp
            simp_all only [Prod.forall, Prod.mk.eta, ne_eq, gt_iff_lt, Polynomial.coe_evalRingHom,
              MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_id]
      _ = MvPolynomial.eval (phaseSpacePolyEval (line t)) p := by
            have hev : (fun s => Polynomial.eval (t : ℂ) (affineCoord s)) =
                phaseSpacePolyEval (line t) := by
              funext s
              cases s with
              | inl q =>
                  simp [affineCoord, phaseSpacePolyEval, line]
                  ring
              | inr q =>
                  simp [affineCoord, phaseSpacePolyEval, line]
                  ring
            rw [hev]
      _ = P (line t) := by rw [hp]
  have hline1 : line 1 = ξ0 := by ext q <;> simp [line]
  have hq_ne : qpoly ≠ 0 := by
    intro hzero
    have hq1 := hqeval 1
    simp_all only [Prod.forall, Prod.mk.eta, ne_eq, gt_iff_lt, Polynomial.eval_zero,
      Complex.ofReal_one, not_true_eq_false]
  let rootsReal : Set ℝ := {t : ℝ | qpoly.eval (t : ℂ) = 0}
  have hroots_finite : rootsReal.Finite := by
    have hroots_complex : ({z : ℂ | qpoly.IsRoot z}).Finite :=
      Polynomial.finite_setOfPred_isRoot hq_ne
    have hpre : rootsReal = Complex.ofReal ⁻¹' {z : ℂ | qpoly.IsRoot z} := by
      ext t
      simp [rootsReal, Polynomial.IsRoot]
    rw [hpre]
    exact Set.Finite.preimage Complex.ofReal_injective.injOn hroots_complex
  have hnonroots_dense : Dense {t : ℝ | qpoly.eval (t : ℂ) ≠ 0} := by
    apply dense_iff_inter_open.2
    intro U hU hUne
    obtain ⟨x, hx⟩ := hUne
    have hU_infinite : U.Infinite := infinite_of_mem_nhds x (hU.mem_nhds hx)
    obtain ⟨t, htU, htroot⟩ := (hU_infinite.sdiff hroots_finite).nonempty
    exact ⟨t, htU, htroot⟩
  have hline_cont : Continuous line := by fun_prop
  have hline0 : line 0 = ξ := by ext q <;> simp [line]
  have hpre_ball : line ⁻¹' Metric.ball ξ ε ∈ nhds (0 : ℝ) := by
    have hball : Metric.ball ξ ε ∈ nhds (line 0) := by
      simpa [hline0] using Metric.ball_mem_nhds ξ hε
    exact hline_cont.continuousAt hball
  rcases hnonroots_dense.inter_nhds_nonempty hpre_ball with ⟨t, ht_nonroot, ht_ball⟩
  refine ⟨line t, ?_⟩
  simp_all only [Prod.forall, Prod.mk.eta, ne_eq, gt_iff_lt, Set.mem_ofPred_eq, Set.mem_preimage,
    Metric.mem_ball, Set.mem_inter_iff, not_false_eq_true, and_self]
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
    Dense {ξ : PhaseSpace d |
      ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ ≠ 0} := by
  refine (dense_ne_zero_of_phaseSpace_polynomial (PKappa_isPolynomial hd kappa) ?_).mono ?_
  · exact ⟨(0, 0), by simp [PKappa, TKappa_zero, Phi_self_zero_ne]⟩
  · intro ξ hP
    change ambiguityRep (varphiKappa kappa) (varphiKappa kappa) ξ ≠ 0
    change PKappa kappa ξ ≠ 0 at hP
    rw [windowAmbiguity_factorization hd kappa ξ]
    exact mul_ne_zero hP (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
end DimdPolyLEAN
