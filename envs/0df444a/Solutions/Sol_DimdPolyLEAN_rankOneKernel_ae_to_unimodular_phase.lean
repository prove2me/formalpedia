-- Prove2me | solution 1 for DimdPolyLEAN.rankOneKernel_ae_to_unimodular_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:41:04.560883+00:00
-- url     : https://prove2.me/submissions/a9adbc0e-c66d-4e59-bdc7-7cd1a2dc44c4

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
public import Theorems.Thm_DimdPolyLEAN_L2_eq_zero_of_rep_ae_eq_zero
public import Theorems.Thm_DimdPolyLEAN_ae_unimodular_phase_to_L2_eq
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
private lemma exists_eventually_and_ne_zero
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {P : α -> Prop} {a : α -> ℂ}
    (hP : ∀ᵐ x ∂μ, P x)
    (hnot : ¬ a =ᵐ[μ] fun _ => (0 : ℂ)) :
    ∃ x, P x ∧ a x ≠ 0 := by
  by_contra hnone
  apply hnot
  filter_upwards [hP] with x hxP
  simp_all only [ne_eq, not_exists, not_and, Decidable.not_not]
private lemma norm_eq_one_of_mul_star_eq_one {w : ℂ}
    (h : w * star w = 1) :
    ‖w‖ = 1 := by
  have h' := congrArg norm h
  simp at h'
  have hw_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
  nlinarith only [h', hw_nonneg]
private theorem rankOneKernel_ae_eq_phase
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {fRep gRep : α → ℂ}
    (hkernel_prod :
      (fun p : α × α => fRep p.1 * star (fRep p.2)) =ᵐ[μ.prod μ]
        fun p => gRep p.1 * star (gRep p.2)) :
    (fRep =ᵐ[μ] fun _ => (0 : ℂ)) ∧ (gRep =ᵐ[μ] fun _ => (0 : ℂ)) ∨
      ∃ w : ℂ, ‖w‖ = 1 ∧ gRep =ᵐ[μ] fun v => w * fRep v := by
  have hrow_ae := MeasureTheory.Measure.ae_ae_of_ae_prod hkernel_prod
  by_cases hf_zero : fRep =ᵐ[μ] fun _ => (0 : ℂ)
  · left
    refine ⟨hf_zero, ?_⟩
    by_contra hg_ne
    have hfRep_zero := hf_zero
    have hgRep_not_zero := hg_ne
    have hgood : ∀ᵐ u ∂μ,
        (∀ᵐ v ∂μ, fRep u * star (fRep v) = gRep u * star (gRep v)) ∧
          fRep u = 0 := hrow_ae.and hfRep_zero
    rcases exists_eventually_and_ne_zero hgood hgRep_not_zero with
      ⟨u0, hgood_u0, hg0_ne⟩
    rcases hgood_u0 with ⟨hrow_u0, hf0⟩
    have hgRep_zero : gRep =ᵐ[μ] fun _ => (0 : ℂ) := by
      filter_upwards [hrow_u0] with v hv
      have hproduct : gRep u0 * star (gRep v) = 0 := by
        simpa only [hf0, zero_mul] using hv.symm
      exact star_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hg0_ne)
    exact hg_ne hgRep_zero
  · right
    have hfRep_not_zero := hf_zero
    rcases exists_eventually_and_ne_zero hrow_ae hfRep_not_zero with
      ⟨u0, hrow_u0, hf0_ne⟩
    have hg0_ne : gRep u0 ≠ 0 := by
      by_contra hg0
      apply hfRep_not_zero
      filter_upwards [hrow_u0] with v hv
      have hproduct : fRep u0 * star (fRep v) = 0 := by
        simpa only [hg0, zero_mul] using hv
      exact star_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_left hf0_ne)
    let w : ℂ := star (fRep u0 / gRep u0)
    have hphase : gRep =ᵐ[μ] fun v => w * fRep v := by
      filter_upwards [hrow_u0] with v hv
      have hstar :
          star (gRep v) = (fRep u0 / gRep u0) * star (fRep v) := by
        calc
          star (gRep v) =
              ((gRep u0)⁻¹ * gRep u0) * star (gRep v) := by rw [inv_mul_cancel₀ hg0_ne, one_mul]
          _ = (gRep u0)⁻¹ * (gRep u0 * star (gRep v)) := by ring
          _ = (gRep u0)⁻¹ * (fRep u0 * star (fRep v)) := by rw [← hv]
          _ = (fRep u0 / gRep u0) * star (fRep v) := by rw [div_eq_mul_inv]; ac_rfl
      have hconj := congrArg star hstar
      calc
        gRep v = fRep v * star (fRep u0 / gRep u0) := by
          simpa only [star_mul, star_star] using hconj
        _ = w * fRep v := by ring
    have hphase_fst :
        (fun p : α × α => gRep p.1)
          =ᵐ[μ.prod μ] fun p => w * fRep p.1 :=
      MeasureTheory.Measure.quasiMeasurePreserving_fst.ae hphase
    have hphase_snd :
        (fun p : α × α => gRep p.2)
          =ᵐ[μ.prod μ] fun p => w * fRep p.2 :=
      MeasureTheory.Measure.quasiMeasurePreserving_snd.ae hphase
    have hscale_prod :
        (fun p : α × α => fRep p.1 * star (fRep p.2))
          =ᵐ[μ.prod μ]
            fun p => (w * star w) * (fRep p.1 * star (fRep p.2)) := by
      filter_upwards [hkernel_prod, hphase_fst, hphase_snd] with p hp hp1 hp2
      calc
        fRep p.1 * star (fRep p.2) = gRep p.1 * star (gRep p.2) := hp
        _ = (w * fRep p.1) * star (w * fRep p.2) := by rw [hp1, hp2]
        _ = (w * star w) * (fRep p.1 * star (fRep p.2)) := by
              rw [star_mul]
              ring
    have hscale_rows := MeasureTheory.Measure.ae_ae_of_ae_prod hscale_prod
    rcases exists_eventually_and_ne_zero hscale_rows hfRep_not_zero with
      ⟨u1, hscale_u1, hu1_ne⟩
    rcases exists_eventually_and_ne_zero hscale_u1 hfRep_not_zero with
      ⟨v1, hscale_u1v1, hv1_ne⟩
    have hF_ne : fRep u1 * star (fRep v1) ≠ 0 :=
      mul_ne_zero hu1_ne (star_ne_zero.mpr hv1_ne)
    have hunit_mul : w * star w = 1 := by
      exact mul_right_cancel₀ hF_ne (by simpa only [one_mul] using hscale_u1v1.symm)
    exact ⟨w, norm_eq_one_of_mul_star_eq_one hunit_mul, hphase⟩
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
    {d : Nat} {f g : L2Real d} {fRep gRep : RealVec d -> ℂ}
    (hf_rep : IsL2Rep f fRep) (hg_rep : IsL2Rep g gRep)
    (hkernel :
      (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
        =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (RealVec d × RealVec d))]
          fun p => gRep p.1 * star (gRep p.2)) :
    (f = 0 ∧ g = 0) ∨ ∃ w : ℂ, ‖w‖ = 1 ∧ g = w • f := by
  have hkernel_prod :
      (fun p : RealVec d × RealVec d => fRep p.1 * star (fRep p.2))
        =ᵐ[(volume : Measure (RealVec d)).prod volume]
          fun p => gRep p.1 * star (gRep p.2) := by
    simpa only [Measure.volume_eq_prod (RealVec d) (RealVec d)] using hkernel
  rcases rankOneKernel_ae_eq_phase hkernel_prod with hzero | ⟨w, hw, hphase⟩
  · exact Or.inl ⟨L2_eq_zero_of_rep_ae_eq_zero hf_rep hzero.1,
      L2_eq_zero_of_rep_ae_eq_zero hg_rep hzero.2⟩
  · exact Or.inr ⟨w, hw, ae_unimodular_phase_to_L2_eq hf_rep hg_rep hphase⟩
end DimdPolyLEAN
