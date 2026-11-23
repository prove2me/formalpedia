-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:00.862837+00:00
-- url     : https://prove2.me/submissions/898375e3-904e-4587-9974-1ebd100564b7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const_smul_complex
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_contDiff_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_ibp
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (ι : Type) [Fintype ι] (N : ℕ) (Γ c₀ : ℝ) (hc₀ : 0 < c₀) : ∃ C₁ : ℝ, 0 ≤ C₁ ∧
    ∀ (v : ι → E), (∀ l, ‖v l‖ = 1) → ∀ (A : Set E) (w : E → ℝ) (φ : E → ℝ) (τ : ℝ), 0 < τ →
      (∀ x ∈ A, 0 < w x) → (∀ x ∈ A, τ ≤ w x ^ 2) → ContDiff ℝ 1 φ → Sym A w 1 (N + 1) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, c₀ * w x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (v l)) ^ 2 + τ) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (b : E → V) (m : ℤ) (K : ℝ),
        HasCompactSupport b → tsupport b ⊆ A → Sym A w m (N + 1) K b →
        ∃ b' : E → V, HasCompactSupport b' ∧ tsupport b' ⊆ A ∧ Sym A w (m - 2) N (C₁ * τ * K) b' ∧
          ∫ x, osc φ τ x • b x ∂μ = ∫ x, osc φ τ x • b' x ∂μ := by
  obtain ⟨Ch, hCh0, hCh⟩ := Sym.inv (E := E) (N + 1) ((∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) + 1) c₀ hc₀
  refine ⟨(Fintype.card ι : ℝ) * (2 ^ (N + 1) * (2 ^ (N + 1) * |Γ| * Ch)) + 2 ^ (N + 1) * Ch, by positivity, ?_⟩
  intro v hv A w φ τ hτ hw hτw hφ hφS hD V _ _ b m K hbs hbA hb
  set p : ι → E → ℝ := fun l x => fderiv ℝ φ x (v l) with hpdef
  set h : E → ℝ := fun x => (∑ l, p l x * p l x + τ)⁻¹ with hhdef
  have hp : ∀ l, Sym A w 1 (N + 1) |Γ| (p l) := fun l => by
    have := (hφS.mono hw le_rfl (le_abs_self Γ)).clm_apply (v l)
    rwa [hv l, mul_one] at this
  have hsum : Sym A w (1 + 1) (N + 1) (∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) (fun x => ∑ l, p l x * p l x) :=
    Sym.sum Finset.univ (fun l _ => Sym.mul hw (hp l) (hp l))
  have hτS : Sym A w (1 + 1) (N + 1) 1 (fun _ : E => τ) :=
    Sym.const τ zero_le_one hw (fun x hx => by
      rw [Real.norm_of_nonneg hτ.le, one_mul]
      have : w x ^ ((1 : ℤ) + 1) = w x ^ 2 := by norm_num
      rw [this]; exact hτw x hx)
  have hDS : Sym A w 2 (N + 1) ((∑ _l : ι, 2 ^ (N + 1) * |Γ| * |Γ|) + 1) (fun x => ∑ l, p l x * p l x + τ) :=
    B_cast (hsum.add hτS) (by norm_num) rfl
  have hpos : ∀ x, 0 < ∑ l, p l x * p l x + τ := fun x =>
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun l _ => mul_self_nonneg _) hτ
  have hh : Sym A w (-2) (N + 1) Ch h := hCh A w _ hw hDS hpos (fun x hx => by
    have := hD x hx
    simpa [hpdef, sq] using this)
  have he : ∀ l, Sym A w (1 + -2) (N + 1) (2 ^ (N + 1) * |Γ| * Ch) (fun x => p l x * h x) :=
    fun l => Sym.mul hw (hp l) hh
  set c : ι → E → V := fun l x => (p l x * h x) • b x with hcdef
  have hc : ∀ l, Sym A w (1 + -2 + m) (N + 1) (2 ^ (N + 1) * (2 ^ (N + 1) * |Γ| * Ch) * K) (c l) :=
    fun l => Sym.smul hw (he l) hb
  have hhb : Sym A w (-2 + m) (N + 1) (2 ^ (N + 1) * Ch * K) (fun x => h x • b x) := Sym.smul hw hh hb
  have hS1 := (Sym.sum Finset.univ (fun l _ => ((hc l).fderiv.clm_apply (v l)))).const_smul_complex
    (Complex.I * (τ : ℂ))
  have hS2 := (hhb.mono hw (Nat.le_succ N) le_rfl).const_smul τ
  have hnI : ‖Complex.I * (τ : ℂ)‖ = τ := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  have hsupp : Function.support
      (fun x => (Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x)) ⊆ tsupport b := by
    intro x hx
    by_contra hxb
    apply hx
    have hb0 : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hxb
    have hc0 : ∀ l, c l =ᶠ[𝓝 x] 0 := fun l => hb0.mono (fun y hy => by simp [hcdef, hy])
    have hf0 : ∀ l, fderiv ℝ (c l) x = 0 := fun l => by
      rw [(hc0 l).fderiv_eq]
      simp
    have hbx : b x = 0 := hb0.self_of_nhds
    simp [hf0, hbx]
  refine ⟨fun x => (Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x), hbs.mono' hsupp,
    (closure_minimal hsupp (isClosed_tsupport _)).trans hbA, ?_, ?_⟩
  · refine B_cast ((B_cast hS1 (by ring) rfl).add (B_cast hS2 (by ring) rfl)) rfl ?_
    simp only [hnI, hv, abs_of_pos hτ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    ring
  · have hoc : Continuous (osc φ τ) := (B_contDiff_osc τ hφ).continuous
    have hc1 : ∀ l, ContDiff ℝ 1 (c l) := fun l => (hc l).1.of_le (by norm_cast; omega)
    have hccs : ∀ l, HasCompactSupport (c l) := fun l => hbs.smul_left
    have hpc : ∀ l, Continuous (p l) := fun l => (hp l).1.continuous
    have hI1 : ∀ l, Integrable (fun x => (Complex.I * (τ : ℂ)) • (osc φ τ x • fderiv ℝ (c l) x (v l))) μ := fun l =>
      (Continuous.integrable_of_hasCompactSupport
        (hoc.smul (((hc1 l).continuous_fderiv (by norm_num)).clm_apply continuous_const))
        ((hccs l).fderiv_apply ℝ (v l)).smul_left).smul _
    have hI2 : Integrable (fun x => osc φ τ x • (τ • (h x • b x))) μ :=
      Continuous.integrable_of_hasCompactSupport
        (hoc.smul (continuous_const.smul (hhb.1.continuous))) (hbs.smul_left.smul_left).smul_left
    have hI3 : ∀ l, Integrable (fun x => (Complex.I * (τ : ℂ)) •
        ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x)) μ := fun l =>
      (Continuous.integrable_of_hasCompactSupport
        (Continuous.smul (by have := hpc l; fun_prop) (hc1 l).continuous) (hccs l).smul_left).smul _
    have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
    symm
    calc ∫ x, osc φ τ x • ((Complex.I * (τ : ℂ)) • ∑ l, fderiv ℝ (c l) x (v l) + τ • (h x • b x)) ∂μ
        = ∫ x, (∑ l, (Complex.I * (τ : ℂ)) • (osc φ τ x • fderiv ℝ (c l) x (v l))) +
            osc φ τ x • (τ • (h x • b x)) ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [smul_add, Finset.smul_sum]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [smul_comm]
      _ = (∑ l, (Complex.I * (τ : ℂ)) • ∫ x, osc φ τ x • fderiv ℝ (c l) x (v l) ∂μ) +
            ∫ x, osc φ τ x • (τ • (h x • b x)) ∂μ := by
          rw [integral_add (integrable_finsetSum _ fun l _ => hI1 l) hI2, integral_finsetSum _ fun l _ => hI1 l]
          simp_rw [integral_smul]
      _ = (∑ l, -∫ x, (Complex.I * (τ : ℂ)) • ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x) ∂μ) +
            ∫ x, osc φ τ x • (τ • (h x • b x)) ∂μ := by
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [B_ibp τ hφ (hc1 l) (hccs l) (v l), smul_neg, integral_smul]
      _ = ∫ x, (∑ l, -((Complex.I * (τ : ℂ)) • ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x))) +
            osc φ τ x • (τ • (h x • b x)) ∂μ := by
          have hI3n : ∀ l, Integrable (fun x => -((Complex.I * (τ : ℂ)) •
              ((Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ)) • c l x))) μ := fun l => (hI3 l).neg
          rw [integral_add (integrable_finsetSum _ fun l _ => hI3n l) hI2,
            integral_finsetSum _ fun l _ => hI3n l]
          simp_rw [integral_neg]
      _ = ∫ x, osc φ τ x • b x ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only [hcdef, ← Complex.coe_smul, smul_smul, ← neg_smul, ← Finset.sum_smul, ← add_smul]
          congr 1
          have hterm : ∀ l, -(Complex.I * (τ : ℂ) * (Complex.I * osc φ τ x * ((τ⁻¹ * p l x : ℝ) : ℂ) *
              ((p l x * h x : ℝ) : ℂ))) = osc φ τ x * (h x : ℂ) * ((p l x * p l x : ℝ) : ℂ) := fun l => by
            push_cast
            calc -(Complex.I * (τ : ℂ) * (Complex.I * osc φ τ x * ((τ : ℂ)⁻¹ * (p l x : ℂ)) *
                  ((p l x : ℂ) * (h x : ℂ))))
                = -(Complex.I * Complex.I) * ((τ : ℂ) * (τ : ℂ)⁻¹) *
                  (osc φ τ x * (h x : ℂ) * ((p l x : ℂ) * (p l x : ℂ))) := by ring
              _ = _ := by rw [Complex.I_mul_I, mul_inv_cancel₀ hτc]; ring
          simp_rw [hterm]
          rw [← Finset.mul_sum, ← Complex.ofReal_sum]
          have hh1 : h x * (∑ l, p l x * p l x + τ) = 1 := inv_mul_cancel₀ (hpos x).ne'
          have hh2 : (h x : ℂ) * (((∑ l, p l x * p l x : ℝ) : ℂ) + (τ : ℂ)) = 1 := by exact_mod_cast hh1
          calc osc φ τ x * (h x : ℂ) * ((∑ l, p l x * p l x : ℝ) : ℂ) + osc φ τ x * ((τ : ℂ) * (h x : ℂ))
              = osc φ τ x * ((h x : ℂ) * (((∑ l, p l x * p l x : ℝ) : ℂ) + (τ : ℂ))) := by ring
            _ = osc φ τ x := by rw [hh2, mul_one]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
