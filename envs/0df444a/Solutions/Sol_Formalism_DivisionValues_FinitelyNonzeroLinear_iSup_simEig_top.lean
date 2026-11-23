-- Prove2me | solution 1 for Formalism.DivisionValues.FinitelyNonzeroLinear.iSup_simEig_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:39:15.970365+00:00
-- url     : https://prove2.me/submissions/e9bcf956-154f-446d-a32c-13cb0e6199af

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_Fnl_zero
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_ker_pow_normal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.FinitelyNonzeroLinear
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.DivisionValues.FinitelyNonzeroLinear
theorem _root_.solution (σ : K →+* ℂ) {Hc : Matrix (Fin n) (Fin n) ℂ} (hH : Hc.PosDef)
    (𝒯 : Set (Matrix (Fin n) (Fin n) K)) (hcomm : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T)
    (hadj : ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, (T.map σ)ᴴ * Hc = Hc * T'.map σ) :
    ⨆ χ : Matrix (Fin n) (Fin n) K → ℂ, simEig σ 𝒯 χ = ⊤ := by
  classical
  let f : 𝒯 → Module.End ℂ (Fin n → ℂ) := fun T =>
    Matrix.toLin' ((T : Matrix (Fin n) (Fin n) K).map σ)
  have hfx : ∀ T x, f T x = ((T : Matrix (Fin n) (Fin n) K).map σ) *ᵥ x := fun T x =>
    Matrix.toLin'_apply _ _
  have hcommC : ∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T.map σ * T'.map σ = T'.map σ * T.map σ :=
    fun T hT T' hT' => by rw [← Matrix.map_mul, ← Matrix.map_mul, hcomm T hT T' hT']
  have hfc : ∀ i j, Commute (f i) (f j) := fun i j => by
    show f i * f j = f j * f i
    refine LinearMap.ext fun x => ?_
    show f i (f j x) = f j (f i x)
    simp only [hfx, Matrix.mulVec_mulVec, hcommC i i.2 j j.2]
  have hsc : ∀ (c : ℂ) (y : Fin n → ℂ), (c • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ y = c • y :=
    fun c y => by
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  have hpowx : ∀ (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (k : ℕ) (x : Fin n → ℂ),
      ((Matrix.toLin' A - c • 1) ^ k) x = ((A - c • 1) ^ k) *ᵥ x := by
    intro A c k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      have hg : ∀ y, (Matrix.toLin' A - c • 1) y = (A - c • 1) *ᵥ y := fun y => by
        simp [Matrix.sub_mulVec, Matrix.toLin'_apply, hsc]
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      exact hg _
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo f
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hfc j i) φ)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  rw [eq_top_iff, ← htop]
  refine iSup_le fun χ => ?_
  let χ' : Matrix (Fin n) (Fin n) K → ℂ := fun T => if h : T ∈ 𝒯 then χ ⟨T, h⟩ else 0
  refine le_trans ?_ (le_iSup _ χ')
  intro x hx
  show ∀ T ∈ 𝒯, (T.map σ).mulVec x = χ' T • x
  intro T hT
  have hxT : x ∈ (f ⟨T, hT⟩).maxGenEigenspace (χ ⟨T, hT⟩) :=
    (Submodule.mem_iInf _).mp hx ⟨T, hT⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, ((f ⟨T, hT⟩ - χ ⟨T, hT⟩ • 1) ^ k) x = 0 := by
    exact Module.End.mem_genEigenspace_top.mp hxT
  have hk' : ((T.map σ - χ ⟨T, hT⟩ • 1) ^ k) *ᵥ x = 0 := by
    rw [← hpowx]
    exact hk
  obtain ⟨T', hT', hadjT⟩ := hadj T hT
  have hAB : Commute (T.map σ) (T'.map σ) := hcommC T hT T' hT'
  have hcN : Commute (T.map σ - χ ⟨T, hT⟩ • 1) (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1) := by
    refine Commute.sub_left (Commute.sub_right hAB ((Commute.one_right _).smul_right _)) ?_
    exact Commute.sub_right ((Commute.one_left _).smul_left _)
      (((Commute.refl (1 : Matrix (Fin n) (Fin n) ℂ)).smul_left _).smul_right _)
  have hadjN : (T.map σ - χ ⟨T, hT⟩ • 1)ᴴ * Hc =
      Hc * (T'.map σ - starRingEnd ℂ (χ ⟨T, hT⟩) • 1) := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      sub_mul, mul_sub, hadjT, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      starRingEnd_apply]
  have h5 := ker_pow_normal hH hadjN hcN.eq k x hk'
  rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at h5
  rw [show χ' T = χ ⟨T, hT⟩ from dif_pos hT]
  exact h5
end Formalism.DivisionValues.FinitelyNonzeroLinear
