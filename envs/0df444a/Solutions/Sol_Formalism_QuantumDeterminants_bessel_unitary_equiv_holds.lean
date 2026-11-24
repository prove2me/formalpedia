-- Prove2me | solution 1 for Formalism.QuantumDeterminants.bessel_unitary_equiv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:09.539513+00:00
-- url     : https://prove2.me/submissions/7546c859-3d17-4d6d-baed-38fb29fea3cc

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnitaryEquiv_integral_transfer
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnitaryEquiv_rep_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_unitary_weyl_normal_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open BesselUnitaryEquiv
namespace Formalism.QuantumDeterminants
theorem _root_.solution : BesselUEquiv := by
  intro Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hN hW hW' hWl hW'l hNc hπ hπ'
    g h₀ hh₀ h₀' hh₀'
  have hu₀ := WeylGroupFacts.isUnit_of_uh hh₀.1
  have hu₀' := WeylGroupFacts.isUnit_of_uh hh₀'.1
  have hi₀ : h₀⁻¹ ∈ UWset k r z := WeylGroupFacts.uw_inv hh₀
  have hi₀' : h₀'⁻¹ ∈ UWset k r z' := WeylGroupFacts.uw_inv hh₀'
  have hui₀' : IsUnit (h₀'⁻¹).det := WeylGroupFacts.isUnit_of_uh hi₀'.1

  let Φ : (Mt k r × Mt k r) × (Mt k r × Mt k r) ≃ᵐ (Mt k r × Mt k r) × (Mt k r × Mt k r) :=
    ((lmulE h₀ hu₀).prodCongr (conjE h₀ hu₀)).prodCongr
      ((lmulE h₀'⁻¹ hui₀').prodCongr (conjE h₀'⁻¹ hui₀'))
  have hΦe : MeasurableEmbedding (Prod.map (Prod.map (lmulM h₀) (conjM h₀))
      (Prod.map (lmulM h₀'⁻¹) (conjM h₀'⁻¹)) :
        (Mt k r × Mt k r) × (Mt k r × Mt k r) → (Mt k r × Mt k r) × (Mt k r × Mt k r)) :=
    Φ.measurableEmbedding
  have hΦ : MeasurePreserving (Prod.map (Prod.map (lmulM h₀) (conjM h₀))
      (Prod.map (lmulM h₀'⁻¹) (conjM h₀'⁻¹)) :
        (Mt k r × Mt k r) × (Mt k r × Mt k r) → (Mt k r × Mt k r) × (Mt k r × Mt k r))
      ((μW.prod μN).prod (μW'.prod μN)) ((μW.prod μN).prod (μW'.prod μN)) := by
    refine MeasurePreserving.prod (MeasurePreserving.prod ?_ ?_) (MeasurePreserving.prod ?_ ?_)
    · exact ⟨(lmulE h₀ hu₀).measurable, hWl h₀ hh₀⟩
    · exact ⟨(conjE h₀ hu₀).measurable, hNc h₀ (Or.inl hh₀)⟩
    · exact ⟨(lmulE h₀'⁻¹ hui₀').measurable, hW'l _ hi₀'⟩
    · exact ⟨(conjE h₀'⁻¹ hui₀').measurable, hNc _ (Or.inr hi₀')⟩

  have aW : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.2 hW
  have aW' : ∀ᵐ x ∂μW', Matrix.of x ∈ UWset k r z' := ae_iff.2 hW'
  have aN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hN
  have q11 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.1.1 ∈ UWset k r z :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_fst).ae aW
  have q12 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.1.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_fst).ae aN
  have q21 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.2.1 ∈ UWset k r z' :=
    (Measure.quasiMeasurePreserving_fst.comp Measure.quasiMeasurePreserving_snd).ae aW'
  have q22 : ∀ᵐ p ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of p.2.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae aN

  let e₂ : Wp ≃L[ℂ] Wp := ContinuousLinearEquiv.equivOfInverse (π h₀) (π h₀⁻¹)
    (fun x => rep_inv hπ hi₀ hh₀ (Matrix.nonsing_inv_mul _ hu₀) x)
    (fun x => rep_inv hπ hh₀ hi₀ (Matrix.mul_nonsing_inv _ hu₀) x)
  let e₁ : Wq ≃L[ℂ] Wq := ContinuousLinearEquiv.equivOfInverse (π' h₀'⁻¹) (π' h₀')
    (fun x => rep_inv hπ' hh₀' hi₀' (Matrix.mul_nonsing_inv _ hu₀') x)
    (fun x => rep_inv hπ' hi₀' hh₀' (Matrix.nonsing_inv_mul _ hu₀') x)
  let L : (Wq →L[ℂ] Wp) ≃L[ℂ] (Wq →L[ℂ] Wp) := e₁.arrowCongr e₂
  have hL : ∀ X : Wq →L[ℂ] Wp, L X = (π h₀).comp (X.comp (π' h₀')) := by
    intro X; ext y; rfl
  rw [← hL]
  unfold besselJ
  refine integral_transfer _ hΦ hΦe L _ _ ?_
  filter_upwards [q11, q12, q21, q22] with p hK hM hK' hM'
  obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := p
  rw [hL]
  set K : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of a
  set M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of b
  set K' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of a'
  set M' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of b'
  have ep : psi k r z c (h₀ * M * h₀⁻¹) = psi k r z c M := by
    unfold psi; rw [(unitary_weyl_normal_holds k r z hz h₀ hh₀ M hM).2]
  have ep' : psi k r z' c (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) = psi k r z' c M' := by
    unfold psi; rw [(unitary_weyl_normal_holds k r z' hz' h₀'⁻¹ hi₀' M' hM').2]
  have earg : (h₀ * K)⁻¹ * (h₀ * M * h₀⁻¹)⁻¹ * (h₀ * g * h₀') * (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) *
      (h₀'⁻¹ * K') = K⁻¹ * M⁻¹ * g * M' * K' := by
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu₀,
      Matrix.nonsing_inv_nonsing_inv _ hu₀', Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.mul_nonsing_inv_cancel_left _ _ hu₀']
  have eπ : π (h₀ * K) = (π h₀).comp (π K) := hπ.2 h₀ hh₀ K hK
  have einv : (h₀'⁻¹ * K')⁻¹ = K'⁻¹ * h₀' := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu₀']
  have eπ' : π' (K'⁻¹ * h₀') = (π' K'⁻¹).comp (π' h₀') := hπ'.2 _ (WeylGroupFacts.uw_inv hK') _ hh₀'
  show (psi k r z c (h₀ * M * h₀⁻¹) * star (psi k r z' c (h₀'⁻¹ * M' * h₀'⁻¹⁻¹))) •
      ((π (h₀ * K)).comp ((F ((h₀ * K)⁻¹ * (h₀ * M * h₀⁻¹)⁻¹ * (h₀ * g * h₀') *
        (h₀'⁻¹ * M' * h₀'⁻¹⁻¹) * (h₀'⁻¹ * K'))).comp (π' (h₀'⁻¹ * K')⁻¹))) =
    (π h₀).comp (((psi k r z c M * star (psi k r z' c M')) •
      ((π K).comp ((F (K⁻¹ * M⁻¹ * g * M' * K')).comp (π' K'⁻¹)))).comp (π' h₀'))
  rw [ep, ep', earg, eπ, einv, eπ']
  ext y
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, map_smul]
end Formalism.QuantumDeterminants
