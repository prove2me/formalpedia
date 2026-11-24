-- Prove2me | solution 1 for Formalism.QuantumDeterminants.bessel_unipotent_equiv_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:47.267242+00:00
-- url     : https://prove2.me/submissions/10c6ec30-d488-4c4b-908a-17f79431ac37

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_star_psi_inv
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_coe_lmulEquiv
import Theorems.Thm_Formalism_QuantumDeterminants_BesselUnipotentEquiv_of_lmulM
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_additive_character_holds
import Theorems.Thm_Formalism_QuantumDeterminants_unipotent_subgroup_holds


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
open BesselUnipotentEquiv
namespace Formalism.QuantumDeterminants
theorem _root_.solution : BesselNEquiv := by
  intro Wp Wq _ _ _ _ _ _ k r z z' c π π' μW μN μW' _ _ _ F hz hz' hNc hinvN g n₀ hn₀ n₀' hn₀'
  have hinv' : n₀'⁻¹ ∈ Nset k r := (unipotent_subgroup_holds k r).2.2 n₀' hn₀'
  have hu0 : IsUnit n₀.det := WeylGroupFacts.isUnit_of_uh hn₀.1
  have hu0' : IsUnit n₀'.det := WeylGroupFacts.isUnit_of_uh hn₀'.1
  have hui' : IsUnit (n₀'⁻¹).det := WeylGroupFacts.isUnit_of_uh hinv'.1
  let e1 := lmulEquiv (k := k) (r := r) n₀ hu0
  let e2 := lmulEquiv (k := k) (r := r) n₀'⁻¹ hui'
  let Φ := ((MeasurableEquiv.refl (Mt k r)).prodCongr e1).prodCongr
    ((MeasurableEquiv.refl (Mt k r)).prodCongr e2)
  have hΦapp : ∀ q : (Mt k r × Mt k r) × (Mt k r × Mt k r),
      Φ q = ((q.1.1, lmulM n₀ q.1.2), (q.2.1, lmulM n₀'⁻¹ q.2.2)) := fun q => rfl
  have hp1 : MeasurePreserving e1 μN μN :=
    ⟨e1.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀ hn₀⟩
  have hp2 : MeasurePreserving e2 μN μN :=
    ⟨e2.measurable, by rw [coe_lmulEquiv]; exact hinvN n₀'⁻¹ hinv'⟩
  have hpΦ : MeasurePreserving Φ ((μW.prod μN).prod (μW'.prod μN))
      ((μW.prod μN).prod (μW'.prod μN)) :=
    ((MeasurePreserving.id μW).prod hp1).prod ((MeasurePreserving.id μW').prod hp2)
  have haeN : ∀ᵐ x ∂μN, Matrix.of x ∈ Nset k r := ae_iff.2 hNc
  have hae1 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.1.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have hae2 : ∀ᵐ q ∂((μW.prod μN).prod (μW'.prod μN)), Matrix.of q.2.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae haeN)
  have key : ∀ h m h' m' : Mt k r, Matrix.of m ∈ Nset k r → Matrix.of m' ∈ Nset k r →
      (psi k r z c (n₀ * Matrix.of m) * star (psi k r z' c (n₀'⁻¹ * Matrix.of m'))) •
        ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
          (n₀'⁻¹ * Matrix.of m') * Matrix.of h')).comp (π' (Matrix.of h')⁻¹))) =
      (psi k r z c n₀ * psi k r z' c n₀') •
        ((psi k r z c (Matrix.of m) * star (psi k r z' c (Matrix.of m'))) •
          ((π (Matrix.of h)).comp ((F ((Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g *
            Matrix.of m' * Matrix.of h')).comp (π' (Matrix.of h')⁻¹)))) := by
    intro h m h' m' hm hm'
    have hmat : (Matrix.of h)⁻¹ * (n₀ * Matrix.of m)⁻¹ * (n₀ * g * n₀') *
        (n₀'⁻¹ * Matrix.of m') * Matrix.of h' =
        (Matrix.of h)⁻¹ * (Matrix.of m)⁻¹ * g * Matrix.of m' * Matrix.of h' := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu0, Matrix.mul_nonsing_inv_cancel_left _ _ hu0']
    rw [hmat, smul_smul]
    congr 1
    rw [(additive_character_holds k r z c hz n₀ hn₀).1 _ hm, (additive_character_holds k r z' c hz' _ hinv').1 _ hm',
      star_mul', star_psi_inv z' c hz' n₀' hn₀']
    ring
  unfold besselJ
  rw [← hpΦ.integral_comp', ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hae1, hae2] with q hm hm'
  rw [hΦapp]
  simp only [of_lmulM]
  exact key q.1.1 q.1.2 q.2.1 q.2.2 hm hm'
end Formalism.QuantumDeterminants
