-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ShearMeasurability.lvl_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:26:28.959289+00:00
-- url     : https://prove2.me/submissions/5d7f3824-d27b-4c26-9b6f-ad7b97b63e84

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShearMeasurability

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.ShearMeasurability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.ShearMeasurability
theorem _root_.solution {ρ : ι → ℕ} {F : (ι → ℂ) → ι → ℂ} (hFm : Measurable F) (hF : ShearCond ρ F) (n : ℕ) :
    MeasurePreserving (lvl ρ F n) volume volume := by
  classical
  let p : ι → Prop := fun q => ρ q ≠ n
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) p
  have he : MeasurePreserving e volume
      ((volume : Measure ({q // p q} → ℂ)).prod (volume : Measure ({q // ¬ p q} → ℂ))) :=
    measurePreserving_piEquivPiSubtypeProd (fun _ => (volume : Measure ℂ)) p
  let x0 : ({q // p q} → ℂ) → ι → ℂ := fun z => e.symm (z, 0)
  let φ : ({q // p q} → ℂ) → {q // ¬ p q} → ℂ := fun z q => F (x0 z) q - x0 z q
  have hx0 : Measurable x0 := e.symm.measurable.comp (measurable_id.prodMk measurable_const)
  have hφ : Measurable φ := by
    apply measurable_pi_lambda
    intro q
    exact ((measurable_pi_apply _).comp (hFm.comp hx0)).sub ((measurable_pi_apply _).comp hx0)
  let T : ({q // p q} → ℂ) × ({q // ¬ p q} → ℂ) → ({q // p q} → ℂ) × ({q // ¬ p q} → ℂ) :=
    fun pr => (pr.1, pr.2 + φ pr.1)
  have hT : MeasurePreserving T ((volume : Measure ({q // p q} → ℂ)).prod volume)
      ((volume : Measure ({q // p q} → ℂ)).prod volume) :=
    (MeasurePreserving.id _).skew_product (g := fun z y => y + φ z)
      (measurable_snd.add (hφ.comp measurable_fst))
      (Filter.Eventually.of_forall fun z => (measurePreserving_add_right _ (φ z)).map_eq)
  have heq : lvl ρ F n = e.symm ∘ T ∘ e := by
    funext x
    apply e.injective
    simp only [Function.comp, MeasurableEquiv.apply_symm_apply]
    rw [MeasurableEquiv.piEquivPiSubtypeProd_apply]
    ext q
    · have hq : ρ q.1 ≠ n := q.2
      simp [T, lvl, hq]
    · have hq : ρ q.1 = n := not_not.1 q.2
      simp only [T, φ, x0, lvl, Pi.add_apply]
      rw [if_pos hq]
      have hagree : ∀ r, ρ r < ρ q.1 →
          x r = e.symm ((fun r : {q // p q} => x r), 0) r := by
        intro r hr
        have hpr : p r := by
          show ρ r ≠ n
          omega
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, hpr]
      have h2 := hF q.1 x _ hagree
      linear_combination h2
  rw [heq]
  exact (he.symm e).comp (hT.comp he)
end Formalism.FourierDecayAlt.P.ShearMeasurability
