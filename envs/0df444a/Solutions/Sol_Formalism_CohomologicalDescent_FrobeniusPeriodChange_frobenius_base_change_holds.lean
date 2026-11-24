-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_base_change_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:06.993966+00:00
-- url     : https://prove2.me/submissions/fccb6026-d1f6-4dc5-a91e-0ad04d355553

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_dvd_mul_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : PhiBaseChange := by
  intro k _ n l h g g' P hl
  have hs : HasSubst (X ^ l : k⟦X⟧) := HasSubst.X_pow hl.ne'
  let fr : k⟦X⟧ →+* k⟦X⟧ := (substAlgHom hs).toRingHom
  have hfr : ∀ y, fr y = frob0 l y := fun y => by
    change substAlgHom hs y = _
    rw [coe_substAlgHom hs]; rfl
  let g2 : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ :=
    Units.map (fr.mapMatrix :
      Matrix (Fin n) (Fin n) k⟦X⟧ →+* Matrix (Fin n) (Fin n) k⟦X⟧).toMonoidHom g'
  have hg2 : (g' : Matrix (Fin n) (Fin n) k⟦X⟧).map (frob0 l) = (g2 : Matrix (Fin n) (Fin n) k⟦X⟧) := by
    refine Matrix.ext fun a b => ?_
    change frob0 l _ = fr _
    rw [hfr]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * M *
      (g : Matrix (Fin n) (Fin n) k⟦X⟧), ?_⟩
    unfold chgPhi
    rw [hg2]
    calc _ = ((g⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧) * (P *
          ((g2 : Matrix (Fin n) (Fin n) k⟦X⟧) *
            ((g2⁻¹ : (Matrix (Fin n) (Fin n) k⟦X⟧)ˣ) : Matrix (Fin n) (Fin n) k⟦X⟧)) * M) *
          (g : Matrix (Fin n) (Fin n) k⟦X⟧) := by simp only [mul_assoc]
      _ = _ := by
        rw [Units.mul_inv, mul_one, hM, Matrix.mul_smul, Matrix.smul_mul, mul_one, Units.inv_mul]
  · intro x t hx
    exact minors_dvd_mul_holds (k⟦X⟧) n n n n t x _ P _ hx
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
