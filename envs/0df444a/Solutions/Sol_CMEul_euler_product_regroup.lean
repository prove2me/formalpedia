-- Prove2me | solution 1 for CMEul.euler_product_regroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:51.600351+00:00
-- url     : https://prove2.me/submissions/c7cc2d7f-c5ac-4785-a0bb-3fc30ce236d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_Regroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory
namespace CMEul
theorem _root_.solution : StepRegroup := by
  intro F E _ _ _ _ _ _ M hm hf
  classical
  let f : {P : Ideal (𝓞 E) // P.IsMaximal} → {v : Ideal (𝓞 F) // v.IsMaximal} := fun P =>
    ⟨P.1.comap (algebraMap (𝓞 F) (𝓞 E)), by
      have := P.2
      exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P.1⟩
  let e := Equiv.sigmaFiberEquiv f
  have h1 : HasProd (fun x => eulerFac E M (e x).1) (lValEta E M) :=
    (e.hasProd_iff (f := fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => eulerFac E M P.1)).mpr
      hm.hasProd
  have hfib : ∀ v : {v : Ideal (𝓞 F) // v.IsMaximal},
      HasProd (fun c : {x // f x = v} => eulerFac E M (e ⟨v, c⟩).1) (eulerF F E M v.1) := by
    intro v
    let ev : {x // f x = v} ≃
        {P : Ideal (𝓞 E) // P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} :=
      { toFun := fun x => ⟨x.1.1, x.1.2, congrArg Subtype.val x.2⟩
        invFun := fun c => ⟨⟨c.1, c.2.1⟩, Subtype.ext c.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (ev.hasProd_iff (f := fun c : {P : Ideal (𝓞 E) // P.IsMaximal ∧
      P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.1} => eulerFac E M c.1)).mpr (hf v.1 v.2)
  have h2 : HasProd (fun v : {v : Ideal (𝓞 F) // v.IsMaximal} => eulerF F E M v.1) (lValEta E M) :=
    h1.sigma hfib
  exact h2.tprod_eq
end CMEul
