-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.phiI_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:15:45.636165+00:00
-- url     : https://prove2.me/submissions/11e0a0b1-7388-4924-9f8d-25fe292d4f47

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Formalism_L2_Pj_DatLin_phi1_tmul
import Theorems.Thm_Formalism_L2_Pj_DatLin_phiI_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (t : ℝ ⊗[ℤ] (ι → 𝓞 E)) (τ : Ψ) (i : ι) :
    phiI Ψ t τ i = phi1 Ψ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E) t i) τ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp [phiI_tmul, phi1_tmul, TensorProduct.piRightHom_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
end Formalism.L2.Pj.DatLin
