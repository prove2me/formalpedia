-- Prove2me | solution 1 for Formalism.L2.DIV.nabP_colLat_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:12:53.839624+00:00
-- url     : https://prove2.me/submissions/73343eb0-6c6d-412f-ba2c-2d0a66459968

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (B : ι → GL (Fin n) K) (w : HeightOneSpectrum (𝓞 K)) {F : Pol K ι n} (hF : F ∈ nabP lam fun τ => colLat (B τ)) :
    actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have h := hF
  simp only [nabP, transLat, Submodule.mem_iInf] at h
  exact h w B fun _ => rfl
end Formalism.L2.DIV
