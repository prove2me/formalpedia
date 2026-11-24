-- Prove2me | solution 1 for Formalism.L2.DIV.localization_gLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.629712+00:00
-- url     : https://prove2.me/submissions/6bcf984d-819c-432d-810e-d70387b12386

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
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (M : Submodule (𝓞 K) (Fin n → K)) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (gLat g M) = gLat g (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M) := by
  ext x
  constructor
  · rintro ⟨s, hs, y, hy, hyx⟩
    have hyx' : (g : Matrix (Fin n) (Fin n) K) *ᵥ y = s • x := hyx
    refine ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x, ⟨s, hs, ?_⟩, ?_⟩
    · have : s • (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = y := by
        rw [← Matrix.mulVec_smul, ← hyx', Matrix.mulVec_mulVec]
        simp
      rw [this]
      exact hy
    · show (g : Matrix (Fin n) (Fin n) K) *ᵥ (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) = x
      rw [Matrix.mulVec_mulVec]
      simp
  · rintro ⟨y, ⟨s, hs, hy⟩, rfl⟩
    refine ⟨s, hs, s • y, hy, ?_⟩
    show (g : Matrix (Fin n) (Fin n) K) *ᵥ (s • y) = s • ((g : Matrix (Fin n) (Fin n) K) *ᵥ y)
    rw [Matrix.mulVec_smul]
end Formalism.L2.DIV
