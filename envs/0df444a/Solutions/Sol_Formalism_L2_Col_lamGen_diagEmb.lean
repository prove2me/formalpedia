-- Prove2me | solution 1 for Formalism.L2.Col.lamGen_diagEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:03:16.527638+00:00
-- url     : https://prove2.me/submissions/5c90559b-c5d6-498d-9676-256277f7d106

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
import Theorems.Thm_Formalism_L2_Col_supSum_diagMat
import Theorems.Thm_Formalism_L2_Col_blkDet_diagEmb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
namespace Formalism.L2.Col
theorem _root_.solution (ψ : AddChar κ K) (χ : ℕ → κˣ →* Kˣ) {s a : ℕ} (h : s ≤ n) (ha : a ≤ s) (bl : List ℕ) (S : Finset ℕ)
    (hs : ∀ i : ℕ, s ≤ i → bl.length < coarse a bl i) (g : ↥(uniUT s κ a bl)) :
    lamGen ψ χ n a bl S ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ = lamGen ψ χ s a bl S g := by
  unfold lamGen
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply]
  congr 1
  · apply Units.ext
    show ψ (supSum a S (diagMat s n (g.1 : Matrix (Fin s) (Fin s) κ))) = ψ (supSum a S (g.1 : Matrix (Fin s) (Fin s) κ))
    rw [supSum_diagMat h ha]
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    have e1 : Subgroup.inclusion (uniUT_le_blockUT n κ a bl) ⟨diagEmb κ h g.1, diagEmb_mem_uniUT h g.2⟩ =
        ⟨diagEmb κ h g.1, uniUT_le_blockUT n κ a bl (diagEmb_mem_uniUT h g.2)⟩ := rfl
    have e2 : Subgroup.inclusion (uniUT_le_blockUT s κ a bl) g = ⟨g.1, uniUT_le_blockUT s κ a bl g.2⟩ := rfl
    rw [e1, e2]
    unfold detChar
    rw [MonoidHom.finset_prod_apply, MonoidHom.finset_prod_apply]
    apply Finset.prod_congr rfl
    intro c hc
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    congr 1
    have hcl := Finset.mem_range.mp hc
    exact blkDet_diagEmb h (coarse a bl) (c + 1) (fun i hi => by have := hs i hi; omega) g.1 _ _
end Formalism.L2.Col
