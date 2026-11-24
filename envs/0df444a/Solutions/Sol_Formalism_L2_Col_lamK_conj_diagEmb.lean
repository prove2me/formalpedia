-- Prove2me | solution 1 for Formalism.L2.Col.lamK_conj_diagEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:54:12.265931+00:00
-- url     : https://prove2.me/submissions/03e50fe8-76c2-46f0-98b8-bc86895ce514

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount

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
theorem _root_.solution (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (h : r ≤ n) {bl : List ℕ} (g : GL (Fin r) κ) (M : ↥(HK n κ r bl)) :
    lamK χ n r bl ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ = lamK χ n r bl M := by
  unfold lamK
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have hD : diagEmb κ h g ∈ blockUT n κ r bl := by
    show ((diagEmb κ h g : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).BlockTriangular (fun i => coarse r bl i.val)
    intro i j hij
    show diagMat r n (g : Matrix (Fin r) (Fin r) κ) i j = 0
    simp only [diagMat]
    have hi : ¬ i.val < r := by
      intro hi
      have h0 : coarse r bl i.val = 0 := by simp only [coarse, blkIdx, if_pos hi]
      have hij' : coarse r bl j.val < coarse r bl i.val := hij
      omega
    rw [dif_neg (fun hc => hi hc.1)]
    exact Matrix.one_apply_ne (fun e => by subst e; exact lt_irrefl _ hij)
  have e : Subgroup.inclusion (HK_le_blockUT n κ r bl) ⟨diagEmb κ h g * M.1 * (diagEmb κ h g)⁻¹, HK_conj_diagEmb h g M.2⟩ =
      ⟨diagEmb κ h g, hD⟩ * Subgroup.inclusion (HK_le_blockUT n κ r bl) M * ⟨diagEmb κ h g, hD⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
end Formalism.L2.Col
