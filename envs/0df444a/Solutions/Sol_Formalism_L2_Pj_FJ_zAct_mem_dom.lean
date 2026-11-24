-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.zAct_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:47.143278+00:00
-- url     : https://prove2.me/submissions/ef25a06c-a0dd-4425-bcd0-8d08b707ca48

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_Formalism_L2_Pj_FJ_cM_mul
import Theorems.Thm_Formalism_L2_Pj_FJ_unitary_core
import Theorems.Thm_Formalism_L2_Pj_FJ_det_ne_core
import Theorems.Thm_Formalism_L2_Pj_FJ_zMatC_eq
import Theorems.Thm_Formalism_L2_Pj_FJ_gram_eq
import Theorems.Thm_Formalism_L2_Pj_FJ_herm_g
import Theorems.Thm_Formalism_L2_Pj_FJ_iso_F
import Theorems.Thm_Formalism_L2_Pj_FJ_skew_beta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k))
    (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) (hx : x ∈ X.dom) : zAct X cu t x ∈ X.dom := by
  unfold zAct ReciprocityTheory.ChartRestriction.G.FD.Data.dom at *
  unfold GG at *
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  unfold dmin mat at *
  beta_reduce
  set M := zMatC X cu.e (τ : E →+* ℂ) (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map (τ : E →+* ℂ)) with hMdef
  have hU : Mᵀ * X.Gm.map (τ : E →+* ℂ) * cM M = X.Gm.map (τ : E →+* ℂ) := by
    rw [hMdef, zMatC_eq]
    exact unitary_core _ _ _ (herm_g X _) (iso_F X cu _) (skew_beta X cu hb _ t)
  have hD : M.det ≠ 0 := by
    rw [hMdef, zMatC_eq]
    exact det_ne_core _ _ _ (iso_F X cu _)
  have hU' : ∀ Y : Matrix (Fin r) (Fin r) ℂ,
      Mᵀ * (X.Gm.map (τ : E →+* ℂ) * (cM M * Y)) = X.Gm.map (τ : E →+* ℂ) * Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hU]
  have hG : ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (M * of (x τ)) =
      ReciprocityTheory.ChartRestriction.G.FD.gram (τ : E →+* ℂ) X.Gm (of (x τ)) := by
    simp only [gram_eq, Matrix.transpose_mul, cM_mul, Matrix.mul_assoc, hU']
  refine ⟨?_, fun i => ?_⟩
  · show (M * of (x τ)).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hD hdet
  · have := hpos i
    rw [← hG] at this
    exact this
end Formalism.L2.Pj.FJ
