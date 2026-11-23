-- Prove2me | solution 1 for Formalism.L2.Pj.dom_lact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:54.525344+00:00
-- url     : https://prove2.me/submissions/133c0e79-19ca-4290-8921-7b46f13760a1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Theorems.Thm_Formalism_L2_Pj_gram_eq
import Theorems.Thm_Formalism_L2_Pj_ustab_mat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace Formalism.L2.Pj
theorem _root_.solution (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {γ : GL (Fin r) E}
    (hγ : IsUStab X.Gm X.Λ γ) : lact γ x ∈ X.dom := by
  have hU := ustab_mat hγ
  have hcc : ∀ (σ : E →+* ℂ) (a : E), σ (cc a) = starRingEnd ℂ (σ a) := by
    intro σ a
    exact NumberField.IsCMField.complexEmbedding_complexConj E σ a
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hm : mat (lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ := rfl
  have hc : ((γ : Matrix (Fin r) (Fin r) E).map cc).map τ.1 =
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) := by
    ext a b
    simp only [Matrix.map_apply]
    exact hcc _ _
  have key : ((γ : Matrix (Fin r) (Fin r) E).map τ.1)ᵀ * X.Gm.map τ.1 *
      ((γ : Matrix (Fin r) (Fin r) E).map τ.1).map (starRingEnd ℂ) = X.Gm.map τ.1 := by
    rw [← hc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hU]
  have hgr : gram τ.1 X.Gm (mat (lact γ x) τ) = gram τ.1 X.Gm (mat x τ) := by
    rw [hm, gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
    rw [show ∀ M1 M2 M3 M4 M5 : Matrix (Fin r) (Fin r) ℂ,
        M1 * M2 * M3 * (M4 * M5) = M1 * (M2 * M3 * M4) * M5 from
      fun M1 M2 M3 M4 M5 => by simp only [Matrix.mul_assoc], key]
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    refine mul_ne_zero ?_ hdet
    rw [show ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det = τ.1 (γ : Matrix (Fin r) (Fin r) E).det from
      (RingHom.map_det τ.1 _).symm]
    exact (map_ne_zero τ.1).mpr ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit γ)).ne_zero
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hgr]
    exact hi
end Formalism.L2.Pj
