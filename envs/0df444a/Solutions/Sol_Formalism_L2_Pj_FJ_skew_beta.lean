-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.skew_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:35.984535+00:00
-- url     : https://prove2.me/submissions/f3b5a133-6882-4267-9865-aa9b498a6cec

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (hb : ∀ k, IsSkew (zBas X cu k)) (τ : E →+* ℂ)
    (t : Fin (nZ X ρ) → ℝ) :
    cM (∑ k, (t k : ℂ) • (zBas X cu k).map τ) = -(∑ k, (t k : ℂ) • (zBas X cu k).map τ)ᵀ := by
  have h' := hb
  unfold IsSkew at h'
  ext a b
  simp only [cM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, ← emb_cc', h', map_neg, mul_neg, Finset.sum_neg_distrib]
end Formalism.L2.Pj.FJ
