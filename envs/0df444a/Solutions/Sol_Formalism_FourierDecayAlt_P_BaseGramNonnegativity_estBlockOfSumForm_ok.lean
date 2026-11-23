-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:55.534918+00:00
-- url     : https://prove2.me/submissions/bc4f1948-8b5a-464f-8690-cc50f5366820

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_baseGram_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_BaseGramNonnegativity_Wb_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BaseGramNonnegativity
open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity
theorem _root_.solution : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)
end Formalism.FourierDecayAlt.P.BaseGramNonnegativity
