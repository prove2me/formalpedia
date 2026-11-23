-- Prove2me | solution 1 for Formalism.CountingSumsFrames.comm_wtsp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:59:20.591487+00:00
-- url     : https://prove2.me/submissions/011c8be3-837c-4de7-bd99-9ee304669087

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_cartan_eig
import Theorems.Thm_Formalism_CountingSumsFrames_eig_supp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hT : ∀ c x, T (glAct p LL j c c x) = glAct p LL j c c (T x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, T x ∈ WtSpC p LL j univ μ := by
  intro x hx
  have heig : ∀ c, glAct p LL j c c (T x) = ((μ c : ℤ) : ℚ_[p]) • T x := by
    intro c
    rw [← hT, cartan_eig LL j μ x hx c, map_smul]
  unfold WtSpC
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  simp only [Set.mem_setOf_eq]
  intro c _
  have := eig_supp LL j c (μ c) (T x) (heig c)
  rw [MvPolynomial.mem_restrictSupport_iff] at this
  exact this hm
end Formalism.CountingSumsFrames
