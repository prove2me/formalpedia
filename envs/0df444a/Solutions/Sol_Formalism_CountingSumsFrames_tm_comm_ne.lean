-- Prove2me | solution 1 for Formalism.CountingSumsFrames.tm_comm_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:12.343189+00:00
-- url     : https://prove2.me/submissions/f416f6af-dc8a-424f-8b31-9c4a6f5a746e

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_comm_XD

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
theorem _root_.solution (LL : Letters N) (j : ℕ) (i i' : Fin N) (hii : i ≠ i') (c d a b : Fin r)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    tm (p := p) LL j i c d (tm (p := p) LL j i' a b y) = tm (p := p) LL j i' a b (tm (p := p) LL j i c d y) := by
  have hcomm : ∀ u v u' v' : Fin N × Fin r, u.1 = i → v.1 = i → u'.1 = i' → v'.1 = i' →
      X u * pderiv v (X u' * pderiv v' y) = X u' * pderiv v' (X u * pderiv v y) := by
    intro u v u' v' hu hv hu' hv'
    have h1 : u' ≠ v := fun h => hii (by rw [← hv, ← h, hu'])
    have h2 : u ≠ v' := fun h => hii (by rw [← hu, h, hv'])
    have := comm_XD (k := ℚ_[p]) u v u' v' y
    rw [if_neg h1, if_neg h2, sub_zero, sub_eq_zero] at this
    exact this
  have hform : ∀ (l : Fin N) (e f : Fin r), ∃ (α : ℚ_[p]) (u v : Fin r),
      ∀ z, tm (p := p) LL j l e f z = α • (X (l, u) * pderiv (l, v) z) := by
    intro l e f
    by_cases hl : (l : ℕ) < j
    · by_cases hv : LL.vec l = true
      · refine ⟨1, e, f, fun z => ?_⟩
        simp only [tm, if_pos hl, if_pos hv, one_smul]
        rfl
      · refine ⟨-1, f, e, fun z => ?_⟩
        simp only [tm, if_pos hl, if_neg hv, neg_one_smul]
        rfl
    · refine ⟨0, e, f, fun z => ?_⟩
      simp only [tm, if_neg hl, zero_smul]
      rfl
  obtain ⟨α, u, v, hα⟩ := hform i c d
  obtain ⟨β, u', v', hβ⟩ := hform i' a b
  simp only [hα, hβ, Derivation.map_smul, map_smul, mul_smul_comm, smul_smul]
  rw [mul_comm β α, hcomm (i, u) (i, v) (i', u') (i', v') rfl rfl rfl rfl]
end Formalism.CountingSumsFrames
