-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mulLast_bwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:16.968408+00:00
-- url     : https://prove2.me/submissions/3fa21aaf-2a18-48dc-9326-aae268b21353

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_withTop_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
import Theorems.Thm_Formalism_CountingSumsFrames_ycond_le_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hh : h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ))) :
    X (Fin.last K, c) * h ∈ YCond p LL j M := by
  classical
  have hsupp : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤ SuppLE p LL j M := by
    rw [Submodule.span_le]
    rintro _ ⟨d, g, hg, rfl⟩
    have hg' := ycond_le_supp (p := p) LL j _ hg
    show X (Fin.last K, d) * g ∈ restrictSupport ℚ_[p] _
    rw [X_mul_mem]
    rw [mem_restrictSupport_iff] at hg' ⊢
    refine hg'.trans ?_
    intro m hm
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [last_wt LL j hj hv]
    rw [← withTop_shift] at hm
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    split_ifs <;> omega
  have hstab : GlStable p LL j (Submodule.span ℚ_[p] {F | ∃ (d : Fin r)
      (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g}) := by
    intro a b x hx
    have key : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
        g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤
        (Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
          g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g}).comap
          (glAct p LL j a b) := by
      rw [Submodule.span_le]
      rintro _ ⟨d, g, hg, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, glAct_mul, last_X p LL j hj hv]
      refine Submodule.add_mem _ ?_
        (Submodule.subset_span ⟨d, _, ycond_glStable (p := p) LL j _ a b g hg, rfl⟩)
      split_ifs
      · exact Submodule.subset_span ⟨a, g, hg, rfl⟩
      · rw [zero_mul]; exact Submodule.zero_mem _
    exact key hx
  have hle : Submodule.span ℚ_[p] {F | ∃ (d : Fin r) (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]),
      g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) ∧ F = X (Fin.last K, d) * g} ≤ YCond p LL j M := by
    unfold YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (Submodule.subset_span ⟨c, h, hh, rfl⟩)
end Formalism.InvariantFactorPaths.L4
