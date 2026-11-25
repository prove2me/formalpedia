-- Prove2me | solution 1 for Formalism.CountingSumsFrames.monomial_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:41:26.622836+00:00
-- url     : https://prove2.me/submissions/353634fc-3ef7-47f5-a331-23c01ddcb83c

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_polynomial_finite_weights
import Theorems.Thm_Formalism_CountingSumsFrames_count_HW
import Theorems.Thm_Formalism_CountingSumsFrames_tie_onto
import Theorems.Thm_Formalism_CountingSumsFrames_tie_into
import Theorems.Thm_Formalism_CountingSumsFrames_FrL_apply
import Theorems.Thm_Formalism_CountingSumsFrames_finrank_MMw
import Theorems.Thm_Formalism_CountingSumsFrames_YYsp_eq
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_ne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution : Formalism.GM.M.MonoCount := by
  intro p _ N r _ _ LL T hadm ρ hρ _ i n hS fw hfw
  classical
  obtain ⟨S, hSw⟩ := polynomial_finite_weights (p := p) (r := r) (LL.setTies T n) (T.pos i + 1 + 1)
  have hmem0 : ∀ μ : Fin r → ℤ, GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr ≠ ⊥ →
      ∃ v ∈ GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr, v ≠ 0 := fun μ h =>
    Submodule.exists_mem_ne_zero_of_ne_bot h
  have hcount := count_HW (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr S hSw
    (fun μ => T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))
    (fun μ => by
      have := tie_into LL T hadm i ρ hρ n hS _ (hfw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)).1
      rwa [add_sub_cancel_right] at this)
    (fun μ hne => by
      obtain ⟨v, hv, hv0⟩ := hmem0 μ hne
      obtain ⟨f, hf, hfv⟩ := tie_onto LL T hadm i ρ hρ n hS μ hv
      have hf0 : f ≠ 0 := by
        rintro rfl
        apply hv0
        rw [← hfv, ← FrL_apply, map_zero]
      have hb : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
          (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1) ≠ ⊥ := fun hb => hf0 (by
        rw [hb] at hf; exact (Submodule.mem_bot _).mp hf)
      exact Ffull_ne LL T hadm i ρ n _ _ (hfw _).1 ((hfw _).2 hb) hS)
  rw [hcount]
  obtain ⟨g, hg⟩ : ∃ g : (Fin r → ℤ) → ℕ, g = fun μ =>
      Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))) := ⟨_, rfl⟩
  have hterm : ∀ w, Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) *
      Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw w)) =
      g (Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) w) := by
    intro w
    have e : Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) w =
      w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) := rfl
    rw [e, hg]
    show _ = Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1))
          (w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ)) ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (w - ((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ) +
            ((n i : ℕ) : ℤ) • Pi.single ρ 1))))
    rw [sub_add_cancel, finrank_MMw LL T hadm i ρ hρ n hS w, YYsp_eq]
  have hsum : ∑ μ ∈ S, Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
          Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr
          (T.Ffull p (LL.setTies T n) i ρ (n i) (fw (μ + ((n i : ℕ) : ℤ) • Pi.single ρ 1)))) = ∑ μ ∈ S, g μ := by
    rw [hg]
  rw [hsum]
  simp_rw [hterm]
  rw [finsum_comp_equiv (Equiv.subRight (((n i : ℕ) : ℤ) • (Pi.single ρ 1 : Fin r → ℤ))) (f := g),
    finsum_eq_sum_of_support_subset]
  intro μ hμ
  rw [Function.mem_support, hg] at hμ
  have h1 : GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) μ ⊓
      Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr ≠ ⊥ := by
    intro hb
    apply hμ
    beta_reduce
    rw [hb, finrank_bot, zero_mul]
  obtain ⟨v, hv, hv0⟩ := hmem0 μ h1
  by_contra hn
  apply hv0
  have h2 := hSw v hv.2.1 μ hn
  have h3 : (GA p (LL.setTies T n) (T.pos i + 1 + 1)).comp μ v = v := hv.1.1
  rw [← h3, h2]
end Formalism.CountingSumsFrames
