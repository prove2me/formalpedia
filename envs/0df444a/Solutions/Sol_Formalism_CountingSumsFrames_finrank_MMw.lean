-- Prove2me | solution 1 for Formalism.CountingSumsFrames.finrank_MMw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:31:56.953996+00:00
-- url     : https://prove2.me/submissions/5dd0c6fa-a784-44f2-9221-92733da506eb

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_tie_onto
import Theorems.Thm_Formalism_CountingSumsFrames_tie_into
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
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
namespace Formalism.CountingSumsFrames
theorem _root_.solution [NeZero r] (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ)
    (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i) (w : Fin r → ℤ) :
    Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) =
      Module.finrank ℚ_[p] (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) := by
  let Φ : MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w →ₗ[ℚ_[p]]
      (GlX.HWs (GA p (LL.setTies T n) (T.pos i + 1 + 1)) (w - ((n i : ℕ) : ℤ) • Pi.single ρ 1) ⊓
        Cset p (LL.setTies T n) (T.pos i + 1 + 1) T.J T.thr : Submodule ℚ_[p] _) :=
    ((FrL p (LL.setTies T n) T i ρ (n i)).comp (Submodule.subtype _)).codRestrict _
      (fun f => tie_into LL T hadm i ρ hρ n hS w f.2)
  have hΦ : ∀ f, ((Φ f : _) : MvPolynomial (Fin N × Fin r) ℚ_[p]) = T.Ffull p (LL.setTies T n) i ρ (n i) f.1 :=
    fun f => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    by_contra h0
    have h1 := Ffull_ne LL T hadm i ρ n w f.1 f.2 (fun h => h0 (Subtype.ext h)) hS
    apply h1
    rw [← hΦ f, hf]; rfl
  have hsurj : Function.Surjective Φ := by
    intro v
    obtain ⟨f, hf, hfv⟩ := tie_onto LL T hadm i ρ hρ n hS _ v.2
    rw [sub_add_cancel] at hf
    exact ⟨⟨f, hf⟩, Subtype.ext hfv⟩
  exact (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).finrank_eq
end Formalism.CountingSumsFrames
