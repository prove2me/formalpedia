-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.Van.subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:18.997117+00:00
-- url     : https://prove2.me/submissions/9762c1e8-dc03-44ab-bd24-cd8ff774916d

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_mul_right
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries
variable {C : Type} [Field C]
variable {τ : Type}
namespace Formalism.L2.FormalSeriesBounds
namespace Van
theorem _root_.solution {σ : Type} [Finite σ] {T : Set τ} (S : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s ∈ S, Van T (a s)) {f : MvPowerSeries σ C}
    (hf : ∀ e : σ →₀ ℕ, (∀ s ∈ e.support, s ∉ S) → coeff e f = 0) : Van T (MvPowerSeries.subst a f) := by
  intro ν hν
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases h : ∀ s ∈ e.support, s ∉ S
  · rw [hf e h, zero_smul]
  · push Not at h
    obtain ⟨s, hs, hsS⟩ := h
    have hv : Van T (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs]
      apply Van.mul_right
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
      show Van T (a s ^ e s)
      rw [hm, pow_succ']
      exact (haS s hsS).mul_right _
    rw [hv ν hν, smul_zero]
end Van
end Formalism.L2.FormalSeriesBounds
