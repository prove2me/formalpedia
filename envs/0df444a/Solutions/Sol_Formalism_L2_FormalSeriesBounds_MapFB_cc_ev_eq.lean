-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.MapFB.cc_ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:35:04.333815+00:00
-- url     : https://prove2.me/submissions/0d6fe36b-1e80-4874-99c8-83bf711c4731

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePFBMapSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGaugeMapSt
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}
private theorem cc_subst_lemma_2 {σ τ A : Type} [Finite σ] [CommRing A] (a : σ → MvPowerSeries τ A)
    (ha : ∀ s, constantCoeff (a s) = 0) (f : MvPowerSeries σ A) :
    constantCoeff (MvPowerSeries.subst a f) = constantCoeff f := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha)]
  rw [finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [map_finsuppProd]
    simp only [map_pow, ha, Finsupp.prod]
    rw [Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (zero_pow hs), smul_zero]
end Formalism.L2.FormalSeriesBounds.MapFB
namespace Formalism.L2.FormalSeriesBounds
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MapFB
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.MapFB
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {R : Type} [CommRing R] {d : ℕ}
namespace Formalism.L2.FormalSeriesBounds.MapFB
theorem _root_.solution {m n : ℕ} (a : Fin m → Pt R n d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (f : PS R m d) : constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  exact cc_subst_lemma_2 (fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f
end Formalism.L2.FormalSeriesBounds.MapFB
