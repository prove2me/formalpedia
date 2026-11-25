-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.VP.cc_hL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:36:52.472523+00:00
-- url     : https://prove2.me/submissions/d446cce3-4616-42f3-81f3-c4143b108eae

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ConstantCoeffSinglePointZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IntSProd
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_cc_h
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_EqOn_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_prod
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VP_hs
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
namespace VP
section Inv
variable {C : Type} [Field C] {V : VF C} {σ : Type}
end Inv
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]
end VP
end Formalism.L2.FormalSeriesBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open Formalism.L2.FormalSeriesBounds.VP
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
namespace Formalism.L2.FormalSeriesBounds.VP
theorem _root_.solution (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]
end Formalism.L2.FormalSeriesBounds.VP
