-- Prove2me | solution 1 for Formalism.L2.Pj.nrmContOff_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:10:19.990526+00:00
-- url     : https://prove2.me/submissions/259106ff-d87f-4520-9402-7306f73da5e5

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NrmContPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MeasureTheory Topology NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
namespace Formalism.L2.Pj
theorem _root_.solution (h : GenFrEx Xo c) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ)
    (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P)))
    (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1))
    (hst : STLoc h Dd N uL wR jc) (hna : NrmAlong fn yP) (hfn : FnNe Xo c fn) (htr : FnTrdeg Xo c Dd) (hfg : FnFG Xo c)
    (hwb : ∀ Z, evC h Z (wR (jc Z)) ≠ 0) :
    NrmContOff h fn yP Dd N uL wR jc := by
  intro Z sg G f hf hf0
  obtain ⟨S, hSm, hS0, hloc⟩ := hst htr hfg hwb Z sg
  refine ⟨S, hSm, hS0, ?_⟩

  have hne : ∀ P : Om Z →+* ℂ, nrmC fn (yP Z) G f P ≠ 0 := by
    intro P
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
    have ha : a ≠ 0 := by rintro rfl; exact hf0 (zero_smul _ _)
    unfold nrmC
    refine mul_ne_zero ?_ ?_
    · rw [norm_ne_zero_iff, map_ne_zero]
      simpa using ha
    · exact Finset.prod_ne_zero_iff.2 fun i _ => by
        have := abs_pos.2 (hfn _ (yP Z P) i)
        positivity
  intro t0 ht0
  obtain ⟨U, hU, n, Q, hQc, hQ⟩ := hloc t0 ht0
  have hg : ContinuousOn (fun t => ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t))) (U ∩ Sᶜ) := by
    refine continuousOn_finset_sum _ fun k _ => ContinuousOn.log ?_ fun t _ => hne _
    refine hna Z sg hf hf0 (U ∩ Sᶜ) (fun t => Q k t) ?_ (fun a => hQc k a)
    intro t ht
    have hm : Q k t ∈ Set.range (fun k => Q k t) := ⟨k, rfl⟩
    rw [(hQ t ht).2] at hm
    exact hm.1
  have key : ∀ t ∈ U ∩ Sᶜ, ∑ᶠ P ∈ Set.range (fun k => Q k t), Real.log (nrmC fn (yP Z) G f P) =
      ∑ k, Real.log (nrmC fn (yP Z) G f (Q k t)) := fun t ht => by
    rw [finsum_mem_range (hQ t ht).1, finsum_eq_sum_of_fintype]
  have hgw := hg.continuousWithinAt ⟨mem_of_mem_nhds hU, ht0⟩
  rw [Set.inter_comm] at hgw
  refine ((continuousWithinAt_inter hU).1 hgw).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [inter_mem_nhdsWithin Sᶜ hU] with t ht
    rw [← key t ⟨ht.2, ht.1⟩, (hQ t ⟨ht.2, ht.1⟩).2]
    rfl
  · rw [← key t0 ⟨mem_of_mem_nhds hU, ht0⟩, (hQ t0 ⟨mem_of_mem_nhds hU, ht0⟩).2]
end Formalism.L2.Pj
