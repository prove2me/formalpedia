-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.cro_constCoeff_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:43.459825+00:00
-- url     : https://prove2.me/submissions/2d35e702-9e09-44c7-b705-97147fe41f9d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Theorems.Thm_Formalism_L2_Pj_IsEval_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution {m : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p i, constantCoeff (a p i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by
  have ha' : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst ha', finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff
        (e.prod fun s j => (fun p : Fin m × Fin d => a p.1 p.2) s ^ j) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs) (by simp [ha s.1 s.2, zero_pow hs])
    rw [h0, smul_zero]
end Formalism.L2.Pj.Crude
