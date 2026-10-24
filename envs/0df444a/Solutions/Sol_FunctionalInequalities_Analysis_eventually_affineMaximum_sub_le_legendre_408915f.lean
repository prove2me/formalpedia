-- Prove2me | solution 1 for FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:14:37.240659+00:00
-- url     : https://prove2.me/submissions/b7a72fea-7633-4b87-99b1-39a2d860c9fa

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Filter Set
open scoped Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- CEK (60), for an arbitrary genuine finite set: pointwise convergence at
its vertices yields one eventual bound uniform over every dual point. -/
theorem solution
    (φ : ℕ → E → EReal) (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ s, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y : E,
      ((FunctionalInequalities.Analysis.affineMaximum s hs (fun x => (ψ x).toReal) y - ε : ℝ) : EReal) ≤
        FunctionalInequalities.Analysis.legendre (φ j) y := by
  have hupper : ∀ᶠ j in atTop, ∀ x ∈ s,
      φ j x ≤ ((ψ x).toReal + ε : ℝ) := by
    apply (eventually_all_finset s).mpr
    intro x hx
    have hc := EReal.coe_toReal (hfin x hx).1 (hfin x hx).2
    have hlt : ψ x < (((ψ x).toReal + ε : ℝ) : EReal) := by
      rw [← hc]
      exact EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hε)
    exact ((hlim x hx).eventually (Iio_mem_nhds hlt)).mono fun _ h => h.le
  filter_upwards [hupper] with j hj
  intro y
  obtain ⟨x, hx, hmax⟩ := s.exists_mem_eq_sup' hs (fun x => inner ℝ x y - (ψ x).toReal)
  change ((s.sup' hs (fun x => inner ℝ x y - (ψ x).toReal) - ε : ℝ) : EReal) ≤ _
  rw [hmax]
  have hterm : ((inner ℝ x y - (ψ x).toReal - ε : ℝ) : EReal) ≤
      (inner ℝ x y : EReal) - φ j x := by
    have h := EReal.sub_le_sub (le_refl (inner ℝ x y : EReal)) (hj x hx)
    convert h using 1
    rw [← EReal.coe_sub]
    congr 1
    ring
  exact hterm.trans (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ j z) x)
