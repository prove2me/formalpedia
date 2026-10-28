-- Prove2me | solution 1 for FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:40.473389+00:00
-- url     : https://prove2.me/submissions/adcd6eed-c53b-4b59-86b5-cea69b0edcc4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum

noncomputable section
open Filter Set
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
