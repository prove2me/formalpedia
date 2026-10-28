-- Prove2me | solution 1 for CountingMatroid.Analysis.ExchangeClosedBasis.exchange_closed_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:51:41.872234+00:00
-- url     : https://prove2.me/submissions/01da49d9-20ef-4023-ace1-af6447f2278e

import Definitions.Def_CountingMatroid_Model_Prelude
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Data.Rat.Defs

namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
set_option autoImplicit false

/-!
A closure certificate for a part of an independent set. When no element of
that part's ambient set can be inserted, and every permitted exchange stays
in the ambient set, fundamental circuits prove that the part is a basis.
-/

namespace CountingMatroid.Analysis.ExchangeClosedBasis
end CountingMatroid.Analysis.ExchangeClosedBasis
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.ExchangeClosedBasis

/-- INTERNAL: Fundamental circuits turn insertion failure and closure under
single-element exchanges into a basis certificate. This supplies the two
matroid certificates on opposite sides of an exchange-graph separator.
TEXLINE: main.tex:283-289 -/
theorem solution {α : Type*} (M : Matroid α) (I X : Set α)
    (hI : M.Indep I) (hX : X ⊆ M.E)
    (hinsert : ∀ e ∈ X, e ∉ I → ¬ M.Indep (insert e I))
    (hexchange : ∀ e ∈ X, e ∉ I → ∀ u ∈ I,
      M.Indep (insert e (I \ {u})) → u ∈ X) :
    M.IsBasis (I ∩ X) X := by
  apply (hI.subset Set.inter_subset_left).isBasis_of_subset_of_subset_closure
    Set.inter_subset_right
  intro e heX
  by_cases heI : e ∈ I
  · exact M.mem_closure_of_mem ⟨heI, heX⟩
  have hecl : e ∈ M.closure I := by
    by_contra h
    exact hinsert e heX heI
      ((hI.notMem_closure_iff_of_notMem heI (hX heX)).mp h)
  have hC := hI.fundCircuit_isCircuit hecl heI
  apply M.closure_mono _ (hC.mem_closure_sdiff_singleton_of_mem
    (M.mem_fundCircuit e I))
  intro u hu
  have hue : u ≠ e := by simpa only [Set.mem_singleton_iff] using hu.2
  have huI : u ∈ I := (M.fundCircuit_subset_insert e I hu.1).resolve_left hue
  refine ⟨huI, hexchange e heX heI u huI ?_⟩
  rw [Set.insert_sdiff_singleton_comm hue.symm]
  exact (hI.mem_fundCircuit_iff hecl heI).mp hu.1
