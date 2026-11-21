-- Prove2me | solution 1 for CutSetEnum.proposition_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:24:51.028465+00:00
-- url     : https://prove2.me/submissions/e9a38307-5d88-4d54-b6b0-08290c1dbf3a

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal
set_option autoImplicit false

namespace Aux_CutSetEnum_proposition_2_1

open HyperKCut.Structure CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutSet_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    cutSet H Aᶜ = cutSet H A := by
  unfold cutSet
  apply Multiset.filter_congr
  intro e _
  rw [compl_compl]
  exact and_comm

theorem d_eq_card (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H A = (cutSet H A).card := rfl

theorem d_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H Aᶜ = d H A := by
  rw [d_eq_card, d_eq_card, cutSet_compl]

/-- the core of Proposition 2.1: any minimum `(S, Uᶜ)`-terminal cut of a transversal -/
theorem min_cut_of_transversal (H : HyperKCut.Structure.Hypergraph V) (U S : Finset V)
    (hSU : S ⊆ U) (hT : IsTransversal H U S) (A : Finset V)
    (hA : IsMinTerminalCut H S Uᶜ A) : cutSet H A = cutSet H U := by
  by_contra hne
  obtain ⟨⟨hSA, hAd⟩, hmin⟩ := hA
  have hdU : d H A ≤ d H U := hmin U ⟨hSU, disjoint_compl_right⟩
  have hAU : A ⊆ U := by
    intro x hx
    by_contra hxU
    exact Finset.disjoint_left.mp hAd hx (Finset.mem_compl.mpr hxU)
  have hmem : Aᶜ ∈ Coll H U := by
    show Uᶜ ⊂ Aᶜ ∧ d H Aᶜ ≤ d H U ∧ cutSet H Aᶜ ≠ cutSet H U
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.compl_subset_compl.mpr hAU, ?_⟩
      intro heq
      have : A = U := compl_injective heq.symm
      apply hne
      rw [this]
    · rw [d_compl]
      exact hdU
    · rw [cutSet_compl]
      exact hne
  obtain ⟨x, hx⟩ := hT _ hmem
  rw [Finset.mem_inter, Finset.mem_compl] at hx
  exact hx.2 (hSA hx.1)


end Aux_CutSetEnum_proposition_2_1


open HyperKCut.Structure CutSetEnum Aux_CutSetEnum_proposition_2_1 in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S) (hSne : S.Nonempty) :
    ∀ A : Finset V, IsMinTerminalCut H S Uᶜ A → cutSet H A = cutSet H U := by
  intro A hA
  exact min_cut_of_transversal H U S hS.1 hS.2.1 A hA
