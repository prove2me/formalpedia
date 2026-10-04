-- Prove2me | solution 1 for CubicP3Partition.R03SP01ThreeComponentSupportEquiv
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-09-22T05:36:05.813982+00:00
-- url     : https://prove2.me/submissions/23eebef3-0040-4942-8760-943bb6451a6e

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_999a973085_r03_sp01_three_component_support_equiv_candidate

open CubicP3Partition
open SimpleGraph
universe u

theorem solution
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (cA cB cC : F.ConnectedComponent)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    (hcover : ∀ v : V,
      v ∈ cA.supp ∨ v ∈ cB.supp ∨ v ∈ cC.supp) :
    ∃ (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V),
      (∀ x : cA.supp, eV (Sum.inl x) = x.1) ∧
      (∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1) ∧
      (∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1) := by
  let forward : cA.supp ⊕ (cB.supp ⊕ cC.supp) → V
    | Sum.inl x => x.1
    | Sum.inr (Sum.inl x) => x.1
    | Sum.inr (Sum.inr x) => x.1
  have forward_injective : Function.Injective forward := by
    intro x y hxy
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            exact congrArg Sum.inl (Subtype.ext hxy)
        | inr y =>
            cases y with
            | inl y =>
                change x.1 = y.1 at hxy
                exact (hAB (ConnectedComponent.eq_of_common_vertex x.2
                  (hxy.symm ▸ y.2))).elim
            | inr y =>
                change x.1 = y.1 at hxy
                exact (hAC (ConnectedComponent.eq_of_common_vertex x.2
                  (hxy.symm ▸ y.2))).elim
    | inr x =>
        cases x with
        | inl x =>
            cases y with
            | inl y =>
                change x.1 = y.1 at hxy
                exact (hAB (ConnectedComponent.eq_of_common_vertex y.2
                  (hxy ▸ x.2))).elim
            | inr y =>
                cases y with
                | inl y =>
                    exact congrArg Sum.inr (congrArg Sum.inl (Subtype.ext hxy))
                | inr y =>
                    change x.1 = y.1 at hxy
                    exact (hBC (ConnectedComponent.eq_of_common_vertex x.2
                      (hxy.symm ▸ y.2))).elim
        | inr x =>
            cases y with
            | inl y =>
                change x.1 = y.1 at hxy
                exact (hAC (ConnectedComponent.eq_of_common_vertex y.2
                  (hxy ▸ x.2))).elim
            | inr y =>
                cases y with
                | inl y =>
                    change x.1 = y.1 at hxy
                    exact (hBC (ConnectedComponent.eq_of_common_vertex y.2
                      (hxy ▸ x.2))).elim
                | inr y =>
                    exact congrArg Sum.inr (congrArg Sum.inr (Subtype.ext hxy))
  have forward_surjective : Function.Surjective forward := by
    intro v
    rcases hcover v with hv | hv | hv
    · exact ⟨Sum.inl ⟨v, hv⟩, rfl⟩
    · exact ⟨Sum.inr (Sum.inl ⟨v, hv⟩), rfl⟩
    · exact ⟨Sum.inr (Sum.inr ⟨v, hv⟩), rfl⟩
  let eV := Equiv.ofBijective forward ⟨forward_injective, forward_surjective⟩
  refine ⟨eV, ?_⟩
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

#print axioms solution
