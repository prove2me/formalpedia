-- Prove2me | solution 1 for CGWH.weakHausdorffification_universal
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:06:54.171813+00:00
-- url     : https://prove2.me/submissions/99eda709-505e-4031-907c-a0eeea145a1c

import Definitions.Def_CGWH_WeakHausdorff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_quotient_iff
import Theorems.Thm_CGWH_weaklyHausdorffSpace_iff_isClosed_diagonal

open Topology TopologicalSpace

set_option autoImplicit false

universe u

namespace Sol_CGWH_weakHausdorffification_universal

/-- Closed sets of the `k`-ification: a set is `k`-closed iff its preimage under every test map
is closed. -/
theorem isClosed_compactlyGenerated_iff {Y : Type u} [TopologicalSpace Y] (s : Set Y) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} Y] s ↔
      ∀ (K : CompHaus.{u}) (f : C(K, Y)), IsClosed (f ⁻¹' s) := by
  rw [TopologicalSpace.compactlyGenerated, isClosed_coinduced, isClosed_sigma_iff]
  exact ⟨fun h K f => h ⟨K, f⟩, fun h ⟨K, f⟩ => h K f⟩

/-- The graph of the smallest closed equivalence relation `R_X` is itself `k`-closed: it is the
intersection of the graphs of all `k`-closed equivalence relations. -/
theorem isClosed_whSetoid (X : Type u) [TopologicalSpace X] :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)]
      {p : X × X | CGWH.whSetoid X p.1 p.2} := by
  rw [isClosed_compactlyGenerated_iff]
  intro K c
  have hset : c ⁻¹' {p : X × X | CGWH.whSetoid X p.1 p.2} =
      ⋂ S ∈ {S : Setoid X |
          IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)] {p : X × X | S p.1 p.2}},
        c ⁻¹' {p : X × X | S p.1 p.2} := by
    ext k
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_iInter]
    exact Iff.rfl
  rw [hset]
  refine isClosed_biInter fun S hS => ?_
  exact (isClosed_compactlyGenerated_iff _).mp hS K c

/-- The kernel of a continuous map into a space whose diagonal is `k`-closed is a `k`-closed
equivalence relation. -/
theorem isClosed_ker {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (hΔ : IsClosed[TopologicalSpace.compactlyGenerated.{u} (Y × Y)] (Set.diagonal Y))
    (f : X → Y) (hf : Continuous f) :
    IsClosed[TopologicalSpace.compactlyGenerated.{u} (X × X)]
      {p : X × X | Setoid.ker f p.1 p.2} := by
  rw [isClosed_compactlyGenerated_iff] at hΔ ⊢
  intro K c
  exact hΔ K ⟨fun k => (f (c k).1, f (c k).2),
    (hf.comp (continuous_fst.comp c.continuous)).prodMk
      (hf.comp (continuous_snd.comp c.continuous))⟩

end Sol_CGWH_weakHausdorffification_universal

open CGWH Sol_CGWH_weakHausdorffification_universal in
theorem solution
    (X : Type u) [TopologicalSpace X] [CompactlyGeneratedSpace X] :
    CompactlyGeneratedSpace (WeakHausdorffification X) ∧
      WeaklyHausdorffSpace (WeakHausdorffification X) ∧
      ∀ (Y : Type u) [TopologicalSpace Y] [CompactlyGeneratedSpace Y] [WeaklyHausdorffSpace Y]
        (f : C(X, Y)),
        ∃! g : C(WeakHausdorffification X, Y), ∀ x : X, g (WeakHausdorffification.mk x) = f x := by
  refine ⟨?_, ?_, ?_⟩
  · -- `h(X)` is a quotient of a compactly generated space
    exact inferInstanceAs (CompactlyGeneratedSpace (Quotient (whSetoid X)))
  · -- `R_X` is closed, hence `X / R_X` is weakly Hausdorff
    exact (weaklyHausdorffSpace_quotient_iff (whSetoid X)).mpr (isClosed_whSetoid X)
  · intro Y _ _ _ f
    -- the kernel of `f` is a closed equivalence relation, hence contains `R_X`
    have hΔ : IsClosed[TopologicalSpace.compactlyGenerated.{u} (Y × Y)] (Set.diagonal Y) :=
      (weaklyHausdorffSpace_iff_isClosed_diagonal Y).mp inferInstance
    have hker : whSetoid X ≤ Setoid.ker f := sInf_le (isClosed_ker hΔ f f.continuous)
    have hcompat : ∀ a b : X, whSetoid X a b → f a = f b := fun a b hab => hker hab
    refine ⟨⟨Quotient.lift (⇑f) hcompat, f.continuous.quotient_lift hcompat⟩,
      fun x => rfl, ?_⟩
    intro g hg
    ext z
    induction z using Quotient.inductionOn with
    | h x => exact hg x
