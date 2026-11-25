-- Prove2me | solution 1 for GalvinMultigraph.Local.kernel_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:54:56.551946+00:00
-- url     : https://prove2.me/submissions/286e96c4-0af5-4a53-b241-36bb9f8a16aa

module
public import Definitions.Def_GalvinLib_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Kernel
public import Theorems.Thm_Galvin_exists_listColoring


set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Local
variable {V : Type*} [Fintype V]
namespace GalvinMultigraph.Local
theorem _root_.solution (A : V → V → Prop) [DecidableRel A]
    (hirr : ∀ v, ¬ A v v)
    (hker : ∀ S : Finset V, ∃ K, IsKernelOn A S K)
    (L : V → Finset ℕ)
    (hL : ∀ v, (Finset.univ.filter fun u => A v u).card + 1 ≤ (L v).card) :
    ∃ φ : V → ℕ, (∀ v, φ v ∈ L v) ∧ ∀ u v, A u v → φ u ≠ φ v := by
  have hK : Galvin.HasKernels (SimpleGraph.fromRel A) A := by
    intro S
    obtain ⟨K, hKS, hKind, hKabs⟩ := hker S
    refine ⟨K, hKS, fun x hx y hy hxy => ?_, hKabs⟩
    rcases ((SimpleGraph.fromRel_adj _ _ _).1 hxy).2 with h | h
    · exact hKind x hx y hy h
    · exact hKind y hy x hx h
  obtain ⟨c, hc⟩ := Galvin.exists_listColoring (SimpleGraph.fromRel A) A hK L
    fun x => Nat.lt_of_succ_le (hL x)
  refine ⟨c, hc, fun u v huv => c.valid ?_⟩
  exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨fun h => hirr u (h ▸ huv), Or.inl huv⟩
end GalvinMultigraph.Local
