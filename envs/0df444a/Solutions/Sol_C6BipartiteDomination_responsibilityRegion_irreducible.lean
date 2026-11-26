-- Prove2me | solution 1 for C6BipartiteDomination.responsibilityRegion_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T21:41:40.479521+00:00
-- url     : https://prove2.me/submissions/d190d275-73e6-4ff5-b9e8-20617568cf2c

import Definitions.Def_C6BipartiteDomination_Basic
import Definitions.Def_C6BipartiteDomination_A2
import Theorems.Thm_C6BipartiteDomination_mem_responsibilityRegion
import Theorems.Thm_C6BipartiteDomination_collective_exchange


set_option autoImplicit true
open C6BipartiteDomination
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D X Y : Finset V}
    (hD : MinimumBipartiteDominatingSet G D)
    (hX : IsolatedSubset G D X)
    (hY : BipartiteDominatingOn G (responsibilityRegion G D X) Y) :
    X.card ≤ Y.card := by
  classical
  let D' := (D \ X) ∪ Y
  have hcover : ∀ ⦃v⦄, Responsible G D X v → v ∈ Y ∨ ∃ y ∈ Y, G.Adj y v := by
    intro v hv
    have hvR : v ∈ responsibilityRegion G D X := (mem_responsibilityRegion G D X v).2 hv
    by_cases hvY : v ∈ Y
    · exact Or.inl hvY
    · obtain ⟨y, hy, hadj⟩ := hY.2.1 hvR hvY
      exact Or.inr ⟨y, hy, hadj⟩
  have hbip : IsBipartiteOn G D' := by
    rcases hD.1.2 with ⟨c, hc⟩
    rcases hY.2.2 with ⟨d, hd⟩
    refine ⟨fun v => if v ∈ D \ X then c v else d v, ?_⟩
    intro u v hu hv hadj
    rcases Finset.mem_union.mp hu with huRet | huY
    · rcases Finset.mem_union.mp hv with hvRet | hvY
      · have huD := (Finset.mem_sdiff.mp huRet).1
        have hvD := (Finset.mem_sdiff.mp hvRet).1
        simpa [huRet, hvRet] using hc huD hvD hadj
      · have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
        have hnotAdj := (mem_responsibilityRegion G D X v).mp hvR |>.2 u huRet
        exact (hnotAdj hadj).elim
    · rcases Finset.mem_union.mp hv with hvRet | hvY
      · have huR : u ∈ responsibilityRegion G D X := hY.1 huY
        have hnotAdj := (mem_responsibilityRegion G D X u).mp huR |>.2 v hvRet
        exact (hnotAdj hadj.symm).elim
      · have huR : u ∈ responsibilityRegion G D X := hY.1 huY
        have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
        have huNotRet := (mem_responsibilityRegion G D X u).mp huR |>.1
        have hvNotRet := (mem_responsibilityRegion G D X v).mp hvR |>.1
        simpa [huNotRet, hvNotRet] using hd huY hvY hadj
  have hD' : IsBipartiteDominatingSet G D' :=
    collective_exchange G hcover hbip
  have hmin := hD.2 D' hD'
  have hdisj : Disjoint (D \ X) Y := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvRet hvY
    have hvR : v ∈ responsibilityRegion G D X := hY.1 hvY
    exact (mem_responsibilityRegion G D X v).mp hvR |>.1 hvRet
  have hcardD' : D'.card = D.card - X.card + Y.card := by
    dsimp [D']
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset hX.1]
  rw [hcardD'] at hmin
  have hXcard : X.card ≤ D.card := Finset.card_le_card hX.1
  omega
end C6BipartiteDomination
