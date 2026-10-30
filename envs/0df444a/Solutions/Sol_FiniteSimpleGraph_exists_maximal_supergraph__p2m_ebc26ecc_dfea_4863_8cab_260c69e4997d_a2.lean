-- Prove2me | solution 1 for FiniteSimpleGraph.exists_maximal_supergraph__p2m_ebc26ecc_dfea_4863_8cab_260c69e4997d_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:13.772329+00:00
-- url     : https://prove2.me/submissions/341df362-6a99-42b3-8e1b-c2480ce55e3f

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Card

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hG : P G) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ P K ∧
      (∀ H : SimpleGraph V,
        G ≤ H → P H → K ≤ H → H ≤ K) := by
  classical
  let S : Finset (SimpleGraph V) :=
    Finset.univ.filter fun H => G ≤ H ∧ P H
  have hGmem : G ∈ S := by
    simp [S, hG]
  obtain ⟨K, hKmem, hKmax⟩ :=
    Finset.exists_max_image S (fun H : SimpleGraph V => H.edgeSet.ncard)
      ⟨G, hGmem⟩
  have hK : G ≤ K := (Finset.mem_filter.mp hKmem).2.1
  have hPK : P K := (Finset.mem_filter.mp hKmem).2.2
  refine ⟨K, hK, hPK, ?_⟩
  intro H hGH hPH hKH
  have hHmem : H ∈ S := by
    simp [S, hGH, hPH]
  by_contra hHK
  have hne : K ≠ H := by
    intro heq
    apply hHK
    simpa [heq] using hKH
  have hlt : K < H := lt_of_le_of_ne hKH hne
  have hstrict : K.edgeSet ⊂ H.edgeSet :=
    (SimpleGraph.edgeSet_ssubset_edgeSet).2 hlt
  have hcard : K.edgeSet.ncard < H.edgeSet.ncard :=
    Set.ncard_lt_ncard hstrict
  have hmax := hKmax H hHmem
  exact (not_lt_of_ge hmax) hcard