-- Prove2me | solution 1 for ConstRegretMatch.Acyclic.lemma_C_1_U0
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:10:54.173756+00:00
-- url     : https://prove2.me/submissions/afad49d3-1108-4ad5-9c19-32a1d566abab

import Mathlib
import Definitions.Def_ConstRegretMatch_Acyclic_Network
import Definitions.Def_ConstRegretMatch_Acyclic_SPP
import Definitions.Def_ConstRegretMatch_Acyclic_Residual
import Theorems.Thm_ConstRegretMatch_Acyclic_lemma_C_1_leaves

open ConstRegretMatch.Acyclic

theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : ConstRegretMatch.Upper.IsMatchValues r) (lam : Fin n → ℝ) (hlam : ConstRegretMatch.Upper.IsArrivalRates lam)
    (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s)
    (hM0 : ConstRegretMatch.Upper.Mzero z = ∅) (hconn : (residualGraph N z).Connected)
    (hacyc : (residualGraph N z).IsAcyclic) :
    (ConstRegretMatch.Upper.Qplus s).card + d = n ∧ 1 ≤ (U0 N s).card := by
  classical
  have hMp : ConstRegretMatch.Upper.Mplus z = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro m
    by_contra hm
    have : m ∈ ConstRegretMatch.Upper.Mzero z := by
      simp only [ConstRegretMatch.Upper.Mzero, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [ConstRegretMatch.Upper.Mplus] using hm
    rw [hM0] at this
    simp at this
  have hcard : (ConstRegretMatch.Upper.Qplus s).card + d = n := by
    have := hGP.2
    rw [hMp, Finset.card_univ, Fintype.card_fin] at this
    omega
  refine ⟨hcard, ?_⟩
  have hres : residualGraph N z = networkGraph N := by
    unfold residualGraph networkGraph; rw [hMp]
  have hL := lemma_C_1_leaves N (hres ▸ hconn) (hres ▸ hacyc)
  -- leaves are agent types participating in exactly one match
  have hleaf : ∀ v ∈ leaves (networkGraph N), ∃ i, v = Sum.inl i ∧ matchCount N i = 1 := by
    intro v hv
    simp only [leaves, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj] at hv
    obtain ⟨w, hw, huniq⟩ := hv
    rcases v with i | m
    · refine ⟨i, rfl, ?_⟩
      rcases w with i' | m0
      · simp [networkGraph, incidenceGraph] at hw
      · have hm0 : i ∈ N.A m0 := by simpa [networkGraph, incidenceGraph] using hw
        unfold matchCount
        rw [Finset.card_eq_one]
        refine ⟨m0, ?_⟩
        ext m
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · intro hm
          have := huniq (Sum.inr m) (by simpa [networkGraph, incidenceGraph] using hm)
          exact Sum.inr_injective this
        · rintro rfl; exact hm0
    · exfalso
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (N.two_le_card m)
      have h1 := huniq (Sum.inl a) (by simpa [networkGraph, incidenceGraph] using ha)
      have h2 := huniq (Sum.inl b) (by simpa [networkGraph, incidenceGraph] using hb)
      exact hab (Sum.inl_injective (h1.trans h2.symm))
  let Lt : Finset (Fin n) := Finset.univ.filter (fun i => matchCount N i = 1)
  have hLle : (leaves (networkGraph N)).card ≤ Lt.card := by
    refine le_trans (Finset.card_le_card (t := Lt.map (Function.Embedding.inl (β := Fin d))) ?_)
      (Finset.card_map _).le
    intro v hv
    obtain ⟨i, rfl, hi⟩ := hleaf v hv
    exact Finset.mem_map_of_mem _ (by simp [Lt, hi])
  by_contra hU
  push Not at hU
  have hsub : Lt ⊆ ConstRegretMatch.Upper.Qplus s := by
    intro i hi
    by_contra hq
    have : i ∈ U0 N s := by
      simp only [U0, ConstRegretMatch.Upper.Qzero, Finset.mem_filter, Finset.mem_univ, true_and]
      simp only [ConstRegretMatch.Upper.Qplus, Finset.mem_filter, Finset.mem_univ, true_and] at hq
      simp only [Lt, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact ⟨hq, hi⟩
    have := Finset.card_pos.2 ⟨i, this⟩
    omega
  have := Finset.card_le_card hsub
  omega
