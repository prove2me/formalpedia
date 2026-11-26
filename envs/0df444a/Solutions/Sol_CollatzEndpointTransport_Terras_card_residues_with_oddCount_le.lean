-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:17:04.800556+00:00
-- url     : https://prove2.me/submissions/91770874-e755-4caa-8b06-2a44172c1e32

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution (H K : ℕ) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card =
      lowerBinomialSum H K := by
  classical
  let s : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun n => oddCount H (n : ℕ) ≤ K)
  have hmap :
      ∀ n ∈ s, oddCount H (n : ℕ) ∈ Finset.range (K + 1) := by
    intro n hn
    have hnK : oddCount H (n : ℕ) ≤ K := by
      simpa [s] using hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hnK)
  calc
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) ≤ K)).card = s.card := by
        rfl
    _ = ∑ k ∈ Finset.range (K + 1),
        (s.filter (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ k ∈ Finset.range (K + 1), H.choose k := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkK : k ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hfilter :
          s.filter (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k) =
            Finset.univ.filter
              (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = k) := by
        ext n
        simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact And.right
        · intro hweight
          exact ⟨hweight.le.trans hkK, hweight⟩
      rw [hfilter, card_residues_with_oddCount]
    _ = lowerBinomialSum H K := rfl
end CollatzEndpointTransport.Terras
