-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_residues_with_oddCount_ge_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:25:32.942918+00:00
-- url     : https://prove2.me/submissions/dc57ce91-2e19-483e-8564-c89f1daaf2ba

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_oddCount_le_length
import Theorems.Thm_CollatzEndpointTransport_Terras_card_residues_with_oddCount


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    (H K : ℕ) (hKH : K ≤ H) :
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card =
      lowerBinomialSum H K := by
  classical
  let s : Finset (Fin (2 ^ H)) :=
    Finset.univ.filter (fun n => H - K ≤ oddCount H (n : ℕ))
  have hmap :
      ∀ n ∈ s, H - oddCount H (n : ℕ) ∈ Finset.range (K + 1) := by
    intro n hn
    have hge : H - K ≤ oddCount H (n : ℕ) := by
      simpa [s] using hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by omega))
  calc
    (Finset.univ.filter
      (fun n : Fin (2 ^ H) => H - K ≤ oddCount H (n : ℕ))).card = s.card := by
        rfl
    _ = ∑ j ∈ Finset.range (K + 1),
        (s.filter
          (fun n : Fin (2 ^ H) => H - oddCount H (n : ℕ) = j)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ j ∈ Finset.range (K + 1), H.choose j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjK : j ≤ K := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hjH : j ≤ H := hjK.trans hKH
      have hfilter :
          s.filter
              (fun n : Fin (2 ^ H) => H - oddCount H (n : ℕ) = j) =
            Finset.univ.filter
              (fun n : Fin (2 ^ H) => oddCount H (n : ℕ) = H - j) := by
        ext n
        have hodd : oddCount H (n : ℕ) ≤ H :=
          oddCount_le_length H (n : ℕ)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨hge, hdefect⟩
          omega
        · intro hweight
          constructor
          · show n ∈ s
            simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
            calc
                H - K ≤ H - j := Nat.sub_le_sub_left hjK H
                _ = oddCount H (n : ℕ) := hweight.symm
          · rw [hweight, Nat.sub_sub_self hjH]
      rw [hfilter, card_residues_with_oddCount, Nat.choose_symm hjH]
    _ = lowerBinomialSum H K := rfl
end CollatzEndpointTransport.Terras
