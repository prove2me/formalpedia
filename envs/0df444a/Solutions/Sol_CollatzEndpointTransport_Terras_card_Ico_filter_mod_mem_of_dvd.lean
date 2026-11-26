-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:16.818112+00:00
-- url     : https://prove2.me/submissions/862b18c4-95c4-4dde-8238-0bef33a2218e

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_fin_filter_mod_mem

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {base blocks q : ℕ} (hq : 0 < q) (hbase : q ∣ base)
    (S : Finset (Fin q)) :
    ((Finset.Ico base (base + blocks * q)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
      blocks * S.card := by
  classical
  have hbase_mod : base % q = 0 := Nat.mod_eq_zero_of_dvd hbase
  have hcard :
      ((Finset.Ico base (base + blocks * q)).filter
        (fun n =>
          (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        (Finset.univ.filter
          (fun x : Fin (blocks * q) =>
            (⟨(x : ℕ) % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card := by
    apply Finset.card_bij
      (fun n hn =>
        ⟨n - base, by
          have hnIco := (Finset.mem_filter.mp hn).1
          have hnle := (Finset.mem_Ico.mp hnIco).1
          have hnlt := (Finset.mem_Ico.mp hnIco).2
          omega⟩)
    · intro n hn
      have hnIco := (Finset.mem_filter.mp hn).1
      have hnS := (Finset.mem_filter.mp hn).2
      have hnle := (Finset.mem_Ico.mp hnIco).1
      have hn_eq : base + (n - base) = n := Nat.add_sub_of_le hnle
      have hmod : n % q = (n - base) % q := by
        calc
          n % q = (base + (n - base)) % q := by rw [hn_eq]
          _ = (n - base) % q := by simp [Nat.add_mod, hbase_mod]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hmod] using hnS
    · intro n hn m hm hnm
      have hnIco := (Finset.mem_filter.mp hn).1
      have hmIco := (Finset.mem_filter.mp hm).1
      have hnle := (Finset.mem_Ico.mp hnIco).1
      have hmle := (Finset.mem_Ico.mp hmIco).1
      have hval : n - base = m - base := congrArg Fin.val hnm
      omega
    · intro x hx
      refine ⟨base + (x : ℕ), ?_, ?_⟩
      · have hxS := (Finset.mem_filter.mp hx).2
        simp only [Finset.mem_filter, Finset.mem_Ico]
        constructor
        · constructor
          · omega
          · exact Nat.add_lt_add_left x.isLt base
        · simpa [Nat.add_mod, hbase_mod] using hxS
      · apply Fin.ext
        simp
  rw [hcard, card_fin_filter_mod_mem hq S]
end CollatzEndpointTransport.Terras
