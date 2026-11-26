-- Prove2me | solution 1 for BandParity.sum_alt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:08:31.226787+00:00
-- url     : https://prove2.me/submissions/50e196db-dbc7-4d35-9d8f-aa68a4240394

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
public import Theorems.Thm_BandParity_sum_Ioc_alt
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 4 * m + 1 := ⟨p / 4, by omega⟩
  have hset : (range (4 * m + 1)).filter (fun v => 0 < v ∧ 2 * v < 4 * m + 1) =
      Finset.Ioc 0 (2 * m) := by
    ext v; simp only [mem_filter, mem_range, mem_Ioc]; omega
  rw [hset, sum_Ioc_alt]
end BandParity
