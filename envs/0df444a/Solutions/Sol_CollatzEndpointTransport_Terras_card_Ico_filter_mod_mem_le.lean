-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.card_Ico_filter_mod_mem_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:17.70389+00:00
-- url     : https://prove2.me/submissions/78ad0e76-f3d2-4e7b-8ead-216c883ef1d8

import Mathlib.Data.Nat.Periodic
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Definitions.Def_CollatzEndpointTransport_Common_TerrasShellRepetition
import Theorems.Thm_CollatzEndpointTransport_Terras_card_Ico_filter_mod_mem_of_dvd

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {base length q : ℕ} (hq : 0 < q) (S : Finset (Fin q)) :
    ((Finset.Ico base (base + length)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card ≤
      (length / q + 1) * S.card := by
  classical
  let blocks := length / q + 1
  let p : ℕ → Prop := fun n =>
    (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S
  have hp : Function.Periodic p q := by
    intro n
    simp [p, Nat.add_mod]
  have hlength : length ≤ blocks * q := by
    calc
      length = length % q + q * (length / q) :=
        (Nat.mod_add_div length q).symm
      _ ≤ q + q * (length / q) := by
        exact Nat.add_le_add_right (Nat.mod_lt length hq).le _
      _ = blocks * q := by
        simp [blocks]
        ring
  have hsubset :
      (Finset.Ico base (base + length)).filter p ⊆
        (Finset.Ico base (base + blocks * q)).filter p := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Ico] at hn ⊢
    exact ⟨⟨hn.1.1,
      hn.1.2.trans_le (Nat.add_le_add_left hlength base)⟩, hn.2⟩
  have hpblocks : Function.Periodic p (blocks * q) := by
    simpa [nsmul_eq_mul] using hp.nsmul blocks
  have hperiod :=
    Nat.filter_Ico_card_eq_of_periodic base (blocks * q) p hpblocks
  have hzero := card_Ico_filter_mod_mem_of_dvd
    (base := 0) (blocks := blocks) (q := q) hq (dvd_zero q) S
  have hcount : (blocks * q).count p = blocks * S.card := by
    rw [Nat.count_eq_card_filter_range, ← Nat.Ico_zero_eq_range]
    simpa [p] using hzero
  calc
    ((Finset.Ico base (base + length)).filter
      (fun n =>
        (⟨n % q, Nat.mod_lt _ hq⟩ : Fin q) ∈ S)).card =
        ((Finset.Ico base (base + length)).filter p).card := by rfl
    _ ≤ ((Finset.Ico base (base + blocks * q)).filter p).card :=
      Finset.card_le_card hsubset
    _ = (blocks * q).count p := hperiod
    _ = blocks * S.card := hcount
    _ = (length / q + 1) * S.card := by rfl
end CollatzEndpointTransport.Terras
