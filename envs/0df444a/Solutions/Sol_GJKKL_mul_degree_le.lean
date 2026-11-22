-- Prove2me | solution 1 for GJKKL.mul_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:00.729664+00:00
-- url     : https://prove2.me/submissions/82d814c2-ec2c-44a2-bce1-28c82a11c5b7

module
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_VertexCount
public import Theorems.Thm_GJKKL_sum_codegree_eq

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) {k c : ℕ} (hk : IsUniform H k)
    (hc : ∀ u w, u ≠ w → codegree H u w ≤ c) (v : V) :
    (k - 1) * degree H v ≤ (Fintype.card V - 1) * c := by
  have h1 : ∑ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card = degree H v * (k - 1) := by
    have hconst : ∀ e ∈ H.filter (fun e => v ∈ e), (e.erase v).card = k - 1 := by
      intro e he
      rw [mem_filter] at he
      rw [card_erase_of_mem he.2, hk e he.1]
    rw [sum_congr rfl hconst, sum_const, smul_eq_mul, degree]
  have h2 : ∑ u ∈ univ.erase v, codegree H v u ≤ ∑ _u ∈ univ.erase v, c :=
    sum_le_sum fun u hu => hc v u (mem_erase.mp hu).1.symm
  rw [sum_const, card_erase_of_mem (mem_univ v), card_univ, smul_eq_mul] at h2
  rw [sum_codegree_eq, h1] at h2
  rw [mul_comm]
  exact h2
end GJKKL
