-- Prove2me | solution 1 for CliqueMinors.mader_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:43:15.862229+00:00
-- url     : https://prove2.me/submissions/1943237d-fb12-413a-bebe-cc624da03f04

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
public import Theorems.Thm_CliqueMinors_isMinor_of_clique
public import Theorems.Thm_CliqueMinors_isMinor_lift_contract
public import Theorems.Thm_CliqueMinors_isMinor_lift_cone
public import Theorems.Thm_CliqueMinors_card_edge_contract
public import Theorems.Thm_CliqueMinors_cone_edges
public import Theorems.Thm_CliqueMinors_contractG_adj
public import Theorems.Thm_CliqueMinors_contract_support
public import Theorems.Thm_CliqueMinors_exists_adj_of_card_pos


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open scoped Classical
variable [Fintype V]
namespace CliqueMinors
theorem _root_.solution (r : ℕ) : ∀ (G : SimpleGraph V) (S : Finset V), S.Nonempty →
    (∀ a b, G.Adj a b → a ∈ S) → 2 ^ r * S.card ≤ 8 * G.edgeFinset.card →
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by
  induction r using Nat.strong_induction_on with
  | _ r ihr =>
  match r with
  | 0 => exact fun G _ _ _ _ => isMinor_of_clique Fin.elim0 (fun i => i.elim0)
  | 1 =>
    intro G S hS _ _
    obtain ⟨v, _⟩ := hS
    exact isMinor_of_clique (fun _ => v) (fun i j h => absurd (Subsingleton.elim i j) h)
  | 2 =>
    intro G S hS _ hE
    have := hS.card_pos
    obtain ⟨a, b, hab⟩ := exists_adj_of_card_pos (G := G) (by omega)
    refine isMinor_of_clique ![a, b] fun i j h => ?_
    fin_cases i <;> fin_cases j <;> simp_all [hab.symm]
  | k + 3 =>
    suffices ∀ n (G : SimpleGraph V) (S : Finset V), S.card = n → S.Nonempty →
        (∀ a b, G.Adj a b → a ∈ S) → 2 ^ (k + 3) * S.card ≤ 8 * G.edgeFinset.card →
        IsMinor (⊤ : SimpleGraph (Fin (k + 3))) G from fun G S => this _ G S rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
    intro G S hn hS hsupp hE
    have hpow : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have hE' : 2 ^ k * S.card ≤ G.edgeFinset.card := by
      rw [hpow, mul_assoc] at hE; omega
    have hS1 := hS.card_pos
    have hk1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have hE0 : 0 < G.edgeFinset.card := by nlinarith
    obtain ⟨x, y, hxy⟩ := exists_adj_of_card_pos hE0
    have hmul : 2 ^ k * (S.card - 1) + 2 ^ k = 2 ^ k * S.card := by
      rw [Nat.mul_sub_one]; have : 2 ^ k ≤ 2 ^ k * S.card := Nat.le_mul_of_pos_right _ hS1
      omega
    by_cases hc : ∃ y', G.Adj x y' ∧ 2 ^ k * (S.card - 1) ≤ (contractG G x y').edgeFinset.card
    · obtain ⟨y', hxy', hc⟩ := hc
      refine isMinor_lift_contract (G' := contractG G x y') hxy'
        (fun u v h => (contractG_adj.1 h).2) (by omega) ?_
      have hy'S : y' ∈ S := hsupp _ _ hxy'.symm
      refine ihn (S.card - 1) (by omega) (contractG G x y') (S.erase y')
        (Finset.card_erase_of_mem hy'S)
        ⟨x, Finset.mem_erase.2 ⟨hxy'.ne, hsupp _ _ hxy'⟩⟩ (contract_support hxy' hsupp) ?_
      rw [Finset.card_erase_of_mem hy'S, hpow, mul_assoc]
      omega
    · simp only [not_exists, not_and, not_le] at hc
      have hcom : ∀ v, G.Adj x v → 2 ^ k ≤ (G.neighborFinset x ∩ G.neighborFinset v).card := by
        intro v hv
        have h1 := card_edge_contract hv
        have h2 := hc v hv
        omega
      have hcone := cone_edges hcom
      refine isMinor_lift_cone (G' := coneG G x) (fun u v h => h) (r := k + 2) (by omega) ?_
      refine ihr (k + 2) (by omega) (coneG G x) (G.neighborFinset x)
        ⟨y, by simpa using hxy⟩ (fun a b h => by simpa using h.2.1) ?_
      have : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
      rw [this, mul_assoc]
      omega
end CliqueMinors
