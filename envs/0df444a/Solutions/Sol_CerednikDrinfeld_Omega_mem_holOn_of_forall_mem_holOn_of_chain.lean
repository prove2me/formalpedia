-- Prove2me | solution 1 for CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/d3ee3978-6e3c-59e0-8bdd-d5b8f04cb1e7

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain

set_option autoImplicit false

p2m_open "CerednikDrinfeld.Omega P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain.CerednikDrinfeld.Omega Filter"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"
namespace Omega
p2m_export "CerednikDrinfeld.Omega" "holOn mem_holOn_iff mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt"
namespace ChainAux
p2m_open "CerednikDrinfeld.Omega CerednikDrinfeld"

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem holOn_restrict {A B : Set K} (hAB : A ⊆ B) {f : ↥B → K} (hf : f ∈ holOn K B) :
    (fun z : ↥A => f ⟨(z : K), hAB z.2⟩) ∈ holOn K A := by
  rw [mem_holOn_iff] at hf ⊢
  obtain ⟨r, hpf, ⟨b, hb⟩, hlim⟩ := hf
  refine ⟨r, fun k z hz => hpf k z (hAB hz), ⟨b, fun k z => hb k ⟨(z : K), hAB z.2⟩⟩, ?_⟩
  exact hlim.comp (fun z : ↥A => (⟨(z : K), hAB z.2⟩ : ↥B))

end CerednikDrinfeld.Omega.ChainAux

open CerednikDrinfeld.Omega.ChainAux in

theorem solution
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (k : ℕ) (P : Fin (k + 1) → Set K)
    (hsub : ∀ j, P j ⊆ S) (hcov : S ⊆ ⋃ j, P j)
    (t π : Fin (k + 1) → K) (Z : Fin (k + 1) → Finset K)
    (hπ : ∀ j, j ≠ 0 → π j ≠ 0)
    (hout : ∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j))
    (hin : ∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j))
    (hrim : ∀ j, j ≠ 0 → ∀ z : K, Valued.v (z - t j) = Valued.v (π j) →
      (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i)
    (h : ↥S → K)
    (hh : ∀ j, (fun z : ↥(P j) => h ⟨(z : K), hsub j z.2⟩) ∈ holOn K (P j)) :
    h ∈ holOn K S := by
  classical

  let U : ℕ → Set K := fun m => {z | ∃ i : Fin (k + 1), i.val ≤ m ∧ z ∈ P i}
  have hUS : ∀ m, U m ⊆ S := fun m z hz => by
    obtain ⟨i, -, hz⟩ := hz
    exact hsub i hz
  have main : ∀ m, m ≤ k → (fun z : ↥(U m) => h ⟨(z : K), hUS m z.2⟩) ∈ holOn K (U m) := by
    intro m
    induction m with
    | zero =>
      intro _
      have hsub0 : U 0 ⊆ P 0 := fun z hz => by
        obtain ⟨i, hi, hz⟩ := hz
        have : i = 0 := Fin.ext (Nat.le_zero.mp hi)
        rwa [this] at hz
      exact holOn_restrict hsub0 (hh 0)
    | succ m ih =>
      intro hmk
      have ih' := ih (Nat.le_of_succ_le hmk)
      let j : Fin (k + 1) := ⟨m + 1, Nat.lt_succ_of_le hmk⟩
      have hj0 : j ≠ 0 := fun h0 => Nat.succ_ne_zero m (congrArg Fin.val h0)
      have hUP : U m ∪ P j ⊆ S := fun z hz => hz.elim (fun h' => hUS m h') (fun h' => hsub j h')
      have h₁ : ∀ z ∈ U m, Valued.v (π j) ≤ Valued.v (z - t j) := fun z hz => by
        obtain ⟨i, hi, hz⟩ := hz
        exact hout j hj0 i (Fin.lt_def.mpr (Nat.lt_succ_of_le hi)) z hz
      have h₂ : ∀ z ∈ P j, z ∈ U m ∨ Valued.v (z - t j) < Valued.v (π j) := fun z hz => by
        rcases hin j hj0 z hz with ⟨i, hij, hzi⟩ | hlt
        · exact Or.inl ⟨i, Nat.lt_succ_iff.mp (Fin.lt_def.mp hij), hzi⟩
        · exact Or.inr hlt
      have hC : ∀ z : K, Valued.v (z - t j) = Valued.v (π j) → (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) →
          z ∈ U m ∩ P j := fun z hz hZ => by
        obtain ⟨hzj, i, hij, hzi⟩ := hrim j hj0 z hz hZ
        exact ⟨⟨i, Nat.lt_succ_iff.mp (Fin.lt_def.mp hij), hzi⟩, hzj⟩
      have glue := CerednikDrinfeld.Omega.mem_holOn_union_of_mem_holOn_of_forall_le_of_forall_mem_or_lt K (U m) (P j) (t j) (π j) (hπ j hj0) (Z j) h₁ h₂ hC
        (fun z : ↥(U m ∪ P j) => h ⟨(z : K), hUP z.2⟩) ih' (hh j)
      have hsub1 : U (m + 1) ⊆ U m ∪ P j := fun z hz => by
        obtain ⟨i, hi, hz⟩ := hz
        rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hlt | heq
        · exact Or.inl ⟨i, Nat.lt_succ_iff.mp hlt, hz⟩
        · have : i = j := Fin.ext heq
          exact Or.inr (this ▸ hz)
      exact holOn_restrict hsub1 glue
  have hSU : S ⊆ U k := fun z hz => by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hz)
    exact ⟨i, Nat.lt_succ_iff.mp i.isLt, hi⟩
  exact holOn_restrict hSU (main k le_rfl)

end S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain (solution)
