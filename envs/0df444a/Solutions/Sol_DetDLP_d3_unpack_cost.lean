-- Prove2me | solution 1 for DetDLP.d3_unpack_cost
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:22:09.474745+00:00
-- url     : https://prove2.me/submissions/d7c39ca9-b9ef-4d6b-8afd-6cd0e1ee1f74

import Definitions.Def_DetDLP_F9A3_BUnpackTerm

import Theorems.Thm_Groundwork_Unary_of_length

set_option maxHeartbeats 2500000
namespace DetDLP.ResidualScalarOracle
open Polynomial Finset
noncomputable section

section Cost
open Groundwork Groundwork.PolyT
attribute [local fun_prop] PolyT.comp PolyT.length PolyT.fst PolyT.snd PolyT.prodMk PolyT.const PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_ite__226169acf219 PolyT.map PolyT.flatMap PolyT.mul PolyT.mod
  w5_M6Sort.decode_poly w5_M6Sort.encode_poly DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly

@[local fun_prop] private theorem range_length_poly {α γ : Type} [Enc α] [Enc γ] {l : α → List γ}
    (hl : PolyT l) : PolyT fun x => List.range (l x).length := PolyT.range (Unary.of_length hl)

@[local fun_prop] private theorem horner_poly {α : Type} [Enc α] {m v : α → ℕ} {c s : α → List ℕ}
    (hm : PolyT m) (hc : PolyT c) (hs : PolyT s) (hv : PolyT v) :
    PolyT fun x => hornerStep (m x) (c x) (s x) (v x) := by unfold hornerStep; fun_prop

private theorem list_cost (l : List ℕ) (m : ℕ) (h : ∀ t ∈ l, t ≤ m) :
    len l ≤ l.length * (len m + 2) + 2 := by
  induction l with
  | nil => simp [len_nil]
  | cons a l ih =>
    have ha := len_nat_mono (h a (by simp))
    have hl := ih (fun t ht => h t (by simp [ht]))
    simp only [len_cons,List.length_cons,Nat.succ_mul]; omega

private theorem reduce_poly_aux : PolyT fun p : ℕ × List ℕ × List ℕ => reduceRow p.1 p.2.1 p.2.2 := by
  unfold reduceRow
  have hm : PolyT fun p : ℕ × List ℕ × List ℕ => max 1 p.1 := by simp only [max_def]; fun_prop
  apply PolyT.foldl_add (l := fun p : ℕ × List ℕ × List ℕ => p.2.2.reverse) (a := fun p : ℕ × List ℕ × List ℕ => p.2.1.map fun _ => 0) (g := fun (p : ℕ × List ℕ × List ℕ) s v => hornerStep (max 1 p.1) p.2.1 s v)
  · fun_prop
  · fun_prop
  · fun_prop
  · refine ⟨fun n => n * (n + 6) + 2, (PB.id'.mul (PB.id'.add (PB.const 6))).add (PB.const 2), ?_⟩
    rintro ⟨m,c,r⟩ s v _
    have bound := list_cost (hornerStep (max 1 m) c s v) (max 1 m) (by
      intro t ht; obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
      exact (Nat.mod_lt _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left ..))).le)
    simp only [hornerStep,List.length_map,List.length_range] at bound
    have hc := length_le_len c
    have hm : len (max 1 m) ≤ len m + 4 := by
      rcases le_total 1 m with h | h
      · rw [max_eq_right h]; omega
      · rw [max_eq_left h]; simp [len_nat]
    change len (hornerStep _ _ _ _) ≤ _
    apply le_trans bound
    simp only [len_pair]; nlinarith

@[local fun_prop] private theorem reduce_poly {α : Type} [Enc α] {m : α → ℕ} {c r : α → List ℕ}
    (hm : PolyT m) (hc : PolyT c) (hr : PolyT r) : PolyT fun x => reduceRow (m x) (c x) (r x) :=
  reduce_poly_aux.comp (hm.prodMk (hc.prodMk hr))

@[local fun_prop] private theorem dec_poly {α : Type} [Enc α] {l : α → List Bool} (h : PolyT l) : PolyT fun x => w5_M6Sort.decode (l x) := w5_M6Sort.decode_poly.comp h

theorem bUnpackTermRaw_poly : PolyT bUnpackTermRaw := by unfold bUnpackTermRaw unpackRows; fun_prop
end Cost
end
end DetDLP.ResidualScalarOracle
theorem solution : Groundwork.PolyT DetDLP.ResidualScalarOracle.bUnpackTermRaw := DetDLP.ResidualScalarOracle.bUnpackTermRaw_poly
