-- Prove2me | solution 1 for DetDLP.D3Stopped.d3_stopped_schedule_raw_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:56:07.959438+00:00
-- url     : https://prove2.me/submissions/39f83d8b-0c54-4e89-ba2e-28ae9641e004

import Definitions.Def_DetDLP_D3StoppedRaw
import Definitions.Def_DetDLP_W5_M6Sort
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_PolyT_div_pow
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Theorems.Thm_Groundwork_PolyT_sum
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_P2M_Groundwork_PolyT_size__c8c8eb1b342f

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace DetDLP.D3Stopped
open AppendixD4 Groundwork Groundwork.PolyT DetDLP_W1_Queries Polynomial
open OAI.Algorithms.SubexponentialSAT
attribute [local fun_prop] PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.const PolyT.id'
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86
  P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_size__c8c8eb1b342f
  PolyT.div PolyT.mul PolyT.div_pow PolyT.map PolyT.countP PolyT.sum
  first_poly more_poly w5_M6Sort.encode_poly frame_poly

variable {α : Type} [Enc α]
private theorem clogSize (n : ℕ) : Nat.clog 2 n = Nat.size (n-1) := by
  apply le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by decide)).2
    have := Nat.lt_size_self (n-1); omega
  · apply Nat.size_le.mpr
    have := Nat.le_pow_clog (by decide : 1 < 2) n
    have : 0 < 2 ^ Nat.clog 2 n := by positivity
    omega
@[local fun_prop] private theorem pLevel {s : α → ℕ} (hs : PolyT s) : PolyT (fun x => level (s x)) := by
  simp only [level,clogSize]; fun_prop
private theorem uBound {g h : α → ℕ} (hg : PolyT g) (hh : PolyT h) (hb : ∀ x, g x ≤ level (h x)) : Unary g := by
  have hp : PolyT fun x => (((h x).bits.take (g x)).map fun _ => ()) := by fun_prop
  apply hp.congr; intro x
  apply List.ext_getElem
  · simp only [List.length_map,List.length_take,List.length_replicate]
    apply min_eq_left
    rw [Nat.size_eq_bits_len]
    exact (hb x).trans (by rw [level,clogSize]; exact Nat.size_le_size (Nat.sub_le ..))
  · intros; rfl
private theorem countLT (n k : ℕ) : (List.range n).countP (fun t => decide (t < k)) = min n k := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ,List.countP_append,ih]; by_cases h : n < k <;> simp [h] <;> omega
@[local fun_prop] private theorem pRoot {s : α → ℕ} (hs : PolyT s) : PolyT (fun x => (level (s x)).sqrt) := by
  have hr := PolyT.range (uBound (pLevel hs) hs fun _ => le_rfl)
  apply (PolyT.countP (f := fun x t => decide ((t+1)*(t+1) ≤ level (s x))) (by fun_prop) hr).congr
  intro x
  simp only [← Nat.le_sqrt, Nat.succ_le_iff, countLT, min_eq_right (Nat.sqrt_le_self _)]
@[local fun_prop] private theorem pDepth {s : α → ℕ} (C : ℕ) (hs : PolyT s) : PolyT (fun x => depth C (s x)) := by
  have h (n : ℕ) : Nat.clog 8 n = (level n+2)/3 := Nat.clog_pow_left 2 3 n
  simp only [depth,h]; fun_prop
@[local fun_prop] private theorem pThreshold {s : α → ℕ} (hs : PolyT s) : PolyT (fun x => threshold (s x)) :=
  PolyT.div (PolyT.sub (PolyT.add hs (pRoot hs)) (const 1)) (PolyT.max' (const 1) (pRoot hs))
@[local fun_prop] private theorem pWidth {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) : PolyT (fun x => width (s x) (j x)) := by unfold width; fun_prop
@[local fun_prop] private theorem pCap {s : α → ℕ} (hs : PolyT s) : PolyT (fun x => cap (s x)) := by
  apply pow_unary (const 2); apply uBound (h := s) (by fun_prop) hs; intro x; omega
private theorem rangeSum (n : ℕ) (f : ℕ → ℕ) : ((List.range n).map f).sum = ∑ t ∈ Finset.range n, f t := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,Finset.sum_range_succ,ih]
private theorem shiftTrunc (S j : ℕ) : shift S j = 2*(((List.range (level S)).map fun t => if t ≤ j then width S t else 0).sum) := by
  rw [rangeSum,shift]; congr 1
  calc
    _ = ∑ t ∈ Finset.range (max (j+1) (level S)), (if t ≤ j then width S t else 0) := by
      symm; rw [← Finset.sum_filter]; congr 1
      ext t; simp; omega
    _ = _ := by
      symm; apply Finset.sum_subset (Finset.range_mono (le_max_right ..))
      intro t _ ht
      have ht' : level S ≤ t := by simpa using ht
      have hw : width S t = 0 := Nat.div_eq_of_lt ((Nat.div_le_self ..).trans_lt (ht'.trans_lt (Nat.lt_pow_self (by decide : 1 < 2))))
      simp [hw]
@[local fun_prop] private theorem pShift {s j : α → ℕ} (hs : PolyT s) (hj : PolyT j) : PolyT (fun x => shift (s x) (j x)) := by
  have hr := PolyT.range (uBound (pLevel hs) hs fun _ => le_rfl)
  simp only [shiftTrunc]; fun_prop
private theorem mapRange (n : ℕ) (f : ℕ → ℕ) : List.ofFn (fun j : Fin n => f j.val) = (List.range n).map f := by
  apply List.ext_getElem <;> simp
private theorem pWords {s m d : α → ℕ} {f : α → Bits} (C : ℕ) (hs : PolyT s) (hm : PolyT m) (hd : PolyT d) (hf : PolyT f) : PolyT (fun x => scheduleWords C (s x) (m x) (d x) (f x)) := by
  let D := fun x => if m x ≤ threshold (s x) then 0 else depth C (s x) - d x
  have hD : PolyT D := by dsimp [D]; fun_prop
  have hR : PolyT (fun x => List.range (D x)) := by
    apply PolyT.range; apply uBound hD (h := fun x => C * max 1 (level (s x)).sqrt) (by fun_prop)
    intro x; dsimp [D]; split
    · omega
    · exact (Nat.sub_le ..).trans (Nat.clog_anti_left (by decide) (by decide : 2 ≤ 8))
  have hu : PolyT fun x => (List.range (D x)).map (fun t => width (s x) (d x+t)) := by fun_prop
  have ha : PolyT fun x => (List.range (D x)).map (fun t => shift (s x) (d x+t)) := by fun_prop
  change PolyT (fun x => Encoding.encodeList id [encodeNatListBin [min (m x) (threshold (s x)), d x, D x, cap (s x), 4*level (s x)], encodeNatListBin (List.ofFn fun t : Fin (D x) => width (s x) (d x+t.val)), encodeNatListBin (List.ofFn fun t : Fin (D x) => shift (s x) (d x+t.val)), f x])
  have h1 (x : α) := mapRange (D x) (fun t => width (s x) (d x+t))
  have h2 (x : α) := mapRange (D x) (fun t => shift (s x) (d x+t))
  simp only [h1,h2,Encoding.encodeList,id_eq,← frame_correct]; fun_prop

theorem _root_.solution (C : ℕ) : Groundwork.PolyT (scheduleRaw C) ∧ ∀ (d₀ S P l : ℕ) (payload : Bits) (G : Graph) (f : ℤ[X]),
    scheduleRaw C (encodeBTNInstance (descOf d₀ f payload) G S P l) = (schedule C S G.nE d₀).bits f := by
  refine ⟨?_, scheduleRaw_spec C⟩
  unfold scheduleRaw; apply pWords <;> fun_prop (disch := assumption) [third,second]
end DetDLP.D3Stopped
