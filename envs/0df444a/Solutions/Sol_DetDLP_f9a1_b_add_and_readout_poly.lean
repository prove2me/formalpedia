-- Prove2me | solution 1 for DetDLP.f9a1_b_add_and_readout_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T03:03:38.215263+00:00
-- url     : https://prove2.me/submissions/26c84f2b-b848-4f06-afb3-168f7d06fe82

import Definitions.Def_DetDLP_F9A1_BAddRead
import Definitions.Def_ToTuring_Lib_List2

open Polynomial DetDLP DetDLP.F9A1 DetDLP.ResidualScalarOracle
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open DetDLP_W1_Queries Groundwork Groundwork.PolyT
set_option maxHeartbeats 1200000

attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk
  PolyT.map PolyT.length PolyT.mul PolyT.div PolyT.mod
  P2M_Groundwork_PolyT_id__1c5d0f44cc8f first_poly more_poly w5_M6Sort.encode_poly

private theorem parsedWords_poly {α : Type} [Enc α] {f : α → List Bool} (h : PolyT f) :
    PolyT (fun x => w5_M6Sort.decode (f x)) := w5_M6Sort.decode_poly.comp h
attribute [local fun_prop] parsedWords_poly

private theorem rangeLen_poly {α : Type} [Enc α] {f : α → List Bool} (h : PolyT f) :
    PolyT (fun x => List.range (f x).length) := by
  apply PolyT.range
  have hm : PolyT (fun x => (f x).map fun _ => ()) := by fun_prop
  apply hm.congr
  intro x
  simp
attribute [local fun_prop] rangeLen_poly

private theorem readWord (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (acc : B f ell q)
    (j : Fin ell) (zero : Fin f.natDegree) (hz : zero.val = 0) :
    (bWords f ell q hf acc).getD (j.val * f.natDegree) 0 = word f ell q hf acc j zero := by
  let idx := finProdFinEquiv (j,zero)
  have he : idx.val = j.val * f.natDegree := by
    change zero.val + f.natDegree * j.val = _
    simp [hz, Nat.mul_comm]
  rw [← he, bWords, List.getD_eq_getElem _ _ (by simpa using idx.isLt), List.getElem_ofFn]
  change word f ell q hf acc (finProdFinEquiv.symm (finProdFinEquiv (j,zero))).1
    (finProdFinEquiv.symm (finProdFinEquiv (j,zero))).2 = _
  simp

theorem solution :
    (∀ (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (x y : B f ell q),
      bAddRaw (Encoding.encodeList id [(2^q : ℕ).bits, bEncode f ell q hf x,
        bEncode f ell q hf y]) = bEncode f ell q hf (x + y)) ∧
    (∀ (f : ℤ[X]) (ell q g : ℕ) (hf : f.Monic) (acc : B f ell q)
      (zero : Fin f.natDegree), zero.val = 0 →
      bReadZeroDivRaw (Encoding.encodeList id [(2^g : ℕ).bits, List.replicate f.natDegree true,
        List.replicate ell true, bEncode f ell q hf acc]) =
        encodeNatListBin (List.ofFn fun j : Fin ell => word f ell q hf acc j zero / 2^g)) ∧
    (Groundwork.PolyT bAddRaw ∧ Groundwork.PolyT bReadZeroDivRaw) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f ell q hf x y
    simp only [bAddRaw, bEncode, first_cons, more_cons, id_eq, w5_M6Sort.decode_encode, bval_bits]
    apply congrArg encodeNatListBin
    unfold bWords
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map, List.getElem_zip, List.getElem_ofFn, word,
        map_add, coeff_add, ZMod.val_add]
  · intro f ell q g hf acc zero hz
    simp only [bReadZeroDivRaw, bEncode, first_cons, more_cons, id_eq, w5_M6Sort.decode_encode,
      bval_bits, List.length_replicate, Nat.add_zero]
    apply congrArg encodeNatListBin
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      have hj : i < ell := by simpa using hi'
      simpa only [List.getElem_map, List.getElem_range, List.getElem_ofFn] using
        congrArg (fun n => n / 2^g) (readWord f ell q hf acc ⟨i,hj⟩ zero hz)
  · unfold bAddRaw
    apply w5_M6Sort.encode_poly
    apply PolyT.map (f := fun w (ab : ℕ × ℕ) => (ab.1 + ab.2) % bval (first w))
    · fun_prop
    · apply PolyT.zip <;> fun_prop
  · unfold bReadZeroDivRaw
    apply w5_M6Sort.encode_poly
    apply PolyT.map (f := fun w (j : ℕ) =>
      (w5_M6Sort.decode (first (more (more (more w))))).getD
        (j * (first (more w)).length + 0) 0 / bval (first w))
    · apply PolyT.div
      · apply PolyT.getD <;> fun_prop
      · fun_prop
    · apply rangeLen_poly
      fun_prop
