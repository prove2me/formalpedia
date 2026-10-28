-- Prove2me | solution 1 for BitDFT.header_inverse_fourier_bank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T15:49:43.530333+00:00
-- url     : https://prove2.me/submissions/f32d839c-d645-46aa-a567-a364d3f579b5

import Definitions.Def_BitDFT_BankedTripleAlphabetHost
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open IntMul BitDFT.DedicatedTapeBanks BitDFT.BankedTripleAlphabetHost
private theorem route_wrap_local (r offset : ℕ) (hoff : offset < 4 + r)
    (i : Fin (5 + r)) (hi : 1 ≤ i.val) :
    routing r offset hoff i =
      ⟨((offset + i.val - 1) % (4 + r)) + 1, by have hm := Nat.mod_lt (offset + i.val - 1) (by omega : 0 < 4 + r); omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hright : ¬ i.val < 1 := by omega
  change Sum.map id (rotateTail r offset hoff) (splitIndex r i) =
    splitIndex r ⟨((offset + i.val - 1) % (4 + r)) + 1, by have hm := Nat.mod_lt (offset + i.val - 1) (by omega : 0 < 4 + r); omega⟩
  have hout : ¬ (((offset + i.val - 1) % (4 + r)) + 1) < 1 := by omega
  simp only [splitIndex, hright, hout, dif_neg]
  apply congrArg Sum.inr
  apply Fin.ext
  simp [rotateTail, Fin.val_add]
  congr 1
  omega

theorem solution (A M H : IntMul.MultitapeTM)
    (p : Fin (width A M H)) (hp : 1 ≤ p.val) (hpa : p.val < A.k) :
    H.k ≤ ((route A M H (headerOffset A M H)
      (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
          dsimp [tail, headerOffset]; omega) ).symm p).val := by
  let W := width A M H
  let r := tail A M H
  let off := headerOffset A M H
  let hoff : off < 4 + r := by
    dsimp [off, headerOffset, r, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega
  let R := route A M H off hoff
  have hW : W = A.k + M.k + H.k + 1 := by dsimp [W]; exact width_eq_sum A M H
  let k : Fin W := ⟨H.k + p.val + 2, by
    rw [hW]
    change H.k + p.val + 2 < A.k + M.k + H.k + 1
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    have hpW : p.val < A.k + M.k + H.k + 1 := by
      rw [← width_eq_sum A M H]
      exact p.isLt
    omega⟩
  have hk : 1 ≤ k.val := by dsimp [k]; have hH := H.two_le_k; omega
  have hlenEq : 4 + r = A.k + M.k + H.k := by
    dsimp [r, tail]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    omega
  have hlen : p.val < 4 + r := by rw [hlenEq]; omega
  have hroute : R k = p := by
    change routing r off hoff k = p
    rw [route_wrap_local r off hoff k hk]
    apply Fin.ext
    dsimp [R, off, r, headerOffset, tail, k]
    have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k
    have heq : (A.k + M.k - 2) + (H.k + p.val + 1) =
        (4 + (A.k + M.k + H.k - 4)) + (p.val - 1) := by omega
    rw [heq]
    have hpm : p.val - 1 < 4 + r := by omega
    have hmod : ((4 + r) + (p.val - 1)) % (4 + r) = p.val - 1 := by
      rw [Nat.add_mod]
      simp [Nat.mod_eq_of_lt hpm]
    rw [hmod]
    omega
  have hinv : R.symm p = k := by
    rw [← hroute]
    exact R.symm_apply_apply k
  rw [hinv]
  dsimp [k]
  omega

end
