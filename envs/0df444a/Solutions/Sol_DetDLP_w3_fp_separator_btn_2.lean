-- Prove2me | solution 2 for DetDLP.w3_fp_separator_btn
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T11:34:16.471069+00:00
-- url     : https://prove2.me/submissions/fb1f2a36-6eb0-4f11-a490-3c9e210455b0

import Theorems.Thm_DetDLP_w3_compile_wire_separator
import Theorems.Thm_DetDLP_fp_native_uniform_wiring

set_option autoImplicit false
open DetDLP

private theorem fpBlockCard {p m : ℕ} [Fact p.Prime] (T : ℕ) (S : FpSeed p m) (i : Fin m) :
    (fpFactorBlock T S i).card ≤ T := by
  let a := (S i).1.val + 1
  let b := (S i).2.val
  have ha : a < p := by have h := (S i).1.isLt; dsimp [a]; omega
  have nz : (a : ZMod p) ≠ 0 := by
    intro h
    have e := congrArg ZMod.val h
    rw [ZMod.val_natCast_of_lt ha,ZMod.val_zero] at e
    dsimp [a] at e
    omega
  let index (x : ↥(fpFactorBlock T S i)) : Fin T :=
    ⟨(a * (x.val : ZMod p).val + b) % p,
      of_decide_eq_true (Finset.mem_filter.mp x.property).2⟩
  have inj : Function.Injective index := by
    intro x y h
    have e := congrArg (fun n : ℕ => (n : ZMod p)) (congrArg Fin.val h)
    change (((a * (x.val : ZMod p).val + b) % p : ℕ) : ZMod p) =
      (((a * (y.val : ZMod p).val + b) % p : ℕ) : ZMod p) at e
    simp only [ZMod.natCast_mod,Nat.cast_add,Nat.cast_mul,ZMod.natCast_val,ZMod.cast_id] at e
    exact Subtype.ext (Units.ext (mul_left_cancel₀ nz (add_right_cancel e)))
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective index inj

theorem solution : w3_Separator w3_fpQueries := by
  refine w3_compile_wire_separator _ ?_ fp_native_uniform_wiring
  intro q hq
  obtain ⟨p,hp,hp67,_,h64,_,seed,F,hF,P,y,pre,rfl⟩ := hq
  refine ⟨le_max_left 2 _,by dsimp only; omega,?_⟩
  intro i
  let m := blockCount (bitLen p)
  let T := hashThreshold p (p-1) m (p-1)
  change ((F i).map Additive.ofMul).length ≤ 2^Nat.clog 2 (2*T)
  rw [List.length_map,←List.toFinset_card_of_nodup (hF i).1,(hF i).2]
  have h := fpBlockCard T seed i
  exact h.trans ((show T ≤ 2*T by omega).trans (Nat.le_pow_clog (by decide) _))
