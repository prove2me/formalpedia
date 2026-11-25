-- Prove2me | solution 1 for DetDLP.w3_ec_separator_btn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T21:41:39.965935+00:00
-- url     : https://prove2.me/submissions/e6c5fcb8-aafe-41af-a302-800779b866e9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_w3_compile_wire_separator
import Theorems.Thm_DetDLP_w3_ec_native_wire_programs
import Theorems.Thm_DetDLP_w3_m5_modmul_r2
import Theorems.Thm_DetDLP_stage1_cond_exp_derand_and_size_bounds

set_option autoImplicit false
open DetDLP

theorem solution : w3_Separator w3_ecQueries := by
  refine w3_compile_wire_separator _ ?_ (w3_ec_native_wire_programs w3_m5_modmul_r2)
  intro q hq
  obtain ⟨p,hp,E,hE,ha1,_,ha3,h67,h64,_,_,seed,F,hF,P,y,pre,rfl⟩ := hq
  letI := ecPointFintype E
  let M := Fintype.card E.toAffine.Point
  let m := blockCount (bitLen p)
  let T := hashThreshold p (M-1) m M
  refine ⟨le_max_left 2 _,by dsimp only; omega,?_⟩
  intro i
  change (F i).length ≤ 2^Nat.clog 2 (2*T)
  rw [←List.toFinset_card_of_nodup (hF i).1,(hF i).2]
  exact ((stage1_cond_exp_derand_and_size_bounds.2.2.1.2 p m T E seed i).2 (by omega) ha1 ha3).trans (Nat.le_pow_clog (by decide) _)
