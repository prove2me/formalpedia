-- Prove2me | solution 1 for DetDLP.w3_fp_separator_btn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T23:50:38.830782+00:00
-- url     : https://prove2.me/submissions/80144c45-fe9c-497e-886f-ee711fe4bc18
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_w3_compile_wire_separator
import Theorems.Thm_DetDLP_w3_fp_native_wire_programs
import Theorems.Thm_DetDLP_w3_m5_modmul_r2
import Theorems.Thm_DetDLP_stage1_cond_exp_derand_and_size_bounds

set_option autoImplicit false
open DetDLP

theorem solution : w3_Separator w3_fpQueries := by
  refine w3_compile_wire_separator _ ?_ (w3_fp_native_wire_programs w3_m5_modmul_r2)
  intro q hq
  obtain ⟨p,hp,hp67,_,h64,_,seed,F,hF,P,y,pre,rfl⟩ := hq
  refine ⟨le_max_left 2 _,by dsimp only; omega,?_⟩
  intro i
  let m := blockCount (bitLen p)
  let T := hashThreshold p (p-1) m (p-1)
  change ((F i).map Additive.ofMul).length ≤ 2^Nat.clog 2 (2*T)
  rw [List.length_map,←List.toFinset_card_of_nodup (hF i).1,(hF i).2]
  have h := (stage1_cond_exp_derand_and_size_bounds.2.2.1.1 p m T seed i).2
  exact h.trans ((show T ≤ 2*T by omega).trans (Nat.le_pow_clog (by decide) _))
