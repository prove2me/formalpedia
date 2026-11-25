-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.coeff_spec
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T21:33:25.451574+00:00
-- url     : https://prove2.me/submissions/d748ed76-be88-4894-aae7-25b509d203db

import Definitions.Def_DetDLP_M3A_FpPolyDefs
set_option autoImplicit false
namespace DetDLP.M3A.FpPolyDefs
private theorem folds (z j : ℕ) : ((List.range j).foldl (fun a i => a*(z-i)) 1)=z.descFactorial j ∧
    ((List.range j).foldl (fun a i => a*(z+i)) 1)=z.ascFactorial j ∧ ((List.range j).foldl (fun a i => a*(i+1)) 1)=j.factorial := by
  induction j with
  | zero => simp
  | succ j ih => simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,ih.1,ih.2.1,ih.2.2,Nat.descFactorial_succ,Nat.ascFactorial_succ,Nat.factorial_succ];simp [Nat.mul_comm]
private theorem signed (b : Bool) (z j : ℕ) : intBinom (if b then (z:ℤ) else -(z:ℤ)) j =
    (if !b && j%2=1 then -(magnitude b z j:ℤ) else (magnitude b z j:ℤ)) := by
  cases b
  · rw [intBinom];simp only [Bool.false_eq_true,if_false,Bool.not_false,Bool.true_and,decide_eq_true_eq,magnitude,(folds z j).2.1,(folds z j).2.2,Nat.ascFactorial_eq_factorial_mul_choose',Nat.mul_div_cancel_left _ (Nat.factorial_pos _)]
    cases j with
    | zero => simp
    | succ j =>
      rw [Ring.choose_neg]; simp only [Nat.cast_succ];rw [show (z:ℤ)+(j+1)-1=(z+j:ℕ) by push_cast;ring,Ring.choose_natCast];by_cases h : (j+1)%2=1
      · rw [Int.negOnePow_odd _ (show Odd ((j:ℤ)+1) from ⟨(j+1)/2,by omega⟩)];simp [h,Nat.add_assoc,Units.neg_smul]
      · rw [Int.negOnePow_even _ (show Even ((j:ℤ)+1) from ⟨(j+1)/2,by omega⟩)];simp [h,Nat.add_assoc]
  · simp [intBinom,magnitude,(folds z j).1,(folds z j).2.2,Ring.choose_natCast,Nat.choose_eq_descFactorial_div_factorial]

theorem coeff_spec (b : Bool) (z j P : ℕ) : coeff b z (2^P) j = ((intBinom (if b then (z:ℤ) else -(z:ℤ)) j : ℤ) : ZMod (2^P)).val := by
  rw [signed];unfold coeff; split <;> simp [ZMod.neg_val',ZMod.val_natCast]
end DetDLP.M3A.FpPolyDefs

abbrev solution := @DetDLP.M3A.FpPolyDefs.coeff_spec
