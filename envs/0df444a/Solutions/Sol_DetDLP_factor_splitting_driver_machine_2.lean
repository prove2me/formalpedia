-- Prove2me | solution 2 for DetDLP.factor_splitting_driver_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:46:28.141325+00:00
-- url     : https://prove2.me/submissions/844f591b-2ed1-4561-b871-39932009762f

import Definitions.Def_DetDLP_M6_DFSOracleTrace
import Theorems.Thm_Groundwork_PB_comp
open DetDLP DetDLP.M6Loop DetDLP.w5_SplitArithmetic
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open Groundwork
set_option autoImplicit false

private theorem bounded (j d : ℕ) : ∃ h : ℕ, ∀ n : ℕ,
    (2*n+1)*(pol j (limit d n)+j*(pol d n+1)+j) ≤ pol h n := by
  have p (k) : PB (pol k) := ⟨k,fun _ => le_rfl⟩
  have sq := (PB.id'.add (PB.const 1)).mul (PB.id'.add (PB.const 1))
  have l : PB (limit d) := by change PB (fun n => 100*(n+1)^2 + pol d n + 10); simpa only [pow_two] using ((((PB.const 100).mul sq).add (p d)).add (PB.const 10))
  exact (((PB.const 2).mul PB.id').add (PB.const 1)).mul ((((p j).comp l).add ((PB.const j).mul ((p d).add (PB.const 1)))).add (PB.const j))

private theorem poly_up {h K : ℕ} (hK : h ≤ K) (n : ℕ) : polyBound h n ≤ polyBound K n := by
  unfold polyBound; gcongr; linarith [Nat.cast_nonneg (α:=ℝ) n]

theorem solution
    (f : ℕ → ℕ) (Md : PrimitiveMachine) (od : Fin Md.tapeCount) (Kd : ℕ)
    (hd : ∀ N : ℕ, 2 ≤ N →
      let n := bitLen (N+1)
      RunsWithin Md od (countWord N) (countWord (f N))
        ((2 : ℝ)^((Kd : ℝ)*n/Real.sqrt (logSafe n))) (polyBound Kd n)) :
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N+1)
        let split : ℕ → ℕ → List ℕ :=
          Nat.rec (motive := fun _ => ℕ → List ℕ) (fun x => [x]) (fun _ prev x =>
            let d := f x
            if 2 ≤ d ∧ d < x ∧ d ∣ x then prev d ++ prev (x/d) else [x])
        RunsWithin M out (countWord N) (encodeNatListBin ((split n N).mergeSort))
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ)))) (polyBound K n) := by
  obtain ⟨M,o,j,_,run⟩ := m89_polyT_oracle_loop step step_poly Md od
  obtain ⟨h,hb⟩ := bounded j Kd
  refine ⟨M,o,24*h+Kd,?_⟩
  intro N hN
  let n := bitLen (N+1)
  let e := rate Kd n
  let s := polyBound Kd n
  let a := polyBound j (limit Kd n) + (j:ℝ)*(s+1)
  have he : 1 ≤ e := by unfold e rate; apply Real.one_le_rpow (by norm_num); positivity
  have hs : 0 ≤ s := by unfold s polyBound; positivity
  have ha : 0 ≤ a := by unfold a polyBound; positivity
  have exec := run e s (by linarith) hs ((calls f n N).length+1) (limit Kd n) (countWord N) (encodeNatListBin ((split f n N).mergeSort (fun a b => decide (a ≤ b)))) (by omega) (by simpa only [Loop,pair,e,s,n] using root f Md od Kd N hN hd)
  have HH : (2*(n:ℝ)+1)*(a+j) ≤ polyBound h n := by
    have hr := Nat.cast_le (α:=ℝ).mpr (hb n)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,cast_pol,a,s] using hr
  apply MachineComposition.runsWithin_mono exec
  · have hnum : (((calls f n N).length+1 : ℕ):ℝ) ≤ 2*n+1 := by exact_mod_cast Nat.add_le_add_right (length_calls_lt_two_bitLen f n N hN).le 1
    have hadd : polyBound j (limit Kd n) + (j:ℝ)*(e+s+1) = a + (j:ℝ)*e := by dsimp [a]; ring
    rw [hadd]
    calc
      _ ≤ (2*(n:ℝ)+1)*((a+(j:ℝ))*e) := by gcongr; nlinarith [mul_nonneg ha (sub_nonneg.mpr he)]
      _ = ((2*(n:ℝ)+1)*(a+j))*e := by ring
      _ ≤ polyBound h n * e := mul_le_mul_of_nonneg_right HH (by linarith)
      _ ≤ _ := w5_polyBound_mul_sqrtLogExp_le h Kd n (w5_M6CallBudget.two_le_bitLen_of_two_le hN)
  · have hr := Nat.cast_le (α:=ℝ).mpr (hb n)
    have HH : (2*(n:ℝ)+1)*(a+j) ≤ polyBound h n := by simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,cast_pol,a,s] using hr
    apply le_trans (b:=polyBound h n) _ (poly_up (by omega) n)
    change a ≤ _; nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) n) (show 0 ≤ a+j by positivity)]

#print axioms solution
