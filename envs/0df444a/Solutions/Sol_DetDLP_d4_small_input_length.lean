-- Prove2me | solution 1 for DetDLP.d4_small_input_length
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:11:23.679632+00:00
-- url     : https://prove2.me/submissions/9b1744e9-f19b-488e-b636-dd9151fffa93

import Definitions.Def_DetDLP_D4Plan
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Definitions.Def_DetDLP_W5_M6DriverFrames
set_option autoImplicit false
open DetDLP DetDLP.D4Plan DetDLP.w5_SplitArithmetic OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
private theorem cw (n : ℕ) : (countWord n).length ≤ n+1 := by
  cases n with
  | zero => decide
  | succ n => simp only [countWord, Nat.succ_ne_zero,if_false]; rw [Nat.size_eq_bits_len (n+1)]; apply Nat.size_le.mpr; exact (Nat.lt_two_pow_self (n:=n+1)).trans_le (Nat.pow_le_pow_right (by decide) (by omega))

theorem solution (C c L : ℕ) (hc : 0 < c) : ∃ K : ℕ,
  ∀ x : Input C c, Nat.clog 2 x.S < L → (input x).length ≤ K * (size x + 1)^K := by
  let F := 4*(C+1)*(2^L+1)+5
  let K := (2000*(F+1)^2+c)
  refine ⟨K,?_⟩
  intro x hl
  let y := (size x + 1)^c
  have y1 : 1 ≤ y := Nat.one_le_pow _ _ (by omega)
  have dy : x.desc.length ≤ y := by
    have := Nat.pow_le_pow_right (show 1 ≤ size x+1 by omega) hc
    simp only [pow_one] at this; exact le_trans (by dsimp [size]; omega) this
  have nv : x.G.nV ≤ y := x.nV
  have hs := (Nat.clog_le_iff_le_pow (b:=2) (by decide)).mp hl.le
  obtain ⟨hu,he⟩ := m14a_separator_edge_budget x.spec
  have k1 := x.hk; have m1 := x.hm
  have mβ : x.m ≤ 4*x.m*x.k := by nlinarith only [Nat.mul_le_mul_left (4*x.m) k1]
  have kβ : x.k ≤ 4*x.m*x.k := by nlinarith only [Nat.mul_le_mul_right x.k (show 1 ≤ 4*x.m by omega)]
  have hh := x.lower.trans (Nat.mul_le_mul_left C hu)
  have ll := x.lm.trans (Nat.mul_le_mul_left C (mβ.trans hu))
  have pS := x.pS
  have facts : x.G.nE+1 ≤ F ∧ x.b+1 ≤ F ∧ x.m+1 ≤ F ∧ x.k+1 ≤ F ∧ x.S+1 ≤ F ∧ x.p+1 ≤ F ∧ x.l+1 ≤ F := by
    dsimp [F]; have := Nat.mul_le_mul_left (2*C) hs
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> nlinarith only [this,hs,he,hu,mβ,kβ,hh,ll,pS,Nat.zero_le C,Nat.zero_le (C*2^L),Nat.zero_le (2^L)]
  obtain ⟨ne,bb,mm,kk,ss,pp,ll'⟩ := facts
  let es := (List.finRange x.G.nE).flatMap fun e => [(x.G.endpoints e).1.val,(x.G.endpoints e).2.val]
  have esL : es.length = 2*x.G.nE := by simp [es,List.length_flatMap]; omega
  have esB : (encodeNatListBin es).length ≤ (2*y+2)*(2*x.G.nE)+1 := by
    apply (length_encodeList_le countWord es y ?_).trans_eq (by rw [esL])
    intro a ha; simp only [es,List.mem_flatMap,List.mem_cons,List.not_mem_nil,or_false] at ha
    obtain ⟨e,_,rfl|rfl⟩ := ha <;> exact (cw _).trans (by have h := (x.G.endpoints e).1.isLt; have h' := (x.G.endpoints e).2.isLt; omega)
  let cap := (2*y+2)*(2*F)+F+y+2
  have gr : x.G.encode.length ≤ (2*cap+2)*4+1 := by
    apply length_encodeList_le id _ cap
    intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · have := cw x.G.nV; dsimp [cap]; omega
    · have := cw x.G.nE; dsimp [cap]; omega
    · simp [cap]; omega
    · change (encodeNatListBin es).length ≤ cap; dsimp [cap]; nlinarith only [esB,Nat.mul_le_mul_left (2*y+2) (show 2*x.G.nE ≤ 2*F by omega)]
  let cap' := (2*cap+2)*4+1+F+y
  have term : (input x).length ≤ (2*cap'+2)*9+1 := by
    apply length_encodeList_le id _ cap'
    intro w hw; simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [id_eq,List.length_ofFn] <;> dsimp [cap'] <;> first | omega | exact (cw _).trans (by omega)
  have leK : c ≤ K := by dsimp [K]; omega
  apply term.trans; apply le_trans (b:=K*y) _ (Nat.mul_le_mul_left K (Nat.pow_le_pow_right (by omega) leK))
  dsimp [cap',cap,K]; nlinarith only [y1,Nat.mul_le_mul_left F y1,Nat.mul_le_mul_left (F^2) y1,Nat.zero_le (c*y),Nat.zero_le F,Nat.zero_le (F*y),Nat.zero_le (F^2*y)]
