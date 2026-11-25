-- Prove2me | solution 1 for DetDLP.bordered_update_bit_program
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:22:52.840828+00:00
-- url     : https://prove2.me/submissions/a412d5fb-cbfb-41cb-9e90-90e12c4b9280

import Theorems.Thm_DetDLP_bordered_binary_input_preparation
import Theorems.Thm_DetDLP_bordered_binary_output_recovery
import Theorems.Thm_DetDLP_packed_hermite_normal_form_machine

namespace DetDLP
open OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls BorderedBitIO

private theorem io_embed {s : ℕ} (raw : List Bool) (r q : Fin 8 → Bool)
    (a b : Fin 55 → List Bool) :
    embedState id (Fin.castAdd (s+2)) ⟨r,withBackup s a raw⟩ ⟨q,b⟩ =
      ⟨q,withBackup s b raw⟩ := by
  apply embedState_eq_of_ports id (Fin.castAdd (s+2)) _ _ _ Function.injective_id (Fin.castAdd_injective ..)
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; simp [withBackup]
  · intro j
    refine Fin.addCases (m:=55) (n:=s+2) (motive:=fun j => (¬ ∃ i : Fin 55, i.castAdd (s+2)=j) →
      withBackup s b raw j=withBackup s a raw j) (fun i hi => (hi ⟨i,rfl⟩).elim) (fun i _ => ?_) j
    simp [withBackup]

private theorem io_call {s l : ℕ} (P : Program 8 55 l) (raw : List Bool)
    (r q : Fin 8 → Bool) (a b : Fin 55 → List Bool) (t : ℕ)
    (tr : Trace P t ⟨some P.entry,r,a⟩ ⟨none,q,b⟩) :
    Eval (.call (ProgramLinking.liftProgram P id (Fin.castAdd (s+2)))) t
      ⟨r,withBackup s a raw⟩ ⟨q,withBackup s b raw⟩ := by
  have h := eval_call_lifted P id (Fin.castAdd (s+2)) ⟨r,withBackup s a raw⟩
    Function.injective_id (Fin.castAdd_injective ..) (a:=⟨r,a⟩) (b:=⟨q,b⟩) tr
  simpa only [io_embed] using h

private theorem io_time (n m kp kw kq t u v : ℕ) (hn : 1 ≤ n)
    (ht : t ≤ (n+bitLen m+2)^kp) (hu : u ≤ (n+1+n+bitLen m+4)^kw)
    (hv : v ≤ (n+bitLen m+2)^kq) :
    t+(u+v)+1 ≤ (n+bitLen m+2)^(max kp (max (2*kw) kq)+2) := by
  let B := n+bitLen m+2
  let K := max kp (max (2*kw) kq)
  have hB : 3 ≤ B := by dsimp [B]; omega
  have hp : 1 ≤ B^K := Nat.one_le_pow _ _ (by omega)
  have hb : n+1+n+bitLen m+4 ≤ B^2 := by
    have h : n+1+n+bitLen m+4 ≤ 2*B+1 := by dsimp [B]; omega
    apply h.trans
    nlinarith only [hB,Nat.mul_le_mul_left B hB]
  have t' : t ≤ B^K := ht.trans (Nat.pow_le_pow_right (by omega : 0<B) (le_max_left ..))
  have v' : v ≤ B^K := hv.trans (Nat.pow_le_pow_right (by omega : 0<B) ((le_max_right ..).trans (le_max_right ..)))
  have u' : u ≤ B^(2*kw) := by rw [pow_mul]; exact hu.trans (Nat.pow_le_pow_left hb kw)
  have u'' : u ≤ B^K := u'.trans (Nat.pow_le_pow_right (by omega : 0<B) ((le_max_left ..).trans (le_max_right ..)))
  change _ ≤ B^(K+2)
  rw [pow_add]
  have h4 : 4 ≤ B^2 := by nlinarith only [hB,Nat.mul_le_mul_left B hB]
  nlinarith only [hp,t',u'',v',Nat.mul_le_mul_left (B^K) h4]

end DetDLP

open DetDLP OAI.Algorithms.SubexponentialSAT BitProgram StructuredCalls DetDLP.BorderedBitIO

theorem solution :
    ∃ (r s l : ℕ) (p : BitProgram.Program r s l) (out : Fin s) (k : ℕ),
      ∀ (m n : ℕ), 2 ≤ m → 1 ≤ n →
      ∀ (x a : Fin n → ℕ) (B : Matrix (Fin n) (Fin n) ℤ) (c : ℕ),
      (∀ i, x i < m) → (∀ i, a i < m) → c < m → (∀ i j, |B i j| ≤ (m:ℤ)) →
      let res := BorderedHermite.update m (Vector.ofFn x) (Vector.ofFn fun j => Vector.ofFn fun i => B i j)
        (Vector.ofFn a) c
      ∃ (steps : ℕ) (f : BitProgram.Cfg r s l),
        BitProgram.Trace p steps (BitProgram.initial p (encodeCosetUpdateInput m x B a c)) f ∧
        f.pc = none ∧ f.stacks out = encodeCosetRep res.1.get (fun i j => (res.2.get j).get i) ∧
        f.stacks p.outputStack = [true] ∧ steps ≤ (n+bitLen m+2)^k := by
  obtain ⟨u,U⟩ := bordered_binary_input_preparation
  obtain ⟨v,V⟩ := bordered_binary_output_recovery
  let s := max u v
  obtain ⟨pre,kp,HP⟩ := U s (le_max_left ..)
  obtain ⟨l,kw,P,HN⟩ := packed_hermite_normal_form_machine
  obtain ⟨post,kq,HQ⟩ := V s (le_max_right ..) P.outputStack
  let full : Code s := pre.seq ((Cmd.call (ProgramLinking.liftProgram P id (Fin.castAdd (s+2)))).seq post)
  refine ⟨8,55+(s+2),_,compiled full (backup s) (backup s),answer s,max kp (max (2*kw) kq)+2,?_⟩
  intro m n hm hn x a B c hx ha hc hB
  letI : NeZero m := ⟨by omega⟩
  let raw := encodeCosetUpdateInput m x B a c
  have valid : BorderedBitIO.Valid m x a B c := ⟨hm,hn,hx,ha,hc,hB⟩
  obtain ⟨t,r,ht,et⟩ := HP m x a B c valid
  obtain ⟨j,⟨pc,rr,ss⟩,ej,hpc,hw,hj⟩ := HN m (n+1) hm (columns a B) r
  change pc=none at hpc
  subst pc
  have inv := io_call (s:=s) P raw r rr (staged m (columns a B)) ss j ej
  obtain ⟨y,final,hy,ey,repok,flag⟩ := HQ m x a B c valid rr ss hw
  have all : Eval full (t+(j+y)) ⟨fun _ => false,initialStacks s raw⟩ final :=
    .seq et (.seq inv ey)
  have tr := compiled_halt_trace all (backup s) (backup s)
  refine ⟨_,_,tr,rfl,repok,flag,?_⟩
  have sz : (columns a B).size=n := by simp [columns]
  exact io_time n m kp kw kq t j y hn ht (by simpa only [sz] using hj) hy
