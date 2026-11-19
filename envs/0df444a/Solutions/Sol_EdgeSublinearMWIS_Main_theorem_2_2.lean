-- Prove2me | solution 2 for EdgeSublinearMWIS.Main.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T10:13:41.45442+00:00
-- url     : https://prove2.me/submissions/8b572f5b-f19a-4259-8934-31dd4db996ee

import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Size
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Theorems.Thm_EdgeSublinearMWIS_Main_treewidth_separator
import Mathlib.Combinatorics.SimpleGraph.Star
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Mathlib.Algebra.Order.Floor.Div
import Theorems.Thm_EdgeSublinearMWIS_Main_stack_simulation
import Definitions.Def_EdgeSublinearMWIS_Main_NativeSchemeInterfaces
import Theorems.Thm_EdgeSublinearMWIS_Main_RamBridge_uniform_bit_simulation
import Theorems.Thm_Lax263307Proofs_NativeQptasImplementation_exists_fixed
import Theorems.Thm_Lax263307Proofs_NativeWeightedExecution_command_spec
import Theorems.Thm_Lax808846Proofs_Simulation_compileProgram_runsTo

section

namespace Lax808846Proofs.Imp

@[simp] theorem Bop.apply_add (m n:ℕ):Bop.add.apply m n=m + n:=rfl
@[simp] theorem Bop.apply_sub (m n:ℕ):Bop.sub.apply m n=m - n:=rfl
@[simp] theorem Bop.apply_mul (m n:ℕ):Bop.mul.apply m n=m * n:=rfl
@[simp] theorem Bop.apply_div (m n:ℕ):Bop.div.apply m n=m / n:=rfl
@[simp] theorem Bop.apply_and (m n:ℕ):Bop.and.apply m n=Nat.land m n:=rfl
@[simp] theorem Bop.apply_or (m n:ℕ):Bop.or.apply m n=Nat.lor m n:=rfl
@[simp] theorem Bop.apply_xor (m n:ℕ):Bop.xor.apply m n=Nat.xor m n:=rfl
@[simp] theorem Bop.apply_shiftl (m n:ℕ):Bop.shiftl.apply m n=m * 2 ^ n:=rfl
@[simp] theorem Bop.apply_shiftr (m n:ℕ):Bop.shiftr.apply m n=m / 2 ^ n:=rfl

@[simp] theorem Expr.add_def (e f:Expr):Expr.add e f=.bin .add e f:=rfl
@[simp] theorem Expr.sub_def (e f:Expr):Expr.sub e f=.bin .sub e f:=rfl
@[simp] theorem Expr.mul_def (e f:Expr):Expr.mul e f=.bin .mul e f:=rfl
@[simp] theorem Expr.div_def (e f:Expr):Expr.div e f=.bin .div e f:=rfl
@[simp] theorem Expr.and_def (e f:Expr):Expr.and e f=.bin .and e f:=rfl
@[simp] theorem Expr.or_def (e f:Expr):Expr.or e f=.bin .or e f:=rfl
@[simp] theorem Expr.xor_def (e f:Expr):Expr.xor e f=.bin .xor e f:=rfl
@[simp] theorem Expr.shiftl_def (e f:Expr):Expr.shiftl e f=.bin .shiftl e f:=rfl
@[simp] theorem Expr.shiftr_def (e f:Expr):Expr.shiftr e f=.bin .shiftr e f:=rfl

def Expr.eval:Expr→ Env→ Option ℕ
  | lit n,_ => some n
  | var x,σ => some (σ.vars x)
  | get a i,σ => (i.eval σ).bind fun k => (σ.arrs a)[k]?
  | bin op e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => op.apply m n

def Cond.eval:Cond→ Env→ Option Bool
  | eq e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => m == n
  | lt e f,σ => (e.eval σ).bind fun m => (f.eval σ).map fun n => decide (m < n)

inductive BigStep:Com→ Env→ Env→ ℕ→ Prop

  | skip {σ:Env}:BigStep .skip σ σ 1

  | assign {σ:Env} {x:String} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.assign x e) σ (σ.setVar x v) (1 + e.size)

  | store {σ:Env} {a:String} {i e:Expr} {k v:ℕ}
      (hi:i.eval σ=some k) (he:e.eval σ=some v)
      (hk:k < (σ.arrs a).length):
      BigStep (.store a i e) σ (σ.setArr a k v) (1 + i.size + e.size)

  | seq {c d:Com} {σ σ' σ'':Env} {k k':ℕ}:
      BigStep c σ σ' k→ BigStep d σ' σ'' k'→
      BigStep (.seq c d) σ σ'' (k + k')

  | ite_true {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | ite_false {b:Cond} {c d:Com} {σ σ':Env} {k:ℕ}
      (hb:b.eval σ=some false) (hd:BigStep d σ σ' k):
      BigStep (.ite b c d) σ σ' (1 + b.size + k)

  | while_true {b:Cond} {c:Com} {σ σ' σ'':Env} {k k':ℕ}
      (hb:b.eval σ=some true) (hc:BigStep c σ σ' k)
      (hw:BigStep (.while b c) σ' σ'' k'):
      BigStep (.while b c) σ σ'' (1 + b.size + k + k')

  | while_false {b:Cond} {c:Com} {σ:Env} (hb:b.eval σ=some false):
      BigStep (.while b c) σ σ (1 + b.size)

  | read {σ:Env} {x:String} {v:ℕ} {rest:List ℕ} (h:σ.inp=v::rest):
      BigStep (.read x) σ { σ.setVar x v with inp:=rest } 1

  | write {σ:Env} {e:Expr} {v:ℕ} (h:e.eval σ=some v):
      BigStep (.write e) σ { σ with out:=σ.out ++ [v] } (1 + e.size)

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Imp

theorem fit_eq_some {B v u:ℕ}:fit B v=some u↔ u=v∧ v < B:=by
  constructor
  · intro h
    by_cases hv:v < B
    · rw [fit,if_pos hv] at h
      exact ⟨(Option.some.inj h).symm,hv⟩
    · rw [fit,if_neg hv] at h; exact absurd h (by simp)
  · rintro ⟨rfl,h⟩; rw [fit,if_pos h]

theorem fit_self {B v:ℕ} (h:v < B):fit B v=some v:=by rw [fit,if_pos h]

end Lax808846Proofs.Imp

end

section

namespace Lax808846Proofs.Reasoning

open Lax808846Proofs.Imp Lax808846Proofs.Compile

@[simp] theorem vars_setVar (σ:Env) (x:String) (v:ℕ) (y:String):
    (σ.setVar x v).vars y=if y=x then v else σ.vars y:=rfl

@[simp] theorem arrs_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).arrs=σ.arrs:=rfl

@[simp] theorem inp_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).inp=σ.inp:=rfl

@[simp] theorem out_setVar (σ:Env) (x:String) (v:ℕ):
    (σ.setVar x v).out=σ.out:=rfl

@[simp] theorem vars_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).vars=σ.vars:=rfl

@[simp] theorem arrs_setArr (σ:Env) (a:String) (i v:ℕ) (b:String):
    (σ.setArr a i v).arrs b=if b=a then (σ.arrs a).set i v else σ.arrs b:=rfl

@[simp] theorem inp_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).inp=σ.inp:=rfl

@[simp] theorem out_setArr (σ:Env) (a:String) (i v:ℕ):
    (σ.setArr a i v).out=σ.out:=rfl

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

@[simp] theorem evalB_lit_iff {B n v:ℕ} {σ:Env}:
    (Expr.lit n).evalB B σ=some v↔ v=n∧ n < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_var_iff {B:ℕ} {x:String} {σ:Env} {v:ℕ}:
    (Expr.var x).evalB B σ=some v↔ v=σ.vars x∧ σ.vars x < B:=by
  rw [Expr.evalB,fit_eq_some]

@[simp] theorem evalB_get_iff {B:ℕ} {a:String} {i:Expr} {σ:Env} {v:ℕ}:
    (Expr.get a i).evalB B σ=some v↔
      ∃ k,i.evalB B σ=some k∧ (σ.arrs a)[k]?=some v∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨k,hk,u,hu,rfl,hlt⟩; exact ⟨k,hk,hu,hlt⟩
  · rintro ⟨k,hk,hu,hlt⟩; exact ⟨k,hk,v,hu,rfl,hlt⟩

@[simp] theorem evalB_bin_iff {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {v:ℕ}:
    (Expr.bin op e f).evalB B σ=some v↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ v=op.apply m n∧ v < B:=by
  rw [Expr.evalB]
  simp only [Option.bind_eq_some_iff,fit_eq_some]
  constructor
  · rintro ⟨m,hm,n,hn,rfl,hlt⟩; exact ⟨m,n,hm,hn,rfl,hlt⟩
  · rintro ⟨m,n,hm,hn,rfl,hlt⟩; exact ⟨m,hm,n,hn,rfl,hlt⟩

@[simp] theorem evalB_condEq_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.eq e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=(m == n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

@[simp] theorem evalB_condLt_iff {B:ℕ} {e f:Expr} {σ:Env} {r:Bool}:
    (Cond.lt e f).evalB B σ=some r↔
      ∃ m n,e.evalB B σ=some m∧ f.evalB B σ=some n∧ r=decide (m < n):=by
  rw [Cond.evalB]
  simp only [Option.bind_eq_some_iff,Option.map_eq_some_iff]
  constructor
  · rintro ⟨m,hm,n,hn,rfl⟩; exact ⟨m,n,hm,hn,rfl⟩
  · rintro ⟨m,n,hm,hn,rfl⟩; exact ⟨m,hm,n,hn,rfl⟩

theorem evalB_lit {B n:ℕ} {σ:Env} (h:n < B):(Expr.lit n).evalB B σ=some n:=
  fit_self h

theorem evalB_var {B:ℕ} {x:String} {σ:Env} (h:σ.vars x < B):
    (Expr.var x).evalB B σ=some (σ.vars x):=fit_self h

theorem evalB_get {B:ℕ} {a:String} {i:Expr} {σ:Env} {k v:ℕ}
    (hi:i.evalB B σ=some k) (hk:(σ.arrs a)[k]?=some v) (hv:v < B):
    (Expr.get a i).evalB B σ=some v:=by
  rw [Expr.evalB,hi,Option.bind_some,hk,Option.bind_some,fit_self hv]

theorem evalB_bin {B:ℕ} {op:Bop} {e f:Expr} {σ:Env} {m n:ℕ}
    (he:e.evalB B σ=some m) (hf:f.evalB B σ=some n) (h:op.apply m n < B):
    (Expr.bin op e f).evalB B σ=some (op.apply m n):=by
  rw [Expr.evalB,he,Option.bind_some,hf,Option.bind_some,fit_self h]

@[simp] theorem size_lit (n:ℕ):(Expr.lit n).size=1:=rfl
@[simp] theorem size_var (x:String):(Expr.var x).size=1:=rfl
@[simp] theorem size_get (a:String) (i:Expr):(Expr.get a i).size=i.size + 1:=rfl
@[simp] theorem size_bin (op:Bop) (e f:Expr):
    (Expr.bin op e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_add (e f:Expr):(Expr.add e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_sub (e f:Expr):(Expr.sub e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_mul (e f:Expr):(Expr.mul e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_div (e f:Expr):(Expr.div e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_and (e f:Expr):(Expr.and e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_or (e f:Expr):(Expr.or e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_xor (e f:Expr):(Expr.xor e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftl (e f:Expr):(Expr.shiftl e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_shiftr (e f:Expr):(Expr.shiftr e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condEq (e f:Expr):(Cond.eq e f).size=e.size + f.size + 1:=rfl
@[simp] theorem size_condLt (e f:Expr):(Cond.lt e f).size=e.size + f.size + 1:=rfl

theorem Run.of_bigStepB {B:ℕ} {c:Com} {σ σ':Env} {k:ℕ} (h:BigStepB B c σ σ' k):
    Run B c σ σ' k:= ⟨k,le_rfl,h⟩

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

theorem Run.assign {B:ℕ} {σ:Env} {x:String} {e:Expr} {v:ℕ}
    (h:e.evalB B σ=some v):
    Run B (.assign x e) σ (σ.setVar x v) (1 + e.size):=.of_bigStepB (.assign h)

theorem Run.read {B:ℕ} {σ:Env} {x:String} {v:ℕ} {rest:List ℕ}
    (h:σ.inp=v::rest):
    Run B (.read x) σ { σ.setVar x v with inp:=rest } 1:=.of_bigStepB (.read h)

theorem Run.seq {B:ℕ} {c d:Com} {σ σ' σ'':Env} {K K':ℕ}
    (h:Run B c σ σ' K) (h':Run B d σ' σ'' K'):Run B (.seq c d) σ σ'' (K + K'):=by
  obtain ⟨k,hk,hbs⟩:=h
  obtain ⟨k',hk',hbs'⟩:=h'
  exact ⟨k + k',by omega, .seq hbs hbs'⟩

end Lax808846Proofs.Reasoning

end

section

namespace EdgeSublinearMWIS.Main.RamBridge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

def appendInput (σ:Env) (extra:List ℕ):Env:= {σ with inp:=σ.inp++extra}

@[simp] theorem eval_append (e:Expr) (B:ℕ) (σ:Env) (extra:List ℕ):
    e.evalB B (appendInput σ extra)=e.evalB B σ:=by
  induction e with
  | lit => rfl
  | var => rfl
  | get a i ih => simp only [Expr.evalB,ih]; rfl
  | bin op e f ihe ihf => simp [Expr.evalB,ihe,ihf]

@[simp] theorem cond_append (c:Cond) (B:ℕ) (σ:Env) (extra:List ℕ):
    c.evalB B (appendInput σ extra)=c.evalB B σ:=by
  cases c <;> simp [Cond.evalB]

 theorem bigStepB_append {B:ℕ} {c:Com} {σ τ:Env} {t:ℕ}
    (h:BigStepB B c σ τ t) (extra:List ℕ):
    BigStepB B c (appendInput σ extra) (appendInput τ extra) t:=by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (by simpa using h)
  | store hi he hk => exact .store (by simpa using hi) (by simpa using he) hk
  | seq h₁ h₂ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb h ih => exact .ite_true (by simpa using hb) ih
  | ite_false hb h ih => exact .ite_false (by simpa using hb) ih
  | while_true hb h₁ h₂ ih₁ ih₂ => exact .while_true (by simpa using hb) ih₁ ih₂
  | while_false hb => exact .while_false (by simpa using hb)
  | @read σ x v rest h =>
    have hr:(appendInput σ extra).inp=v::(rest++extra):=by simp [appendInput,h]
    exact .read hr
  | write h => exact .write (by simpa using h)

 theorem run_append {B:ℕ} {c:Com} {σ τ:Env} {t:ℕ}
    (h:Run B c σ τ t) (extra:List ℕ):
    Run B c (appendInput σ extra) (appendInput τ extra) t:=by
  obtain ⟨k,hk,hr⟩:=h
  exact ⟨k,hk,bigStepB_append hr extra⟩

 theorem eval_widen {B D:ℕ} (hBD:B≤ D) {e:Expr} {σ:Env} {v:ℕ}
    (h:e.evalB B σ=some v):e.evalB D σ=some v:=by
  induction e generalizing v with
  | lit n =>
    obtain ⟨rfl,hn⟩:=evalB_lit_iff.mp h
    exact evalB_lit (hn.trans_le hBD)
  | var x =>
    obtain ⟨rfl,hn⟩:=evalB_var_iff.mp h
    exact evalB_var (hn.trans_le hBD)
  | get a i ih =>
    obtain ⟨k,hk,hv,hlt⟩:=evalB_get_iff.mp h
    exact evalB_get (ih hk) hv (hlt.trans_le hBD)
  | bin op e f ihe ihf =>
    obtain ⟨m,n,hm,hn,rfl,hlt⟩:=evalB_bin_iff.mp h
    exact evalB_bin (ihe hm) (ihf hn) (hlt.trans_le hBD)

 theorem cond_widen {B D:ℕ} (hBD:B≤ D) {c:Cond} {σ:Env} {v:Bool}
    (h:c.evalB B σ=some v):c.evalB D σ=some v:=by
  cases c with
  | eq e f =>
    obtain ⟨m,n,hm,hn,rfl⟩:=evalB_condEq_iff.mp h
    exact evalB_condEq_iff.mpr ⟨m,n,eval_widen hBD hm,eval_widen hBD hn,rfl⟩
  | lt e f =>
    obtain ⟨m,n,hm,hn,rfl⟩:=evalB_condLt_iff.mp h
    exact evalB_condLt_iff.mpr ⟨m,n,eval_widen hBD hm,eval_widen hBD hn,rfl⟩

 theorem bigStepB_widen {B D:ℕ} (hBD:B≤ D) {c:Com} {σ τ:Env} {t:ℕ}
    (h:BigStepB B c σ τ t):BigStepB D c σ τ t:=by
  induction h with
  | skip => exact .skip
  | assign h => exact .assign (eval_widen hBD h)
  | store hi he hk => exact .store (eval_widen hBD hi) (eval_widen hBD he) hk
  | seq h₁ h₂ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ite_true hb h ih => exact .ite_true (cond_widen hBD hb) ih
  | ite_false hb h ih => exact .ite_false (cond_widen hBD hb) ih
  | while_true hb h₁ h₂ ih₁ ih₂ => exact .while_true (cond_widen hBD hb) ih₁ ih₂
  | while_false hb => exact .while_false (cond_widen hBD hb)
  | read h => exact .read h
  | write h => exact .write (eval_widen hBD h)

 theorem run_widen {B D:ℕ} (hBD:B≤ D) {c:Com} {σ τ:Env} {t:ℕ}
    (h:Run B c σ τ t):Run D c σ τ t:=by
  obtain ⟨k,hk,hr⟩:=h
  exact ⟨k,hk,bigStepB_widen hBD hr⟩

end EdgeSublinearMWIS.Main.RamBridge

end

section

namespace Lax808846Proofs.Transfer

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Compile
open Lax808846Proofs.Simulation Lax808846Proofs.Reasoning

theorem fitsWords_of_max_le {L:Layout} {B w:ℕ} (h1:1 < B)
    (h:max B (L.span B)≤ 2 ^ w):L.FitsWords B w:=
  ⟨h1,le_trans (le_max_left _ _) h,le_trans (le_max_right _ _) h⟩

end Lax808846Proofs.Transfer

end

section

namespace Lax455465Proofs.RamTransfer

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax808846Proofs.Transfer
open Lax759944.BinaryWordEncoding Lax759944.RamPolytime

def layoutAllowance (L:Layout):ℕ:=
  L.temps + 2 + L.scalars.length + L.arrays.length + 1

theorem layout_fits {L:Layout} {v w:ℕ} (hv:0 < v)
    (hw:v + layoutAllowance L≤ w):L.FitsWords (2 ^ v) w:=by
  have hB:1 < 2 ^ v:=Nat.one_lt_pow (ne_of_gt hv) (by decide)
  have hc:layoutAllowance L≤ 2 ^ layoutAllowance L:=Nat.lt_two_pow_self.le
  have hs:max (2 ^ v) (L.span (2 ^ v))≤ 2 ^ (v + layoutAllowance L):=by
    rw [pow_add]
    apply max_le
    · exact Nat.le_mul_of_pos_right _ (by positivity)
    · unfold Layout.span
      have hp:1≤ 2 ^ v:=hB.le
      calc
        _≤ (L.temps + 2 + L.scalars.length) * 2 ^ v + L.arrays.length * 2 ^ v:=by
          exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hp) _
        _≤ layoutAllowance L * 2 ^ v:=by unfold layoutAllowance; nlinarith
        _≤ _:=by simpa [Nat.mul_comm] using Nat.mul_le_mul_right (2 ^ v) hc
  exact fitsWords_of_max_le hB (hs.trans (Nat.pow_le_pow_right (by decide) hw))

end Lax455465Proofs.RamTransfer

end

section

namespace Lax455465Proofs.RamAutomaticLayout

open Lax808846Proofs.Imp Lax808846Proofs.Compile

def expressionNames:Expr→ List String × List String
  | .lit _ => ([], [])
  | .var x => ([x], [])
  | .get a i => let old:=expressionNames i; (old.1,a::old.2)
  | .bin _ e f => let a:=expressionNames e; let b:=expressionNames f; (a.1 ++ b.1,a.2 ++ b.2)

def conditionNames (b:Cond):List String × List String:=expressionNames (condExpr b)

def commandNames:Com→ List String × List String
  | .skip => ([], [])
  | .assign x e => let a:=expressionNames e; (x::a.1,a.2)
  | .store x i e => let a:=expressionNames i; let b:=expressionNames e; (a.1 ++ b.1,x::(a.2 ++ b.2))
  | .seq c d => let a:=commandNames c; let b:=commandNames d; (a.1 ++ b.1,a.2 ++ b.2)
  | .ite b c d => let a:=conditionNames b; let x:=commandNames c; let y:=commandNames d;
      (a.1 ++ x.1 ++ y.1,a.2 ++ x.2 ++ y.2)
  | .while b c => let a:=conditionNames b; let x:=commandNames c; (a.1 ++ x.1,a.2 ++ x.2)
  | .read x => ([x], [])
  | .write e => expressionNames e

def commandDepth:Com→ ℕ
  | .skip | .read _ => 1
  | .assign _ e | .write e => e.size + 2
  | .store _ i e => max i.size e.size + 2
  | .seq c d => max (commandDepth c) (commandDepth d)
  | .ite b c d => max (condExpr b).size (max (commandDepth c) (commandDepth d)) + 2
  | .while b c => max (condExpr b).size (commandDepth c) + 2

def layout (c:Com):Layout:= ⟨(commandNames c).1, (commandNames c).2,commandDepth c + 2⟩

theorem expression_ok (e:Expr) (L:Layout) (d:ℕ)
    (hv:(expressionNames e).1 ⊆ L.scalars) (ha:(expressionNames e).2 ⊆ L.arrays)
    (hd:d + e.size < L.temps):Expr.Ok L e d:=by
  induction e generalizing d with
  | lit v => trivial
  | var x => exact hv (by simp [expressionNames])
  | get a i ih =>
    refine ⟨ha (by simp [expressionNames]),ih d
      (by simpa [expressionNames] using hv)
      (fun x hx => ha (by simp [expressionNames,hx])) ?_, ?_⟩
    all_goals simp only [Expr.size] at hd; omega
  | bin op e f ihe ihf =>
    have hve:(expressionNames e).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hvf:(expressionNames f).1 ⊆ L.scalars:=fun x hx => hv (by simp [expressionNames,hx])
    have hae:(expressionNames e).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    have haf:(expressionNames f).2 ⊆ L.arrays:=fun x hx => ha (by simp [expressionNames,hx])
    simp only [Expr.Ok]
    exact ⟨ihf d hvf haf (by simp only [Expr.size] at hd; omega),
      ihe (d + 1) hve hae (by simp only [Expr.size] at hd; omega),
      by simp only [Expr.size] at hd; omega⟩

theorem command_ok (c:Com) (L:Layout)
    (hv:(commandNames c).1 ⊆ L.scalars) (ha:(commandNames c).2 ⊆ L.arrays)
    (hd:commandDepth c < L.temps):Com.Ok L c:=by
  induction c with
  | skip => trivial
  | read x => exact hv (by simp [commandNames])
  | assign x e =>
    refine ⟨hv (by simp [commandNames]),expression_ok e L 0
      (fun x hx => hv (by simp [commandNames,hx])) (by simpa [commandNames] using ha) ?_⟩
    simp only [commandDepth] at hd; omega
  | store a i e =>
    refine ⟨ha (by simp [commandNames]),expression_ok i L 0
      (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      expression_ok e L 1 (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | write e =>
    refine ⟨expression_ok e L 0 hv ha ?_, ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | seq c d ihc ihd =>
    refine ⟨ihc (fun x hx => hv (by simp [commandNames,hx]))
      (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx]))
        (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | ite b c d ihc ihd =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ihc (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_,
      ihd (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega
  | «while» b c ih =>
    refine ⟨expression_ok (condExpr b) L 0
      (fun x hx => hv (by simp [commandNames,conditionNames,hx]))
      (fun x hx => ha (by simp [commandNames,conditionNames,hx])) ?_,
      ih (fun x hx => hv (by simp [commandNames,hx])) (fun x hx => ha (by simp [commandNames,hx])) ?_⟩
    all_goals simp only [commandDepth] at hd; omega

theorem layout_ok (c:Com):Com.Ok (layout c) c:=
  command_ok c (layout c) (fun _ h => h) (fun _ h => h) (by simp [layout])

end Lax455465Proofs.RamAutomaticLayout

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem bitSize_append (xs ys:List ℕ):bitSize (xs ++ ys)=bitSize xs + bitSize ys:=by
  simp [bitSize,encode]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

end Lax455465Proofs.WordSize

end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs
open Lax759944.BinaryWordEncoding

 def paddedCommand (c:Com):Com:=
   .seq (.read "padding.discard") (.seq (.assign "padding.discard" (.lit 0)) c)

 theorem padded_command_run {B:ℕ} (hB:0<B) {c:Com} {ext:String→ ℕ}
    {xs:List ℕ} {τ:Env} {t:ℕ} (h:Run B c (initEnv ext xs) τ t) (extra:List ℕ):
    Run B (paddedCommand c) (initEnv ext ((xs++extra).length::(xs++extra))) (appendInput τ extra) (t+3):=by
  let σ:=initEnv ext ((xs++extra).length::(xs++extra))
  let μ:Env:= {σ.setVar "padding.discard" (xs++extra).length with inp:=xs++extra}
  have hread:Run B (.read "padding.discard") σ μ 1:=Run.read rfl
  have hreset:μ.setVar "padding.discard" 0=initEnv ext (xs++extra):=by
    simp [μ,σ,initEnv,Env.setVar]
    funext y
    split_ifs <;> rfl
  have hr:Run B (.assign "padding.discard" (.lit 0)) μ (initEnv ext (xs++extra)) 2:=by
    rw [← hreset]
    exact Run.assign (evalB_lit hB)
  have hbody:=run_append h extra
  change Run B c (initEnv ext (xs++extra)) (appendInput τ extra) t at hbody
  exact (hread.seq (hr.seq hbody)).mono (by omega)

 def paddedProgram (c:Com):Lax808846.Ram.Program:=
   compileProgram (RamAutomaticLayout.layout (paddedCommand c)) (paddedCommand c)

 theorem padded_program_run {c:Com} {xs ys:List ℕ} {t v:ℕ}
    (h:∃ ext τ,Run (2^v) c (initEnv ext xs) τ t∧ τ.out=ys)
    (padding w:ℕ)
    (hv:v≤ bitSize (xs++List.replicate padding 0)+1)
    (hw:bitSize (xs++List.replicate padding 0)+1+
      RamTransfer.layoutAllowance (RamAutomaticLayout.layout (paddedCommand c))≤ w):
    ∃ s≤ (RamAutomaticLayout.layout (paddedCommand c)).const*(t+3)+1,
      Lax808846.Ram.RunsTo w (paddedProgram c)
        ((xs++List.replicate padding 0).length::(xs++List.replicate padding 0)) ys s:=by
  obtain ⟨ext,τ,hRun,hout⟩:=h
  let padded:=xs++List.replicate padding 0
  let b:=bitSize padded+1
  have hRun':=run_widen (Nat.pow_le_pow_right (by decide:1≤2) hv) hRun
  have hr:=padded_command_run (Nat.two_pow_pos b) hRun' (List.replicate padding 0)
  obtain ⟨k,hk,hkRun⟩:=hr
  have hfit:=RamTransfer.layout_fits (L:=RamAutomaticLayout.layout (paddedCommand c))
    (by dsimp [b]; omega:0<b) hw
  have hin:∀ a∈padded.length::padded,a<2^b:=by
    intro a ha
    rcases List.mem_cons.mp ha with rfl|ha
    · have hl:=WordSize.length_le padded
      exact hl.trans_lt (by dsimp [b]; exact (Nat.le_succ _).trans_lt Nat.lt_two_pow_self)
    · exact (WordSize.member_bound padded a ha).trans_le
        (Nat.pow_le_pow_right (by decide) (by dsimp [b]; omega))
  obtain ⟨s,hs,hram⟩:=Lax808846Proofs.Simulation.compileProgram_runsTo hfit
    (RamAutomaticLayout.layout_ok (paddedCommand c)) hin hkRun
  refine ⟨s,hs.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hk) 1),?_⟩
  simpa only [paddedProgram,appendInput,hout] using hram

end EdgeSublinearMWIS.Main.RamBridge

end

section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kDecidableEq
open Turing.TM2
variable {κ Λ σ:Type} [DecidableEq κ] {Γ:κ→ Type}

 def cfg (l:Option Λ) (v:σ) (S:∀i,List (Γ i)):Cfg Γ Λ σ:= ⟨l,v,S⟩
 def run (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ):ℕ→ Option (Cfg Γ Λ σ)
   | 0 => some c
   | t+1 => (run code c t).bind (step code)

 theorem run_iter (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (t:ℕ):
    run code c t=(fun o:Option (Cfg Γ Λ σ) => o.bind (step code))^[t] (some c):=by
  induction t with
  | zero => rfl
  | succ t ih => rw [run,ih,Function.iterate_succ_apply']

 theorem run_add (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (s t:ℕ):
    run code c (s+t)=(run code c s).bind (fun d => run code d t):=by
  induction t with
  | zero => simp only [Nat.add_zero,run]; cases run code c s <;> rfl
  | succ t ih => rw [Nat.add_succ,run,ih]; simp only [Option.bind_assoc,run]

 theorem run_trans (code:Λ→ Stmt Γ Λ σ) (c d e:Cfg Γ Λ σ) (s t:ℕ)
    (hs:run code c s=some d) (ht:run code d t=some e):run code c (s+t)=some e:=by
  rw [run_add,hs,Option.bind_some,ht]

 theorem run_one (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ):run code c 1=step code c:=rfl

 theorem run_first (code:Λ→ Stmt Γ Λ σ) (c:Cfg Γ Λ σ) (t:ℕ):
    run code c (t+1)=(step code c).bind (fun d => run code d t):=by
  rw [show t+1=1+t by omega,run_add,run_one]

 theorem outputs {tm:Turing.FinTM2} (input:List (tm.Γ tm.k₀)) (output:List (tm.Γ tm.k₁))
    (t:ℕ) (h:run tm.m (Turing.initList tm input) t=some (Turing.haltList tm output)):
    Nonempty (Turing.TM2OutputsInTime tm input (some output) t):=by
  refine ⟨⟨⟨t,?_⟩,le_rfl⟩⟩
  have h':=run_iter tm.m (Turing.initList tm input) t
  rw [h'] at h
  exact h

end EdgeSublinearMWIS.Main.RawStack

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ:Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ:κ→ Type} {Δ:μ→ Type}

 abbrev StackSum (A:κ→ Type) (B:μ→ Type):κ⊕μ→ Type
   | .inl k => A k
   | .inr k => B k

 def extendStore (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):∀k:κ⊕μ,List (StackSum Γ Δ k):=fun k => match k with | .inl k => S k | .inr k => T k
 @[simp] theorem extendStore_inl (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ):extendStore S T (.inl k)=S k:=rfl
 @[simp] theorem extendStore_inr (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:μ):extendStore S T (.inr k)=T k:=rfl

 def extendCfg (ret:Ω) (v:τ) (T:∀k,List (Δ k)) (c:Cfg Γ Λ σ):
     Cfg (StackSum Γ Δ) (Λ⊕Ω) (σ×τ):=
   ⟨some (match c.l with | none => .inr ret | some l => .inl l),(c.var,v),extendStore c.stk T⟩
 def extendStmt (ret:Ω):Stmt Γ Λ σ→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ)
   | .push k f q => .push (.inl k) (fun v => f v.1) (extendStmt ret q)
   | .pop k f q => .pop (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .peek k f q => .peek (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .load f q => .load (fun v => (f v.1,v.2)) (extendStmt ret q)
   | .branch f q r => .branch (fun v => f v.1) (extendStmt ret q) (extendStmt ret r)
   | .goto f => .goto (fun v => .inl (f v.1))
   | .halt => .goto (fun _ => .inr ret)

 theorem update_extend (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ) (x:List (Γ k)):
     Function.update (extendStore S T) (.inl k) x=extendStore (Function.update S k x) T:=by
   funext j
   cases j with
   | inl j =>
     by_cases h:j=k
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
   | inr j => simp [Function.update,extendStore]

 theorem stepAux_extend (ret:Ω) (q:Stmt Γ Λ σ) (v:σ) (w:τ)
     (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):
     stepAux (extendStmt ret q) (v,w) (extendStore S T)=extendCfg ret w T (stepAux q v S):=by
   induction q generalizing v S with
   | push k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | pop k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     rw [update_extend]
     exact ih _ _
   | peek k f q ih =>
     simp only [extendStmt,stepAux,extendStore_inl]
     exact ih _ _
   | load f q ih => simpa only [extendStmt,stepAux,extendStore_inl] using ih (f v) S
   | branch f q r iq ir =>
     cases hf:f v <;> simp only [extendStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_extend (ret:Ω) (code:Λ→ Stmt Γ Λ σ)
     (target:Λ⊕Ω→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode:∀l,target (.inl l)=extendStmt ret (code l))
     (c:Cfg Γ Λ σ) (w:τ) (T:∀k,List (Δ k)) (l:Λ) (hc:c.l=some l):
     step target (extendCfg ret w T c)=(step code c).map (extendCfg ret w T):=by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [extendCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_extend ret (code l) v w S T)

 theorem run_extend (ret:Ω) (code:Λ→ Stmt Γ Λ σ)
     (target:Λ⊕Ω→ Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode:∀l,target (.inl l)=extendStmt ret (code l))
     (c d:Cfg Γ Λ σ) (w:τ) (T:∀k,List (Δ k)) (t:ℕ)
     (hr:RawStack.run code c t=some d):
     RawStack.run target (extendCfg ret w T c) t=some (extendCfg ret w T d):=by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc:c.l with
     | none =>
       have hn:step code c=none:=by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs:∃ e,step code c=some e:=by cases c; simp_all [step]
       obtain ⟨e,he⟩:=hs
       rw [step_extend ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.TernaryAdapter
open Turing.TM2 ProgramComposition Lax759944.BinaryWordEncoding
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 @[simp] theorem binarySymbols_length (xs:List Symbol):(binarySymbols xs).length=2*xs.length:=by
   induction xs with
   | nil => rfl
   | cons a xs ih => simp only [binarySymbols,List.flatMap_cons,List.length_append,symbolBits,List.length_cons,List.length_nil] at *; omega

end EdgeSublinearMWIS.Main.TernaryAdapter

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ:Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ:κ→ Type} {Δ:μ→ Type}

 def prefixStore (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):∀k:μ⊕κ,List (StackSum Δ Γ k):=fun k => match k with | .inl k => T k | .inr k => S k
 @[simp] theorem prefixStore_source (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ):prefixStore S T (.inr k)=S k:=rfl
 @[simp] theorem prefixStore_extra (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:μ):prefixStore S T (.inl k)=T k:=rfl

 def prefixCfg (ret:Ω) (v:τ) (T:∀k,List (Δ k)) (c:Cfg Γ Λ σ):
     Cfg (StackSum Δ Γ) (Ω⊕Λ) (τ×σ):=
   ⟨some (match c.l with | none => .inl ret | some l => .inr l),(v,c.var),prefixStore c.stk T⟩
 def prefixStmt (ret:Ω):Stmt Γ Λ σ→ Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ)
   | .push k f q => .push (.inr k) (fun v => f v.2) (prefixStmt ret q)
   | .pop k f q => .pop (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .peek k f q => .peek (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .load f q => .load (fun v => (v.1,f v.2)) (prefixStmt ret q)
   | .branch f q r => .branch (fun v => f v.2) (prefixStmt ret q) (prefixStmt ret r)
   | .goto f => .goto (fun v => .inr (f v.2))
   | .halt => .goto (fun _ => .inl ret)

 theorem update_prefix (S:∀k,List (Γ k)) (T:∀k,List (Δ k)) (k:κ) (x:List (Γ k)):
     Function.update (prefixStore S T) (.inr k) x=prefixStore (Function.update S k x) T:=by
   funext j
   cases j with
   | inr j =>
     by_cases h:j=k
     · subst j; simp [Function.update,prefixStore]
     · simp [Function.update,prefixStore,h]
   | inl j => simp [Function.update,prefixStore]

 theorem stepAux_prefix (ret:Ω) (q:Stmt Γ Λ σ) (v:σ) (w:τ)
     (S:∀k,List (Γ k)) (T:∀k,List (Δ k)):
     stepAux (prefixStmt ret q) (w,v) (prefixStore S T)=prefixCfg ret w T (stepAux q v S):=by
   induction q generalizing v S with
   | push k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     rw [update_prefix]
     exact ih _ _
   | pop k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     rw [update_prefix]
     exact ih _ _
   | peek k f q ih =>
     simp only [prefixStmt,stepAux,prefixStore_source]
     exact ih _ _
   | load f q ih => simpa only [prefixStmt,stepAux,prefixStore_source] using ih (f v) S
   | branch f q r iq ir =>
     cases hf:f v <;> simp only [prefixStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackSpace

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

variable {K:Type} {Γ:K→ Type} {Λ σ:Type}

 def cost:Turing.TM2.Stmt Γ Λ σ→ ℕ
  | .push _ _ q => cost q + 1
  | .peek _ _ q => cost q + 1
  | .pop _ _ q => cost q + 1
  | .load _ q => cost q + 1
  | .branch _ q r => max (cost q) (cost r) + 1
  | .goto _ => 1
  | .halt => 1

 def space [Fintype K] (S:∀ k,List (Γ k)):ℕ:= ∑ k, (S k).length

 theorem space_update [Fintype K] [DecidableEq K] (S:∀ k,List (Γ k)) (k:K) (L:List (Γ k)):
    space (Function.update S k L) + (S k).length=space S + L.length:=by
  have heq:(fun j => (Function.update S k L j).length)=Function.update (fun j => (S j).length) k L.length:=by
    funext j
    by_cases h:j=k
    · subst j; simp
    · simp [Function.update,h]
  unfold space
  rw [heq,Finset.sum_update_of_mem (Finset.mem_univ k),Finset.sdiff_singleton_eq_erase]
  have hsum:=Finset.sum_erase_add (s:=Finset.univ) (fun j => (S j).length) (Finset.mem_univ k)
  omega

 theorem stepAux_space [Fintype K] [DecidableEq K] (q:Turing.TM2.Stmt Γ Λ σ)
    (v:σ) (S:∀ k,List (Γ k)):
    space (Turing.TM2.stepAux q v S).stk≤ space S + cost q:=by
  induction q generalizing v S with
  | push k f q ih =>
    have hh:=ih v (Function.update S k (f v::S k))
    have hu:=space_update S k (f v::S k)
    simp only [List.length_cons] at hu
    change space (Turing.TM2.stepAux q v (Function.update S k (f v::S k))).stk≤ space S + (cost q + 1)
    omega
  | peek k f q ih =>
    have hh:=ih (f v (S k).head?) S
    change space (Turing.TM2.stepAux q (f v (S k).head?) S).stk≤ space S + (cost q + 1)
    omega
  | pop k f q ih =>
    have hh:=ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu:=space_update S k (S k).tail
    have hl:(S k).tail.length≤ (S k).length:=by simp only [List.length_tail]; omega
    change space (Turing.TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk≤ space S + (cost q + 1)
    omega
  | load f q ih =>
    have hh:=ih (f v) S
    change space (Turing.TM2.stepAux q (f v) S).stk≤ space S + (cost q + 1)
    omega
  | branch f q r ihq ihr =>
    change space (cond (f v) (Turing.TM2.stepAux q v S) (Turing.TM2.stepAux r v S)).stk≤ space S + (max (cost q) (cost r) + 1)
    cases hv:f v with
    | false => simp only [cond_false]; have hh:=ihr v S; have hm:=le_max_right (cost q) (cost r); omega
    | true => simp only [cond_true]; have hh:=ihq v S; have hm:=le_max_left (cost q) (cost r); omega
  | goto f => simp [Turing.TM2.stepAux,cost]
  | halt => simp [Turing.TM2.stepAux,cost]

 def bound (tm:Turing.FinTM2):ℕ:=Finset.univ.sup (fun l => cost (tm.m l))

 theorem cost_le_bound (tm:Turing.FinTM2) (l:tm.Λ):cost (tm.m l)≤ bound tm:=by
  unfold bound
  exact Finset.le_sup (f:=fun l => cost (tm.m l)) (Finset.mem_univ l)

 theorem initial_space (tm:Turing.FinTM2) (input:List (tm.Γ tm.k₀)):
    space (Turing.initList tm input).stk=input.length:=by
  have hlen (k:tm.K):((Turing.initList tm input).stk k).length=if k=tm.k₀ then input.length else 0:=by
    by_cases h:k=tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList,h]
  unfold space
  simp only [hlen]
  simp

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_space (tm:Turing.FinTM2) (c c':tm.Cfg) (h:tm.step c=some c'):
    space c'.stk≤ space c.stk + bound tm:=by
  letI:DecidableEq tm.K:=tm.decidableEqK
  change Turing.TM2.step tm.m c=some c' at h
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [Turing.FinTM2.step,Turing.TM2.step] at h
  | some l =>
    change some (Turing.TM2.stepAux (tm.m l) v S)=some c' at h
    have heq:=Option.some.inj h
    rw [← heq]
    exact (stepAux_space (tm.m l) v S).trans (Nat.add_le_add_left (cost_le_bound tm l) _)

 def run (tm:Turing.FinTM2) (start:tm.Cfg):ℕ→ Option tm.Cfg
  | 0 => some start
  | t + 1 => (run tm start t).bind tm.step

 theorem run_space (tm:Turing.FinTM2) (start:tm.Cfg) (t:ℕ) (c:tm.Cfg)
    (h:run tm start t=some c):space c.stk≤ space start.stk + bound tm * t:=by
  induction t generalizing c with
  | zero => simp only [run,Option.some.injEq] at h; subst c; simp
  | succ t ih =>
    cases he:run tm start t with
    | none => simp only [run,he,Option.bind_none,reduceCtorEq] at h
    | some prev =>
      have hstep:tm.step prev=some c:=by simpa only [run,he,Option.bind_some] using h
      have hi:=ih prev he
      have hs:=step_space tm prev c hstep
      rw [Nat.mul_succ]
      omega

 theorem input_run_space (tm:Turing.FinTM2) (input:List (tm.Γ tm.k₀)) (t:ℕ) (c:tm.Cfg)
    (h:run tm (Turing.initList tm input) t=some c):space c.stk≤ input.length + bound tm * t:=by
  simpa only [initial_space] using run_space tm (Turing.initList tm input) t c h

 theorem stack_length_le_space [Fintype K] (S:∀ k,List (Γ k)) (k:K):(S k).length≤ space S:=by
  unfold space
  exact Finset.single_le_sum (f:=fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end EdgeSublinearMWIS.Main.StackSpace

end

section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

noncomputable instance alphabetFintype (P:EdgeSublinearMWIS.Main.Program) (k:P.machine.tm.K):
    Fintype (P.machine.tm.Γ k):= @Fintype.ofFinite _ (P.finiteAlphabet k)

end EdgeSublinearMWIS.Main.StackCompiler

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Phase where | out | into | finish deriving Fintype,DecidableEq
 abbrev SeqK (P Q:Program):=P.machine.tm.K⊕(Q.machine.tm.K⊕Unit)
 abbrev SeqΓ (P Q:Program):SeqK P Q→ Type:=StackSum P.machine.tm.Γ (StackSum Q.machine.tm.Γ (fun _:Unit => Bool))

 abbrev SeqΛ (P Q:Program):=P.machine.tm.Λ⊕(Q.machine.tm.Λ⊕Phase)
 abbrev Seqσ (P Q:Program):=P.machine.tm.σ×(Q.machine.tm.σ×Option Bool)
 def seqInitial (P Q:Program):Seqσ P Q:=(P.machine.tm.initialState,(Q.machine.tm.initialState,none))
 def setCarry {P Q:Program} (v:Seqσ P Q) (b:Option Bool):Seqσ P Q:=(v.1,(v.2.1,b))
 def outLabel {P Q:Program}:SeqΛ P Q:=.inr (.inr .out)
 def intoLabel {P Q:Program}:SeqΛ P Q:=.inr (.inr .into)

 def tempStack {P Q:Program}:SeqK P Q:=.inr (.inr ())

 def seqCode (P Q:Program):SeqΛ P Q→ Stmt (SeqΓ P Q) (SeqΛ P Q) (Seqσ P Q)
   | .inl l => extendStmt (.inr .out) (P.machine.tm.m l)
   | .inr (.inl l) => prefixStmt P.machine.tm.main (extendStmt .finish (Q.machine.tm.m l))
   | .inr (.inr .out) =>
     .peek (.inl P.machine.tm.k₁) (fun v a => setCarry v (a.map P.machine.outputAlphabet))
       (.branch (fun v => v.2.2.isSome)
         (.push tempStack (fun v => v.2.2.getD false)
           (.pop (.inl P.machine.tm.k₁) (fun v _ => setCarry v none) (.goto (fun _ => outLabel))))
         (.load (fun v => setCarry v none) (.goto (fun _ => intoLabel))))
   | .inr (.inr .into) =>
     .pop tempStack (fun v a => setCarry v a)
       (.branch (fun v => v.2.2.isSome)
         (.push (.inr (.inl Q.machine.tm.k₀)) (fun v => Q.machine.inputAlphabet.symm (v.2.2.getD false))
           (.load (fun v => setCarry v none) (.goto (fun _ => intoLabel))))
         (.load (fun v => setCarry v none) (.goto (fun _ => .inr (.inl Q.machine.tm.main)))))
   | .inr (.inr .finish) => .halt

 def seqTM (P Q:Program):Turing.FinTM2 where
   K:=SeqK P Q
   Γ:=SeqΓ P Q
   Λ:=SeqΛ P Q
   σ:=Seqσ P Q
   k₀:=.inl P.machine.tm.k₀
   k₁:=.inr (.inl Q.machine.tm.k₁)
   initialState:=seqInitial P Q
   main:=.inl P.machine.tm.main
   m:=seqCode P Q
 def sequence (P Q:Program):Program where
   machine:= ⟨seqTM P Q,(by change P.machine.tm.Γ P.machine.tm.k₀ ≃ Bool; exact P.machine.inputAlphabet),
     (by change Q.machine.tm.Γ Q.machine.tm.k₁ ≃ Bool; exact Q.machine.outputAlphabet)⟩
   finiteAlphabet k:=by
     cases k with
     | inl k => exact P.finiteAlphabet k
     | inr k => cases k with
       | inl k => exact Q.finiteAlphabet k
       | inr u => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def onlyStack {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L:List (Γ k)):∀j,List (Γ j):=
   Function.update (fun _ => []) k L
 @[simp] theorem onlyStack_self {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L:List (Γ k)):onlyStack k L k=L:=by simp [onlyStack]
 theorem onlyStack_nil {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ):onlyStack k ([]:List (Γ k))=(fun _ => []):=by simp [onlyStack,Function.update_eq_self]
 theorem onlyStack_update {κ:Type} [DecidableEq κ] {Γ:κ→ Type} (k:κ) (L R:List (Γ k)):
     Function.update (onlyStack k L) k R=onlyStack k R:=by simp [onlyStack,Function.update_idem]

 def outStore (P Q:Program) (L acc:List Bool):∀k,List (SeqΓ P Q k):=
   extendStore (onlyStack P.machine.tm.k₁ (L.map P.machine.outputAlphabet.symm))
     (extendStore (fun _ => []) (fun _:Unit => acc))
 def intoStore (P Q:Program) (L acc:List Bool):∀k,List (SeqΓ P Q k):=
   extendStore (fun _ => [])
     (extendStore (onlyStack Q.machine.tm.k₀ (acc.map Q.machine.inputAlphabet.symm)) (fun _:Unit => L))
 def outCfg (P Q:Program) (L acc:List Bool):(seqTM P Q).Cfg:=
   cfg (some outLabel) (seqInitial P Q) (outStore P Q L acc)
 def intoCfg (P Q:Program) (L acc:List Bool):(seqTM P Q).Cfg:=
   cfg (some intoLabel) (seqInitial P Q) (intoStore P Q L acc)

 theorem out_step_cons (P Q:Program) (b:Bool) (L acc:List Bool):
     step (seqCode P Q) (outCfg P Q (b::L) acc)=some (outCfg P Q L (b::acc)):=by
   change step (seqCode P Q) (cfg (some outLabel) (seqInitial P Q) (outStore P Q (b::L) acc))=
     some (cfg (some outLabel) (seqInitial P Q) (outStore P Q L (b::acc)))
   simp only [cfg,step,seqCode,outLabel,stepAux,outStore,seqInitial,setCarry,extendStore_inl,
     List.map_cons,onlyStack_self,List.head?_cons,Option.map_some,Equiv.apply_symm_apply,Option.isSome_some,
     cond_true,Option.getD_some,List.tail_cons,tempStack,extendStore_inr,Function.update_of_ne (by simp:
       (Sum.inl P.machine.tm.k₁:SeqK P Q)≠Sum.inr (Sum.inr ()))]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k =>
     by_cases hk:k=P.machine.tm.k₁
     · subst k
       simp [Function.update,onlyStack,extendStore]
     · simp [Function.update,onlyStack,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [Function.update,onlyStack,extendStore]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def qCfg (P Q:Program) (c:Q.machine.tm.Cfg):(seqTM P Q).Cfg:=
   prefixCfg P.machine.tm.main P.machine.tm.initialState (fun _ => [])
     (extendCfg .finish (none:Option Bool) (fun _:Unit => []) c)
 theorem q_stepAux (P Q:Program) (q:Q.machine.tm.Stmt) (v:Q.machine.tm.σ)
     (S:∀k,List (Q.machine.tm.Γ k)):
     stepAux (prefixStmt P.machine.tm.main (extendStmt .finish q))
       (P.machine.tm.initialState,(v,(none:Option Bool)))
       (prefixStore (extendStore S (fun _:Unit => [])) (fun _ => []))=
         qCfg P Q (stepAux q v S):=by
   rw [stepAux_prefix,stepAux_extend]
   rfl
 theorem q_step (P Q:Program) (c:Q.machine.tm.Cfg) (l:Q.machine.tm.Λ) (hc:c.l=some l):
     step (seqCode P Q) (qCfg P Q c)=(step Q.machine.tm.m c).map (qCfg P Q):=by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [qCfg,prefixCfg,extendCfg,step,seqCode,Option.map_some]
   exact congrArg some (q_stepAux P Q (Q.machine.tm.m l) v S)
 theorem q_run (P Q:Program) (c d:Q.machine.tm.Cfg) (t:ℕ)
     (hr:run Q.machine.tm.m c t=some d):
     run (seqCode P Q) (qCfg P Q c) t=some (qCfg P Q d):=by
   induction t generalizing c with
   | zero => simp only [run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [run_first] at hr ⊢
     cases hc:c.l with
     | none =>
       have hn:step Q.machine.tm.m c=none:=by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs:∃ e,step Q.machine.tm.m c=some e:=by cases c; simp_all [step]
       obtain ⟨e,he⟩:=hs
       rw [q_step P Q c l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

 theorem outputs_run (P:Program) (input output:List Bool) (T:ℕ) (h:Runs P input output T):
     ∃ t,t≤T∧ run P.machine.tm.m (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
       some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)):=by
   obtain ⟨h⟩:=h
   refine ⟨h.steps,h.steps_le_m,?_⟩
   rw [RawStack.run_iter]
   exact h.evals_in_steps

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem out_step_nil (P Q:Program) (acc:List Bool):
     step (seqCode P Q) (outCfg P Q [] acc)=some (intoCfg P Q acc []):=by
   simp [outCfg,intoCfg,cfg,step,seqCode,outLabel,intoLabel,stepAux,outStore,intoStore,seqInitial,setCarry,
     onlyStack_nil,tempStack,extendStore]
 theorem into_step_cons (P Q:Program) (b:Bool) (L acc:List Bool):
     step (seqCode P Q) (intoCfg P Q (b::L) acc)=some (intoCfg P Q L (b::acc)):=by
   simp only [intoCfg,cfg,step,seqCode,intoLabel,stepAux,intoStore,seqInitial,setCarry,tempStack,
     extendStore_inr,extendStore_inl,List.head?_cons,Option.isSome_some,cond_true,Option.getD_some,List.tail_cons]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k => simp [Function.update,onlyStack,extendStore]
   | inr k => cases k with
     | inl k =>
       by_cases hk:k=Q.machine.tm.k₀
       · subst k; simp [Function.update,onlyStack,extendStore]
       · simp [Function.update,onlyStack,extendStore,hk]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

 theorem initList_store (tm:Turing.FinTM2) (L:List (tm.Γ tm.k₀)):
     (Turing.initList tm L).stk=onlyStack tm.k₀ L:=by
   funext k
   by_cases h:k=tm.k₀
   · subst k; simp [Turing.initList,onlyStack]
   · simp [Turing.initList,onlyStack,Function.update,h]
 theorem haltList_store (tm:Turing.FinTM2) (L:List (tm.Γ tm.k₁)):
     (Turing.haltList tm L).stk=onlyStack tm.k₁ L:=by
   funext k
   by_cases h:k=tm.k₁
   · subst k; simp [Turing.haltList,onlyStack]
   · simp [Turing.haltList,onlyStack,Function.update,h]

 theorem into_step_nil (P Q:Program) (acc:List Bool):
     step (seqCode P Q) (intoCfg P Q [] acc)=some (qCfg P Q
       (Turing.initList Q.machine.tm (acc.map Q.machine.inputAlphabet.symm))):=by
   simp only [intoCfg,cfg,step,seqCode,intoLabel,stepAux,intoStore,seqInitial,setCarry,tempStack,
     extendStore_inr,List.head?_nil,Option.isSome_none,cond_false,List.tail_nil]
   congr 1
   simp only [qCfg,prefixCfg,extendCfg,Turing.initList]
   congr 1
   funext k
   cases k with
   | inl k => simp [prefixStore,extendStore,Function.update]
   | inr k => cases k with
     | inl k =>
       by_cases hk:k=Q.machine.tm.k₀
       · subst k; simp [prefixStore,extendStore,Function.update,onlyStack]
       · simp [prefixStore,extendStore,Function.update,onlyStack,hk]
     | inr u => cases u; simp [prefixStore,extendStore,Function.update,onlyStack]

 theorem out_loop (P Q:Program) (L acc:List Bool):
     run (seqCode P Q) (outCfg P Q L acc) (L.length+1)=some (intoCfg P Q (L.reverse++acc) []):=by
   induction L generalizing acc with
   | nil => exact out_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,out_step_cons,Option.bind_some]
     have hh:=ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem into_loop (P Q:Program) (L acc:List Bool):
     run (seqCode P Q) (intoCfg P Q L acc) (L.length+1)=some (qCfg P Q
       (Turing.initList Q.machine.tm ((L.reverse++acc).map Q.machine.inputAlphabet.symm))):=by
   induction L generalizing acc with
   | nil => exact into_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,into_step_cons,Option.bind_some]
     have hh:=ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem cfg_eq {κ Λ σ:Type} {Γ:κ→ Type} {c d:Cfg Γ Λ σ}
     (hl:c.l=d.l) (hv:c.var=d.var) (hs:c.stk=d.stk):c=d:=by
   cases c; cases d; simp_all

 def seqExtra (Q:Program):∀k:Q.machine.tm.K⊕Unit,List (StackSum Q.machine.tm.Γ (fun _:Unit => Bool) k):=
   extendStore (fun _ => []) (fun _ => [])
 theorem p_start (P Q:Program) (input:List Bool):
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none:Option Bool)) (seqExtra Q)
       (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm))=
         Turing.initList (seqTM P Q) (input.map P.machine.inputAlphabet.symm):=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.initList P.machine.tm _).stk (seqExtra Q)=(Turing.initList (seqTM P Q) _).stk
   rw [initList_store,initList_store]
   funext k
   cases k with
   | inl k =>
     by_cases hk:k=P.machine.tm.k₀
     · subst k; simp [onlyStack,Function.update,seqTM,extendStore]
     · simp [onlyStack,Function.update,seqTM,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
     | inr u => cases u; simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
 theorem p_finish (P Q:Program) (output:List Bool):
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none:Option Bool)) (seqExtra Q)
       (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm))=outCfg P Q output []:=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList P.machine.tm _).stk (seqExtra Q)=outStore P Q output []
   rw [haltList_store]
   rfl
 theorem finish_step (P Q:Program) (output:List Bool):
     step (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm)))=
       some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)):=by
   change some (cfg none (seqInitial P Q)
     (prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _:Unit => [])) (fun _ => [])))=some _
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _:Unit => [])) (fun _ => [])=
     (Turing.haltList (seqTM P Q) _).stk
   rw [haltList_store,haltList_store]
   funext k
   cases k with
   | inl k => simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
   | inr k => cases k with
     | inl k =>
       by_cases hk:k=Q.machine.tm.k₁
       · subst k; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
       · simp [prefixStore,extendStore,onlyStack,Function.update,seqTM,hk]
     | inr u => cases u; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]

 theorem sequence_runs (P Q:Program) (input middle output:List Bool) (T U:ℕ)
     (hP:Runs P input middle T) (hQ:Runs Q middle output U):
     Runs (sequence P Q) input output (T+U+2*middle.length+3):=by
   obtain ⟨t,ht,hp⟩:=outputs_run P input middle T hP
   obtain ⟨u,hu,hq⟩:=outputs_run Q middle output U hQ
   have h1:=run_extend (.inr Phase.out) P.machine.tm.m (seqCode P Q) (fun _ => rfl)
     _ _ (Q.machine.tm.initialState,(none:Option Bool)) (seqExtra Q) t hp
   rw [p_start,p_finish] at h1
   have h2:=out_loop P Q middle []
   simp only [List.append_nil] at h2
   have h3:=into_loop P Q middle.reverse []
   simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h3
   have h4:=q_run P Q _ _ u hq
   have h5:run (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm))) 1=
     some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)):=finish_step P Q output
   have hr:=run_trans _ _ _ _ _ _ h1 h2
   have hr:=run_trans _ _ _ _ _ _ hr h3
   have hr:=run_trans _ _ _ _ _ _ hr h4
   have hr:=run_trans _ _ _ _ _ _ hr h5
   have he:=RawStack.outputs (tm:=seqTM P Q) (input.map P.machine.inputAlphabet.symm)
     (output.map Q.machine.outputAlphabet.symm) _ hr
   obtain ⟨he⟩:=he
   refine ⟨{he with steps_le_m:=he.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem spaceRun_eq (tm:Turing.FinTM2) (c:tm.Cfg) (t:ℕ):
     StackSpace.run tm c t=RawStack.run tm.m c t:=by
   induction t with
   | zero => rfl
   | succ t ih => simp only [StackSpace.run,RawStack.run,ih]; rfl
 theorem output_length (P:Program) (input output:List Bool) (T:ℕ) (h:Runs P input output T):
     output.length≤ input.length+StackSpace.bound P.machine.tm*T:=by
   obtain ⟨t,ht,hr⟩:=outputs_run P input output T h
   have hr':StackSpace.run P.machine.tm (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
     some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)):=by rw [spaceRun_eq]; exact hr
   have hs:=StackSpace.input_run_space P.machine.tm (input.map P.machine.inputAlphabet.symm) t _ hr'
   have hl:=StackSpace.stack_length_le_space (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)).stk P.machine.tm.k₁
   simp only [haltList_store,onlyStack_self,List.length_map] at hl
   rw [haltList_store] at hs
   simp only [List.length_map] at hs
   have hmul:=Nat.mul_le_mul_left (StackSpace.bound P.machine.tm) ht
   omega

 theorem sequence_runs_linear (P Q:Program):
     ∃ K:ℕ,0<K∧ ∀ (input middle output:List Bool) (T U:ℕ),
       Runs P input middle T→ Runs Q middle output U→
       Runs (sequence P Q) input output (K*(T+U+input.length+1)):=by
   refine ⟨2*StackSpace.bound P.machine.tm+4,by omega,?_⟩
   intro input middle output T U hP hQ
   obtain ⟨hr⟩:=sequence_runs P Q input middle output T U hP hQ
   refine ⟨{hr with steps_le_m:=hr.steps_le_m.trans ?_}⟩
   have hl:=output_length P input middle T hP
   nlinarith

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax455465Proofs Lax759944.BinaryWordEncoding

 theorem bitSize_zero_padding (xs:List ℕ) (T:ℕ):
    bitSize (xs++List.replicate T 0)=bitSize xs+T:=by
  rw [WordSize.bitSize_append]
  congr 1
  induction T with
  | zero => rfl
  | succ T ih => simp [List.replicate_succ,WordSize.bitSize_cons,ih,Nat.add_comm]

 theorem padded_bit_program:∃ q:ℕ,0<q∧ ∀ c:Com,
    ∃ (E:Program) (K:ℕ),0<K∧ ∀ (xs ys:List ℕ) (t v padding:ℕ),
      (∃ ext τ,Run (2^v) c (initEnv ext xs) τ t∧ τ.out=ys)→
      (∀ a∈ys,a≤1)→
      v+RamTransfer.layoutAllowance (RamAutomaticLayout.layout (paddedCommand c))≤ padding→
      Runs E (wordBits (xs++List.replicate padding 0)) (wordBits ys)
        (K*(bitSize xs+padding+t+1)^q):=by
  obtain ⟨q,hq,hSim⟩:=uniform_bit_simulation
  refine ⟨q,hq,?_⟩
  intro c
  obtain ⟨E,W,K,hK,hW,hE⟩:=hSim (paddedProgram c)
  let L:=RamAutomaticLayout.layout (paddedCommand c)
  let A:=4*L.const+1
  refine ⟨E,K*(A+1)^q,by positivity,?_⟩
  intro xs ys t v padding hSource hOutput hPadding
  let padded:=xs++List.replicate padding 0
  let b:=bitSize padded
  have hb:padding≤ b:=by dsimp [b,padded]; rw [bitSize_zero_padding]; omega
  have hv:v≤ b+1:=by omega
  have hw:b+1+RamTransfer.layoutAllowance L≤ W.eval b:=by
    have hw:=hW b
    change v+RamTransfer.layoutAllowance L≤ padding at hPadding
    omega
  obtain ⟨s,hs,hRAM⟩:=padded_program_run hSource padding (W.eval b) hv hw
  have hFits:Lax759944.RamPolytime.FitsInWords (2*b+1) ((padded.length::padded)++ys):=by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · rcases List.mem_cons.mp ha with rfl|ha
      · have hlen:=WordSize.length_le padded
        have hx:b<2^(2*b+1):=by
          exact (by omega:b≤ 2*b+1).trans_lt Nat.lt_two_pow_self
        exact hlen.trans_lt hx
      · exact (WordSize.member_bound padded a ha).trans_le
          (Nat.pow_le_pow_right (by decide) (by omega:b≤ 2*b+1))
    · have ha:=hOutput a ha
      have hp:1<2^(2*b+1):=Nat.one_lt_pow (by omega) (by decide)
      omega
  obtain ⟨hRun⟩:=hE padded ys s hFits hRAM
  refine ⟨{hRun with steps_le_m:=hRun.steps_le_m.trans ?_}⟩
  have hs':s≤ A*(t+1):=by
    dsimp [A]
    change s≤ (4*L.const+1)*(t+1)
    change s≤ L.const*(t+3)+1 at hs
    nlinarith
  have hbase:b+s+1≤ (A+1)*(b+t+1):=by nlinarith
  have hp:=Nat.mul_le_mul_left K (Nat.pow_le_pow_left hbase q)
  rw [mul_pow] at hp
  have he:K*((A+1)^q*(b+t+1)^q)=(K*(A+1)^q)*(bitSize xs+padding+t+1)^q:=by
    dsimp [b,padded]
    rw [bitSize_zero_padding]
    ring
  exact hp.trans_eq he

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main TreewidthApprox.Pushed
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.GraphHelpers

 theorem comp_mem {n:ℕ} (G:SimpleGraph (Fin n)) (X:Finset (Fin n)) (u v:Fin n):
    v∈ avoidComp G X u↔ AvoidReach G X u v:=by
  classical
  simp [avoidComp]

end EdgeSublinearMWIS.Main.GraphHelpers

end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EdgeCounting

 theorem edgeCount_eq {n:ℕ} (G:SimpleGraph (Fin n)):edgeCount G=G.edgeSet.ncard:=by
  classical
  rw [edgeCount,Set.ncard_eq_toFinset_card']
  change ((Finset.univ:Finset (Fin n × Fin n)).filter
    (fun e => e.1 < e.2∧ G.Adj e.1 e.2)).card=G.edgeFinset.card
  apply Finset.card_bij (fun e he => s(e.1,e.2))
  · intro e he
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using (Finset.mem_filter.mp he).2.2
  · intro e he f hf hEq
    have he':=(Finset.mem_filter.mp he).2.1
    have hf':=(Finset.mem_filter.mp hf).2.1
    rcases Sym2.eq_iff.mp hEq with hEq | hEq
    · exact Prod.ext hEq.1 hEq.2
    · have h1:=congrArg Fin.val hEq.1
      have h2:=congrArg Fin.val hEq.2
      have heV:=he'
      have hfV:=hf'
      simp only [Fin.lt_def] at heV hfV
      omega
  · intro e he
    induction e using Sym2.inductionOn with
    | hf u v =>
      have hadj:G.Adj u v:=by simpa using he
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
      · exact ⟨(u,v),by simp [h,hadj],rfl⟩
      · exact ⟨(v,u),by simp [h,hadj.symm],Sym2.eq_swap⟩

end EdgeSublinearMWIS.Main.EdgeCounting

end

section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main
open EdgeSublinearMWIS.Main.EdgeCounting
open RobertsonSeymour1986.GM5
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BlowupDecomposition

def attachLeaves {α β:Type} (T:SimpleGraph α) (root:α):SimpleGraph (α ⊕ β) where
  Adj
    | .inl a, .inl b => T.Adj a b
    | .inl a, .inr _ => a=root
    | .inr _, .inl b => b=root
    | .inr _, .inr _ => False
  symm:= ⟨by intro a b h; cases a <;> cases b <;> simp_all [T.adj_comm]⟩
  loopless:= ⟨by intro a; cases a <;> simp⟩

 theorem degree_as_sum {V:Type} [Fintype V] (G:SimpleGraph V)
    [DecidableRel G.Adj] (v:V):
    G.degree v=∑ u,if G.Adj v u then 1 else 0:=by
  classical
  rw [SimpleGraph.degree,G.neighborFinset_eq_filter]
  simp

 theorem attachLeaves_tree {α β:Type} [Fintype α] [Fintype β]
    (T:SimpleGraph α) (root:α) (hT:T.IsTree):(attachLeaves (β:=β) T root).IsTree:=by
  classical
  let H:=attachLeaves (β:=β) T root
  let inclusion:T→g H:= ⟨Sum.inl,fun h => h⟩
  have hroot:∀ a:α ⊕ β,H.Reachable a (.inl root):=by
    intro a
    cases a with
    | inl a => exact (hT.connected a root).map inclusion
    | inr b => exact SimpleGraph.Adj.reachable (show H.Adj (.inr b) (.inl root) from rfl)
  have:Nonempty (α ⊕ β):= ⟨.inl root⟩
  have hconn:H.Connected:= ⟨fun a b => (hroot a).trans (hroot b).symm⟩
  have hleft (a:α):H.degree (.inl a)=T.degree a + if a=root then Fintype.card β else 0:=by
    rw [degree_as_sum,Fintype.sum_sum_type,degree_as_sum]
    simp only [H,attachLeaves]
    split_ifs <;> simp_all
  have hright (b:β):H.degree (.inr b)=1:=by
    rw [degree_as_sum,Fintype.sum_sum_type]
    simp [H,attachLeaves,eq_comm]
  have hsum:(∑ v,H.degree v)=(∑ a,T.degree a) + 2 * Fintype.card β:=by
    rw [Fintype.sum_sum_type]
    simp_rw [hleft,hright]
    simp [Finset.sum_add_distrib]
    omega
  change H.IsTree
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hconn, ?_⟩
  have hcount:=hT.card_edgeFinset
  have hhand:=H.sum_degrees_eq_twice_card_edges
  rw [hsum,T.sum_degrees_eq_twice_card_edges] at hhand
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_sum,
    ← SimpleGraph.edgeFinset_card]
  omega

 noncomputable def highDegree {m:ℕ} (H:SimpleGraph (Fin m)) (s:ℕ):Finset (Fin m):=by
  classical
  exact Finset.univ.filter (fun v => s < H.degree v)

 noncomputable def active {m:ℕ} (H:SimpleGraph (Fin m)) (s:ℕ):Finset (Fin m):=by
  classical
  exact Finset.univ.filter (fun v => v∉ highDegree H s∧ ∃ u,u∉ highDegree H s∧ H.Adj v u)

 theorem active_fiber_bound {n m:ℕ} (G:SimpleGraph (Fin n)) (H:SimpleGraph (Fin m))
    (f:Fin m→ Fin n) (hAdj:∀ u v,H.Adj u v↔ G.Adj (f u) (f v)) (s:ℕ) (v:Fin n):
    ((active H s).filter (fun u => f u=v)).card≤ s:=by
  classical
  by_cases hne:((active H s).filter (fun u => f u=v)).Nonempty
  · obtain ⟨u,hu⟩:=hne
    have huv:f u=v:=(Finset.mem_filter.mp hu).2
    obtain ⟨huS,w,hwS,huw⟩:=(Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
    have hdeg:H.degree w≤ s:=by simpa [highDegree] using hwS
    apply le_trans ?_ hdeg
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro z hz
    have hzv:f z=v:=(Finset.mem_filter.mp hz).2
    apply (SimpleGraph.mem_neighborFinset H w z).mpr
    apply (hAdj w z).mpr
    simpa only [hzv, ← huv] using (hAdj w u).mp huw.symm
  · simp [Finset.not_nonempty_iff_eq_empty.mp hne]

 theorem transfer_bound {n m:ℕ} (G:SimpleGraph (Fin n)) (H:SimpleGraph (Fin m))
    (f:Fin m→ Fin n) (hAdj:∀ u v,H.Adj u v↔ G.Adj (f u) (f v))
    {T:Type} [Fintype T] (tree:SimpleGraph T) (bags:T→ Finset (Fin n))
    (dec:IsTreeDecomposition G tree bags) (w s:ℕ) (hsize:∀ t, (bags t).card≤ w + 1):
    ∃ (newTree:SimpleGraph (T ⊕ Fin m)) (newBags:T ⊕ Fin m→ Finset (Fin m)),
      IsTreeDecomposition H newTree newBags∧
      ∀ t, (newBags t).card≤ (highDegree H s).card + max 1 (s * (w + 1)):=by
  classical
  let S:=highDegree H s
  let A:=active H s
  let root:T:=Classical.choice dec.1.connected.nonempty
  let newTree:=attachLeaves (β:=Fin m) tree root
  have htree:newTree.IsTree:=attachLeaves_tree tree root dec.1
  let newBags:T ⊕ Fin m→ Finset (Fin m):=fun t =>
    S ∪ match t with
    | .inl t => A.filter (fun v => f v∈ bags t)
    | .inr v => if v∈ A then ∅ else {v}
  have mem_old (t:T) (v:Fin m):v∈ newBags (.inl t)↔ v∈ S∨ v∈ A∧ f v∈ bags t:=by
    simp [newBags]
  have mem_leaf (u v:Fin m):v∈ newBags (.inr u)↔ v∈ S∨ v=u∧ v∉ A:=by
    by_cases hu:u∈ A <;> simp [newBags,hu] <;> aesop
  have active_notS {v:Fin m} (hv:v∈ A):v∉ S:=(Finset.mem_filter.mp hv).2.1
  have hcover (v:Fin m):∃ t,v∈ newBags t:=by
    by_cases hvS:v∈ S
    · exact ⟨.inl root, (mem_old root v).mpr (Or.inl hvS)⟩
    · by_cases hvA:v∈ A
      · obtain ⟨t,ht⟩:=dec.2.1 (f v)
        exact ⟨.inl t, (mem_old t v).mpr (Or.inr ⟨hvA,ht⟩)⟩
      · exact ⟨.inr v, (mem_leaf v v).mpr (Or.inr ⟨rfl,hvA⟩)⟩
  refine ⟨newTree,newBags, ⟨htree,hcover, ?_, ?_⟩, ?_⟩
  · intro u v huv
    by_cases huS:u∈ S
    · obtain ⟨t,ht⟩:=hcover v
      exact ⟨t,Finset.mem_union_left _ huS,ht⟩
    · by_cases hvS:v∈ S
      · obtain ⟨t,ht⟩:=hcover u
        exact ⟨t,ht,Finset.mem_union_left _ hvS⟩
      · have huA:u∈ A:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,huS,v,hvS,huv⟩
        have hvA:v∈ A:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvS,u,huS,huv.symm⟩
        obtain ⟨t,hut,hvt⟩:=dec.2.2.1 (f u) (f v) ((hAdj u v).mp huv)
        exact ⟨.inl t, (mem_old t u).mpr (Or.inr ⟨huA,hut⟩), (mem_old t v).mpr (Or.inr ⟨hvA,hvt⟩)⟩
  · intro a b c p hp hm v hv
    by_cases hvS:v∈ S
    · exact Finset.mem_union_left _ hvS
    · have hva:=(Finset.mem_inter.mp hv).1
      have hvc:=(Finset.mem_inter.mp hv).2
      by_cases hvA:v∈ A
      · have old_node (t:T ⊕ Fin m) (ht:v∈ newBags t):∃ i:T,t=.inl i∧ f v∈ bags i:=by
          cases t with
          | inl i => exact ⟨i,rfl, ((mem_old i v).mp ht).resolve_left hvS |>.2⟩
          | inr u => have hh:=((mem_leaf u v).mp ht).resolve_left hvS; exact False.elim (hh.2 hvA)
        obtain ⟨a0,rfl,hfa⟩:=old_node a hva
        obtain ⟨c0,rfl,hfc⟩:=old_node c hvc
        obtain ⟨q,hq⟩:=dec.1.connected.exists_isPath a0 c0
        let incl:tree→g newTree:= ⟨Sum.inl,fun h => h⟩
        have hqmap:(q.map incl).IsPath:=hq.map Sum.inl_injective
        let:=htree.isAcyclic.subsingleton_path (.inl a0) (.inl c0)
        have heq:p=q.map incl:=congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩:newTree.Path (.inl a0) (.inl c0)) ⟨q.map incl,hqmap⟩)
        rw [heq,SimpleGraph.Walk.support_map] at hm
        obtain ⟨b0,hb0,rfl⟩:=List.mem_map.mp hm
        apply (mem_old b0 v).mpr
        exact Or.inr ⟨hvA,dec.2.2.2 a0 b0 c0 q hq hb0 (Finset.mem_inter.mpr ⟨hfa,hfc⟩)⟩
      · have leaf_node (t:T ⊕ Fin m) (ht:v∈ newBags t):t=.inr v:=by
          cases t with
          | inl i => have hh:=((mem_old i v).mp ht).resolve_left hvS; exact False.elim (hvA hh.1)
          | inr u => have hh:=((mem_leaf u v).mp ht).resolve_left hvS; exact congrArg Sum.inr hh.1.symm
        have ha:=leaf_node a hva
        have hc:=leaf_node c hvc
        subst a
        subst c
        let:=htree.isAcyclic.subsingleton_path (.inr v) (.inr v)
        have heq:p=.nil:=congrArg Subtype.val (Subsingleton.elim (⟨p,hp⟩:newTree.Path (.inr v) (.inr v)) ⟨.nil,SimpleGraph.Walk.IsPath.nil⟩)
        rw [heq] at hm
        have hb:b=.inr v:=by simpa using hm
        subst b
        exact hva
  · intro t
    cases t with
    | inl i =>
      have hc:(A.filter (fun v => f v∈ bags i)).card≤ s * (w + 1):=by
        rw [← Finset.sum_card_fiberwise_eq_card_filter]
        calc
          _≤ ∑ _v∈ bags i,s:=Finset.sum_le_sum (fun v hv => active_fiber_bound G H f hAdj s v)
          _=(bags i).card * s:=by simp
          _≤ (w + 1) * s:=Nat.mul_le_mul_right _ (hsize i)
          _=s * (w + 1):=Nat.mul_comm _ _
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_right _ _)) _)
    | inr v =>
      have hc:(if v∈ A then (∅:Finset (Fin m)) else {v}).card≤ 1:=by split_ifs <;> simp
      exact (Finset.card_union_le S _).trans (Nat.add_le_add_left (hc.trans (le_max_left _ _)) _)

 theorem treewidth_witness {n:ℕ} (G:SimpleGraph (Fin n)):TreewidthLE G (PlantedSubgraphLD.tw G):=by
  have hne:{w:ℕ | TreewidthLE G w}.Nonempty:=by
    refine ⟨n,PUnit,inferInstance, ⊥, (fun _ => Finset.univ), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩
      · exact ⟨SimpleGraph.Connected.of_subsingleton,by simp⟩
      · intro v; exact ⟨PUnit.unit,Finset.mem_univ _⟩
      · intro u v h; exact ⟨PUnit.unit,Finset.mem_univ _,Finset.mem_univ _⟩
      · intro s s' s'' p hp hm; exact Finset.subset_univ _
    · intro s; simp
  exact Nat.sInf_mem hne

 theorem treewidth_zero {m:ℕ} (H:SimpleGraph (Fin m)) (hz:edgeCount H=0):
    PlantedSubgraphLD.tw H=0:=by
  have hH:H=⊥:=by
    apply SimpleGraph.edgeFinset_eq_empty.mp
    apply Finset.card_eq_zero.mp
    have hh:=hz
    rw [edgeCount_eq] at hh
    simpa only [SimpleGraph.edgeFinset_card,Set.fintypeCard_eq_ncard] using hh
  have hS:highDegree H 0=∅:=by simp [highDegree,hH]
  obtain ⟨T,inst,tree,bags,dec,size⟩:=treewidth_witness H
  let:=inst
  obtain ⟨tr,bs,hd,hsize⟩:=transfer_bound H H id (fun _ _ => Iff.rfl) tree bags dec (PlantedSubgraphLD.tw H) 0 size
  have hw:TreewidthLE H 0:=by
    refine ⟨T ⊕ Fin m,inferInstance,tr,bs,hd, ?_⟩
    intro t
    simpa [hS] using hsize t
  have ht:PlantedSubgraphLD.tw H≤ 0:=Nat.sInf_le hw
  omega

end EdgeSublinearMWIS.Main.BlowupDecomposition

end

section

namespace EdgeSublinearMWIS.Main.RamBridge
open Lax263307.GraphClasses Lax263307.EdgeSublinearSeparators
open TreewidthApprox.Pushed

 theorem hereditary {C:EdgeSublinearMWIS.Main.GraphClass} (hC:Hereditary C):
    IsHereditary C:=by
  rintro m n H G hG ⟨f⟩
  exact hC G H f.toEmbedding hG (fun _ _ => f.map_rel_iff.symm)

 theorem balanced {n:ℕ} {G:SimpleGraph (Fin n)} {S:Finset (Fin n)}
    (h:Balanced G Finset.univ S):IsBalancedSeparator G S:=by
  classical
  intro K
  obtain ⟨u,hu⟩:=K.nonempty_supp
  let D:=avoidComp G S u.val
  have hD:D∈ components G Finset.univ S:=by
    simp only [components,Finset.sdiff_self,Finset.union_empty]
    exact Finset.mem_image.mpr ⟨u.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,u.property⟩,rfl⟩
  have hsub:Subtype.val '' K.supp ⊆ (D:Set (Fin n)):=by
    rintro v ⟨v,hv,rfl⟩
    have heq:(G.induce (↑S:Set (Fin n))ᶜ).connectedComponentMk u =
        (G.induce (↑S:Set (Fin n))ᶜ).connectedComponentMk v:=hu.trans hv.symm
    obtain ⟨p⟩:=SimpleGraph.ConnectedComponent.eq.mp heq
    apply (GraphHelpers.comp_mem G S u.val v.val).mpr
    refine ⟨p.map (⟨Subtype.val,fun h => h⟩:G.induce (↑S:Set (Fin n))ᶜ→g G),?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
    obtain ⟨x,hx,rfl⟩:=hz
    exact x.property
  have hcard:K.supp.ncard≤ D.card:=by
    have hc:=Set.ncard_le_ncard hsub
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at hc
    simpa using hc
  have hb:=h.2 D hD
  simp only [Finset.card_univ,Fintype.card_fin] at hb
  omega

 theorem separators {C:EdgeSublinearMWIS.Main.GraphClass} (hC:StronglyEdgeSublinear C):
    HasStronglyEdgeSublinearSeparators C:=by
  classical
  obtain ⟨b,c,hb,hb1,hc,h⟩:=hC.2
  refine ⟨b,c+1,hb,hb1,by positivity,?_⟩
  intro n G hG
  by_cases hz:edgeCount G=0
  · obtain ⟨S,hS,hsize⟩:=treewidth_separator G Finset.univ
    rw [BlowupDecomposition.treewidth_zero G hz] at hsize
    refine ⟨S,balanced hS,?_⟩
    have hzero:G.edgeSet.ncard=0:=by simpa only [EdgeCounting.edgeCount_eq] using hz
    norm_num [hzero]
    have hs:(S.card:ℝ)≤ 1:=by exact_mod_cast hsize
    linarith
  · obtain ⟨S,hS,hsize⟩:=h n G hG (by omega)
    refine ⟨S,balanced hS,hsize.trans ?_⟩
    rw [EdgeCounting.edgeCount_eq]
    have hr:=Real.rpow_le_rpow (by positivity:(0:ℝ)≤ (G.edgeSet.ncard:ℝ))
      (by linarith:(G.edgeSet.ncard:ℝ)≤ (G.edgeSet.ncard:ℝ)+1) hb
    calc
      _≤ c * ((G.edgeSet.ncard:ℝ)+1)^b:=mul_le_mul_of_nonneg_left hr hc.le
      _≤ _:=mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)

end EdgeSublinearMWIS.Main.RamBridge

end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedHelpers

 theorem weightedAlpha_attained {n:ℕ} (G:SimpleGraph (Fin n)) (W:Finset (Fin n))
    (w:Fin n→ ℚ):∃ I ⊆ W,G.IsIndepSet (I:Set (Fin n))∧
      weightedAlphaOn G W w=∑ v∈ I, (w v:ℝ):=by
  classical
  let S:= {z:ℝ | ∃ I ⊆ W,G.IsIndepSet (I:Set (Fin n))∧ z=∑ v∈ I, (w v:ℝ)}
  have hne:S.Nonempty:=by
    refine ⟨0, ∅,Finset.empty_subset _, ?_,by simp⟩
    simp
  have hfin:S.Finite:=by
    apply (Set.finite_range (fun I:Finset (Fin n) => ∑ v∈ I, (w v:ℝ))).subset
    rintro z ⟨I,hI,hi,rfl⟩
    exact Set.mem_range_self _
  exact hne.csSup_mem hfin

end EdgeSublinearMWIS.Main.WeightedHelpers

end

section

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_le_twice_exponent (L n:ℕ) (hn:n≤ 2 ^ L):depth n≤ 2 * L:=by
  induction L generalizing n with
  | zero =>
    have:n≤ 1:=by simpa using hn
    simp [depth,this]
  | succ L ih =>
    by_cases hn₁:n≤ 1
    · simp [depth,hn₁]
    · rw [depth.eq_def n,if_neg hn₁]
      by_cases ha:2 * n / 3≤ 1
      · rw [depth.eq_def (2 * n / 3),if_pos ha]
        omega
      · rw [depth.eq_def (2 * n / 3),if_neg ha]
        have hb:2 * (2 * n / 3) / 3≤ 2 ^ L:=by
          rw [pow_succ] at hn
          omega
        have:=ih _ hb
        omega

theorem logarithmic_bound (n:ℕ):depth n≤ 2 * (Nat.log2 n + 1):=by
  apply depth_le_twice_exponent
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

end Lax263307Proofs.RecursionDepth

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

end

section

namespace Lax263307Proofs.RoundingBounds

open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

theorem le_maximum {n:ℕ} (w:Fin n→ ℚ) (v:Fin n):w v≤ maximumWeight w:=by
  exact (insert 0 (Finset.univ.image w)).le_max' (w v) (by simp)

theorem scale_positive {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ)
    (hn:0 < n) (hε:0 < ε) (hW:0 < maximumWeight w):0 < scale w ε:=by
  have hnQ:(0:ℚ) < n:=by exact_mod_cast hn
  exact div_pos (mul_pos hε hW) (mul_pos (by norm_num) hnQ)

theorem total_copy_bound {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ)
    (nonnegative:∀ v,0≤ w v) (positive_order:0 < n)
    (positive_accuracy:0 < ε) (positive_maximum:0 < maximumWeight w):
    ((∑ v,copies w ε v:ℕ):ℚ)≤ 2 * (n:ℚ) ^ 2 / ε:=by
  have hτ:=scale_positive w ε positive_order positive_accuracy positive_maximum
  have hn:(n:ℚ) ≠ 0:=by exact_mod_cast ne_of_gt positive_order
  have hW:maximumWeight w ≠ 0:=ne_of_gt positive_maximum
  have hε:ε ≠ 0:=ne_of_gt positive_accuracy
  calc
    ((∑ v,copies w ε v:ℕ):ℚ)=∑ v, (copies w ε v:ℚ):=by norm_cast
    _≤ ∑ v,w v / scale w ε:=Finset.sum_le_sum fun v _ =>
      Nat.floor_le (div_nonneg (nonnegative v) hτ.le)
    _≤ ∑ _v:Fin n,maximumWeight w / scale w ε:=
      Finset.sum_le_sum fun v _ => div_le_div_of_nonneg_right (le_maximum w v) hτ.le
    _=(n:ℚ) * maximumWeight w / scale w ε:=by simp; ring
    _=2 * (n:ℚ) ^ 2 / ε:=by unfold scale; field_simp

end Lax263307Proofs.RoundingBounds

end

section

open scoped BigOperators

namespace Lax109476.LinearProgram

def IsFeasible {m n:ℕ} (P:Program ℝ m n):Prop:=
  ∃ x,PrimalFeasible P x

end Lax109476.LinearProgram

end

section

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def toReal {m n:ℕ} (P:Program ℚ m n):Program ℝ m n where
  A i j:=P.A i j
  b i:=P.b i
  c j:=P.c j

def realVector {n:ℕ} (x:Fin n→ ℚ):Fin n→ ℝ:=fun j => x j

end Lax109476.RationalCertificates

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

open Lax808846.Ram

def runOut (w:ℕ):ℕ→ Program→ State→ ℕ→ Option (List ℕ × ℕ)
  | 0,p,s,k => if s.pc < p.length then none else some (s.out,k)
  | fuel + 1,p,s,k =>
      if s.pc < p.length then
        match step w p s with
        | none => some (s.out,k + 1)
        | some s' => runOut w fuel p s' (k + 1)
      else some (s.out,k)

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

variable {B n i j k v:ℕ} {a b x y m:String} {g F:ℕ→ ℕ} {σ:Env}

def Fill (a x:String) (n i:ℕ) (g F:ℕ→ ℕ) (σ:Env):Prop:=
  σ.arrs a=arrOf n g∧ σ.vars x=i∧ i≤ n∧ ∀ j,j < i→ g j=F j

namespace Fill

namespace Demo

def demo (a x m:String):Com:=
  .seq (.assign x (.lit 0)) (.while (.lt (.var x) (.var m)) (put a x (.var x)))

def demoWatched (a x m:String):Com:=
  .seq (.assign m (.lit 3))
    (.seq (demo a x m)
      (.seq (.write (.get a (.lit 0)))
        (.seq (.write (.get a (.lit 1))) (.write (.get a (.lit 2))))))

def layout:Lax808846Proofs.Compile.Layout:= ⟨["i", "m"], ["ar"],2⟩

def prog:Lax808846.Ram.Program:=
  Lax808846Proofs.Compile.compileProgram layout (demoWatched "ar" "i" "m")

def demoRun:Option (List ℕ × ℕ):=runOut 16 1000 prog (Lax808846.Ram.initState []) 0

end Demo

end Fill

end Lax808846Proofs.Reasoning.Lib

end

section

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

def Correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ):
    Outcome n→ Prop
  | .near y => PrimalFeasible (toReal P) (realVector y)∧
      ∀ j, |(y j:ℝ) - (center j:ℝ)|≤ (ρ:ℝ)
  | .far a α => (∑ j, |(a j:ℝ)|)≤ 1∧
      (∀ y,PrimalFeasible (toReal P) y→ (∑ j, (a j:ℝ) * y j)≤ (α:ℝ))∧
      (ρ:ℝ) < (∑ j, (a j:ℝ) * (center j:ℝ)) - (α:ℝ)
  | .reject => ¬ IsFeasible (toReal P)

end Lax263307.RationalProjection

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem value_mono (coefficients:List ℕ) {x y:ℕ} (h:x≤ y):
    value coefficients x≤ value coefficients y:=by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem exists_coefficients (p:Polynomial ℕ):∃ coefficients:List ℕ,
    ∀ x:ℕ,value coefficients x=p.eval x:=by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[],fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a)::rest, ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    refine ⟨0::coefficients, ?_⟩
    intro x
    simp only [value,Nat.zero_add,hcoeff,Polynomial.eval_mul,Polynomial.eval_X,Nat.mul_comm]

end Lax455465Proofs.RamPolynomial

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

end

section

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem accuracy_budget (n:ℕ) (ε:ℚ) (hε:0 < ε):
    4≤ accuracyDenominator n ε∧
      (Lax263307.RecursionDepth.depth n:ℚ) * (4 / accuracyDenominator n ε)≤ ε:=by
  let E:= ⌈ε⁻¹⌉₊
  let d:=Lax263307.RecursionDepth.depth n
  have hE:0 < E:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hEq:(0:ℚ) < E:=Nat.cast_pos.mpr hE
  have hdq:(0:ℚ) < (d+1:ℕ):=Nat.cast_pos.mpr (by omega)
  have hD:4≤ accuracyDenominator n ε:=by
    change 4≤ 4 * (d+1) * E
    nlinarith only [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hE)]
  refine ⟨hD, ?_⟩
  have hceil:ε⁻¹≤ (E:ℚ):=Nat.le_ceil _
  have hprod:1≤ ε * (E:ℚ):=by
    have hh:=mul_le_mul_of_nonneg_left hceil hε.le
    simpa only [mul_inv_cancel₀ hε.ne'] using hh
  have hdiv:1 / (E:ℚ)≤ ε:=(div_le_iff₀ hEq).mpr (by nlinarith only [hprod])
  apply le_trans _ hdiv
  change (d:ℚ) * (4 / (4 * (d+1) * E:ℕ))≤ 1 / (E:ℚ)
  push_cast
  apply (le_div_iff₀ hEq).mpr
  have hd:(0:ℚ) < (d:ℚ)+1:=by positivity
  field_simp
  ring_nf
  linarith

end Lax263307Proofs.RecursiveAlgorithm

end

section

set_option maxHeartbeats 1000000

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

def child {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (S:Finset (Fin n)) (t:ℕ):Option (Finset (Fin n)):=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))

end Lax263307Proofs.NativeRecursiveOracle

end

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

def emit:Com:=.seq (.assign "emit.count" (.var "input.n"))
  (Lax455465Proofs.RamEmitWords.command "copy.counts" 1)

def command:Com:=.seq prepare emit

open Lax109476Proofs

end Lax263307Proofs.NativeWeightReduction

end

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

theorem mask_test_bit {n:ℕ} (I:Finset (Fin n)) (j:ℕ):
    (mask I).testBit j=decide (j∈I.image Fin.val):=by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I)↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    mask (insert v I)=Nat.lor (mask I) (2^v.val):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j=((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he:j=v.val <;> by_cases hm:j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n:ℕ} (I:Finset (Fin n)) (i:ℕ):Finset (Fin n):=
  I.filter fun v => v.val < i

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

end Lax263307Proofs.NativeMasks

end

section

set_option maxHeartbeats 2000000

namespace Lax263307Proofs.ParameterResources

open Lax263307.AlgorithmParameters Lax263307.ParameterResources

theorem logarithm_mono (n:ℕ):Nat.log2 n + 1≤ logarithm n:=by
  unfold logarithm
  rw [Nat.log2_eq_log_two,Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1

end Lax263307Proofs.ParameterResources

end

section

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target index cursor count:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars count=xs.length
  counter:σ.vars index≤ xs.length
  position:σ.vars cursor=front.length+σ.vars index
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars index)) target σ

end Lax263307Proofs.NativeAppendBuffer

end

section

namespace Lax263307Proofs.NativeDistanceData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection

structure Data {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (σ:Env):Prop where
  source:Prefix (encodeProgram P) "lp.input" σ
  center:Prefix (encodeVector x) "projection.center" σ
  oldRows:σ.vars "projection.m"=m
  oldColumns:σ.vars "projection.n"=n
  rowCount:σ.vars "lp.rows"=rows m n
  columnCount:σ.vars "lp.columns"=columns n
  matrixLength:σ.vars "projection.matrixLength"=rows m n*columns n

end Lax263307Proofs.NativeDistanceData

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

end Lax263307Proofs.NativeShoreMasks

end

section

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem eval_mono (P:Polynomial ℕ) {x y:ℕ} (h:x≤ y):P.eval x≤ P.eval y:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources

end

section

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command:Com:=.ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))

end Lax263307Proofs.NativeChildReturn

end

section

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars "stack.copy.length"=xs.length
  index:σ.vars "stack.i"≤ xs.length
  position:σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars "stack.i")) target σ

end Lax263307Proofs.NativeBlockAppend

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

end Lax263307Proofs.NativeOracleContext

end

section

namespace Lax263307Proofs.NativeRecursionBudget

open Lax263307 AlgorithmParameters

theorem work_le_pow (localCost branches R fuel:ℕ) (hl:localCost≤ R) (hb:branches≤ R):
    work localCost branches fuel≤(R+1)^(fuel+1):=by
  induction fuel with
  | zero => simpa only [work,Nat.zero_add,pow_one] using hl.trans (Nat.le_succ R)
  | succ fuel ih =>
    have hp:R≤(R+1)^(fuel+1):=(Nat.le_succ R).trans (le_self_pow (by omega) (by omega))
    calc
      work localCost branches (fuel+1)≤ R+R*(R+1)^(fuel+1):=
        Nat.add_le_add hl (Nat.mul_le_mul hb ih)
      _≤(R+1)^(fuel+1)*(R+1):=by nlinarith only [hp]
      _=(R+1)^((fuel+1)+1):=(pow_succ _ _).symm

theorem amplify (C d n D localCost branches:ℕ) (hD:0< D)
    (hl:localCost≤2^(C*(D*logarithm n)^d))
    (hb:branches≤2^(C*(D*logarithm n)^d)):
    work localCost branches (RecursionDepth.depth n)≤
      2^(3*(C+1)*(D*logarithm n)^(d+1)):=by
  let X:=D*logarithm n
  have hlog:1≤ logarithm n:=by dsimp [logarithm]; omega
  have hX:1≤ X:=by dsimp [X]; nlinarith only [hlog,hD]
  have hLX:logarithm n≤ X:=Nat.le_mul_of_pos_left _ hD
  have hd:RecursionDepth.depth n+1≤3*X:=by
    have hdepth:=Lax263307Proofs.RecursionDepth.logarithmic_bound n
    have hmono:=ParameterResources.logarithm_mono n
    omega
  have hxpow:1≤ X^d:=Nat.one_le_pow _ _ hX
  have he:C*X^d+1≤(C+1)*X^d:=by nlinarith only [hxpow]
  have hp:2^(C*X^d)+1≤2^(C*X^d+1):=by
    have hpos:1≤2^(C*X^d):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  calc
    work localCost branches (RecursionDepth.depth n)≤(2^(C*X^d)+1)^(RecursionDepth.depth n+1):=
      work_le_pow _ _ _ _ hl hb
    _≤(2^(C*X^d+1))^(RecursionDepth.depth n+1):=Nat.pow_le_pow_left hp _
    _=2^((C*X^d+1)*(RecursionDepth.depth n+1)):=(pow_mul _ _ _).symm
    _≤2^(((C+1)*X^d)*(3*X)):=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul he hd)
    _=2^(3*(C+1)*(D*logarithm n)^(d+1)):=by rw [pow_succ]; dsimp only [X]; congr 1; ring

end Lax263307Proofs.NativeRecursionBudget

end

section

namespace Lax263307Proofs.NativeRootResource

open Lax263307 AlgorithmParameters

theorem budget_bound (Q e C d n D:ℕ) (hD:0< D):
    budget Q e C d n D≤ envelope (Q+e*(C+1)) d n D:=by
  let X:=D*logarithm n
  have hX:1≤ X:=by
    have hp:0< X:=by dsimp [X,logarithm]; positivity
    omega
  have hpow:1≤ X^d:=Nat.one_le_pow _ _ hX
  have hp:2^(C*X^d)+1≤2^(C*X^d+1):=by
    have hh:1≤2^(C*X^d):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  calc
    budget Q e C d n D≤2^Q*(2^(C*X^d+1))^e:=
      Nat.mul_le_mul (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left hp e)
    _=2^(Q+(C*X^d+1)*e):=by rw [←pow_mul,←pow_add]
    _≤ envelope (Q+e*(C+1)) d n D:=by
      apply Nat.pow_le_pow_right (by decide)
      change Q+(C*X^d+1)*e≤(Q+e*(C+1))*X^d
      nlinarith only [hpow,Nat.mul_le_mul_left Q hpow,Nat.mul_le_mul_left e hpow]

theorem recursive_bound (Q e C d n D localCost branches:ℕ) (hD:0< D)
    (hl:localCost≤ budget Q e C d n D) (hb:branches≤ budget Q e C d n D):
    NativeRecursionBudget.work localCost branches (RecursionDepth.depth n)≤
      envelope (3*(Q+e*(C+1)+1)) (d+1) n D:=
  NativeRecursionBudget.amplify (Q+e*(C+1)) d n D localCost branches hD
    (hl.trans (budget_bound Q e C d n D hD)) (hb.trans (budget_bound Q e C d n D hD))

end Lax263307Proofs.NativeRootResource

end

section

namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 1000000

theorem value_bound (cs:List ℕ) (x:ℕ):RamPolynomial.value cs x≤ cs.sum*(x+1)^cs.length:=by
  induction cs with
  | nil => simp [RamPolynomial.value]
  | cons c cs ih =>
    have hp:1≤(x+1)^cs.length:=Nat.one_le_pow _ _ (by omega)
    have hc:c≤ c*(x+1)^cs.length:=Nat.le_mul_of_pos_right _ hp
    have hi:=Nat.mul_le_mul_left x ih
    simp only [RamPolynomial.value,List.sum_cons,List.length_cons]
    calc
      c+x*RamPolynomial.value cs x≤ c+x*(cs.sum*(x+1)^cs.length):=Nat.add_le_add_left hi _
      _≤ c*(x+1)^cs.length+x*(cs.sum*(x+1)^cs.length):=Nat.add_le_add_right hc _
      _≤(c+cs.sum)*(x+1)^cs.length*(x+1):=by ring_nf; omega
      _=_:=by ring

theorem exists_majorant (P:Polynomial ℕ):
    ∃ Q e:ℕ,0< Q∧ 0< e∧ ∀ R,P.eval R≤ Q*(R+1)^e:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  refine ⟨cs.sum+1,cs.length+1,by omega,by omega,?_⟩
  intro R
  rw [←hcs]
  exact (value_bound cs R).trans (Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_right (by omega) (by omega)))

end Lax263307Proofs.NativePolynomialBudget

end

section

namespace Lax263307Proofs.NativePolynomialEnvelope

def Bounded (f:ℕ→ ℕ):Prop:= ∃ P:Polynomial ℕ,∀ R,f R≤ P.eval R

theorem identity:Bounded (fun R => R):= ⟨Polynomial.X,by simp⟩
theorem constant (n:ℕ):Bounded (fun _ => n):= ⟨Polynomial.C n,by simp⟩

theorem add {f g:ℕ→ ℕ} (hf:Bounded f) (hg:Bounded g):Bounded (fun R => f R+g R):=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,hQ⟩:=hg
  exact ⟨P+Q,fun R => by simpa only [Polynomial.eval_add] using Nat.add_le_add (hP R) (hQ R)⟩

theorem mul {f g:ℕ→ ℕ} (hf:Bounded f) (hg:Bounded g):Bounded (fun R => f R*g R):=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,hQ⟩:=hg
  exact ⟨P*Q,fun R => by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul (hP R) (hQ R)⟩

theorem pow {f:ℕ→ ℕ} (k:ℕ) (hf:Bounded f):Bounded (fun R => f R^k):=by
  obtain ⟨P,hP⟩:=hf
  exact ⟨P^k,fun R => by simpa only [Polynomial.eval_pow] using Nat.pow_le_pow_left (hP R) k⟩

theorem eval (P:Polynomial ℕ) {f:ℕ→ ℕ} (hf:Bounded f):Bounded (fun R => P.eval (f R)):=by
  obtain ⟨Q,hQ⟩:=hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

theorem of_le {f g:ℕ→ ℕ} (hf:Bounded f) (h:∀ R,g R≤ f R):Bounded g:=by
  obtain ⟨P,hP⟩:=hf
  exact ⟨P,fun R => (h R).trans (hP R)⟩

theorem monomial {f:ℕ→ ℕ} (hf:Bounded f):
    ∃ Q e:ℕ,0< Q∧ 0< e∧ ∀ R,f R≤ Q*(R+1)^e:=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,e,hQ,he,hbound⟩:=NativePolynomialBudget.exists_majorant P
  exact ⟨Q,e,hQ,he,fun R => (hP R).trans (hbound R)⟩

end Lax263307Proofs.NativePolynomialEnvelope
end

section

set_option maxHeartbeats 1500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeLocalTime

open Lax263307 AlgorithmParameters NativeCoreMachine NativeSelectedRounds NativePolynomialEnvelope

theorem polynomial:∀ (cfg:Lax263307Proofs.NativeCoreMachine.Config),
  Lax263307Proofs.NativePolynomialEnvelope.Bounded fun (W:ℕ) =>
    Lax263307Proofs.NativeLocalTime.steps W + Lax263307Proofs.NativeLocalTime.branches W +
      Lax263307Proofs.NativeLocalTime.time cfg W (2 * (W + 1)):=
fun (cfg:Lax263307Proofs.NativeCoreMachine.Config) =>
  id
    (Lax263307Proofs.NativePolynomialEnvelope.add
      (Lax263307Proofs.NativePolynomialEnvelope.add
        (Lax263307Proofs.NativePolynomialEnvelope.add (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
          (Lax263307Proofs.NativePolynomialEnvelope.mul
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 5)
                (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
                  (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
              (Lax263307Proofs.NativePolynomialEnvelope.constant 7))
            Lax263307Proofs.NativePolynomialEnvelope.identity))
        (Lax263307Proofs.NativePolynomialEnvelope.mul
          (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
            (Lax263307Proofs.NativePolynomialEnvelope.constant 1))
          Lax263307Proofs.NativePolynomialEnvelope.identity))
      (Lax263307Proofs.NativePolynomialEnvelope.add
        (Lax263307Proofs.NativePolynomialEnvelope.add
          (Lax263307Proofs.NativePolynomialEnvelope.add
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 36)
                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                  (Lax263307Proofs.NativePolynomialEnvelope.constant (12 * (4 * cfg.a + 2))))
                (Lax263307Proofs.NativePolynomialEnvelope.constant 88))
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 36)
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                                (Lax263307Proofs.NativePolynomialEnvelope.constant (12 * (4 * cfg.a + 2))))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 76))
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 54)
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            Lax263307Proofs.NativePolynomialEnvelope.identity
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 3)))
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 69)
                                              Lax263307Proofs.NativePolynomialEnvelope.identity)
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 33))
                                          Lax263307Proofs.NativePolynomialEnvelope.identity))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 41))
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 3)))
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 8))
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 38)
                                          Lax263307Proofs.NativePolynomialEnvelope.identity)
                                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 42)
                                        Lax263307Proofs.NativePolynomialEnvelope.identity))
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 60))
                                  Lax263307Proofs.NativePolynomialEnvelope.identity))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 18)))
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 22)
                                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 129))
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                  Lax263307Proofs.NativePolynomialEnvelope.identity))
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 57)
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)))
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 111)))
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)))
                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    Lax263307Proofs.NativePolynomialEnvelope.identity
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                Lax263307Proofs.NativePolynomialEnvelope.identity)))))
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 12)
                        Lax263307Proofs.NativePolynomialEnvelope.identity))
                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 105)
                      (Lax263307Proofs.NativePolynomialEnvelope.mul Lax263307Proofs.NativePolynomialEnvelope.identity
                        Lax263307Proofs.NativePolynomialEnvelope.identity)))
                  (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 91)
                    Lax263307Proofs.NativePolynomialEnvelope.identity))
                (Lax263307Proofs.NativePolynomialEnvelope.constant 108)))
            (Lax263307Proofs.NativePolynomialEnvelope.constant 2))
          (Lax263307Proofs.NativePolynomialEnvelope.mul
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            Lax263307Proofs.NativePolynomialEnvelope.identity
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                        Lax263307Proofs.NativePolynomialEnvelope.identity)))
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          Lax263307Proofs.NativePolynomialEnvelope.identity
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            Lax263307Proofs.NativePolynomialEnvelope.identity
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 4))))
                                      Lax263307Proofs.NativePolynomialEnvelope.identity))))
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 36)
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 100)
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          Lax263307Proofs.NativePolynomialEnvelope.identity
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 124))
                                Lax263307Proofs.NativePolynomialEnvelope.identity))
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 135))
                          Lax263307Proofs.NativePolynomialEnvelope.identity)
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2))
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 14))
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 193)
                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 48)))
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 48)
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2000)
                                  (Lax263307Proofs.NativePolynomialEnvelope.pow 6
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 4)
                                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 20)))))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 14))
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 10))
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 17)
                                      Lax263307Proofs.NativePolynomialEnvelope.identity)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 72)
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                          Lax263307Proofs.NativePolynomialEnvelope.identity)
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 270))
                                Lax263307Proofs.NativePolynomialEnvelope.identity)
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 17)
                                Lax263307Proofs.NativePolynomialEnvelope.identity))
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 67)))
                        (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 10)))
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 43)
                                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 37))
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 36)
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1))
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 258))
                                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 72)))
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 8))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant
                                        (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length))
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant
                                      (7 * (Lax263307Proofs.NativeCoreMachine.frameScalars cfg).length)))
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 52)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      Lax263307Proofs.NativePolynomialEnvelope.identity)))
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 36)))
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          Lax263307Proofs.NativePolynomialEnvelope.identity
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 16))
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant
                                    (Lax263307Proofs.NativeCoreMachine.frameArrays cfg).length))
                                (Lax263307Proofs.NativePolynomialEnvelope.constant
                                  (7 * (Lax263307Proofs.NativeCoreMachine.frameScalars cfg).length)))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 12)))
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 45)
                                Lax263307Proofs.NativePolynomialEnvelope.identity)
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 38))
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 28)
                                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 104))
                                Lax263307Proofs.NativePolynomialEnvelope.identity)
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 30))))
                        (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 10)))
                (Lax263307Proofs.NativePolynomialEnvelope.constant 6))
              Lax263307Proofs.NativePolynomialEnvelope.identity)
            Lax263307Proofs.NativePolynomialEnvelope.identity))
        (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 300)
          (Lax263307Proofs.NativePolynomialEnvelope.pow 3
            (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
              (Lax263307Proofs.NativePolynomialEnvelope.constant 2))))))

end Lax263307Proofs.NativeLocalTime

end

section

namespace Lax263307Proofs.NativeInputBounds

open Lax263307.IndependentSetEncoding

open Lax263307 WeightedIndependentSet

theorem parameter_length {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):
    (encodeParameters w ε).length=3*n+3:=by
  simp [encodeParameters,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]

theorem order_le_bits {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):n≤ rationalBitSize w ε:=by
  have h:=Lax455465Proofs.WordSize.length_le (encodeParameters w ε)
  rw [parameter_length] at h
  change 3*n+3≤ rationalBitSize w ε at h
  omega

end Lax263307Proofs.NativeInputBounds

end

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasPositive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace

theorem positive_parameters {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ) (hN:0< order weights ε):
    0< n∧ 0< WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
  have hn:0< n:=by
    by_contra hn
    have hz:n=0:=by omega
    subst n
    simpa [order] using hN
  refine ⟨hn,?_⟩
  by_contra hmax
  have hmax:WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights)≤ 0:=le_of_not_gt hmax
  have hz (v:Fin n):PositiveWeights.positiveWeights weights v=0:=by
    have hle:PositiveWeights.positiveWeights weights v≤ WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
      apply Finset.le_max'; simp
    exact le_antisymm (hle.trans hmax) (le_max_right _ _)
  have hc (v:Fin n):copies weights ε v=0:=by
    simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,hz v]
  have he:order weights ε=0:=by simp only [order,hc,Finset.sum_const_zero]
  omega

end Lax263307Proofs.NativeQptasPositive

end

section

namespace Lax263307Proofs.NativeFinalBounds

open Lax263307 AlgorithmParameters RecursiveAlgorithm

def inputLog (n:ℕ):ℕ:=Nat.log2 (n+2)+1

theorem half_accuracy (ε:ℚ) (hε:0<ε):⌈(ε/2)⁻¹⌉₊≤2*⌈ε⁻¹⌉₊:=by
  apply Nat.ceil_le.mpr
  have hc:=Nat.le_ceil ε⁻¹
  have he:(ε/2)⁻¹=2*ε⁻¹:=by field_simp
  rw [he]
  push_cast
  linarith

theorem copy_order {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ)
    (hw:∀ v,0≤ weights v) (hn:0< n) (hε:0<ε)
    (hmax:0< WeightRounding.maximumWeight weights):
    ∑ v,WeightRounding.copies weights ε v≤2*n^2*⌈ε⁻¹⌉₊:=by
  have h:=Lax263307Proofs.RoundingBounds.total_copy_bound weights ε hw hn hε hmax
  have hc:=Nat.le_ceil ε⁻¹
  have he:(2*(n:ℚ)^2)/ε=2*(n:ℚ)^2*ε⁻¹:=by ring
  rw [he] at h
  have hc':=mul_le_mul_of_nonneg_left hc (show (0:ℚ)≤2*(n:ℚ)^2 by positivity)
  have ht:=h.trans hc'
  exact_mod_cast ht

theorem blowup_log (n N E:ℕ) (hE:0< E) (hN:N≤2*n^2*E):logarithm N≤6*(E*inputLog n):=by
  let L:=inputLog n
  have hL:1≤ L:=by dsimp [L,inputLog]; omega
  have hn:n≤2^L:=by
    have hh:n+2<2^L:=Nat.lt_pow_of_log_lt (by decide) (by
      change Nat.log 2 (n+2)< Nat.log2 (n+2)+1
      rw [Nat.log2_eq_log_two]; omega)
    omega
  have he:E≤2^E:=Nat.lt_two_pow_self.le
  have hp:2*N≤2^(2+2*L+E):=by
    calc
      2*N≤4*(n^2*E):=by nlinarith only [hN]
      _≤4*((2^L)^2*2^E):=Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hn 2) he)
      _=_:=by rw [←pow_mul,←pow_add]; norm_num; congr 1; ring
  have ht:2*N<2^(3+2*L+E):=by
    have hx:0<2^(2+2*L+E):=Nat.two_pow_pos _
    have heq:3+2*L+E=(2+2*L+E)+1:=by omega
    rw [heq,pow_succ]
    omega
  have hl:Nat.log 2 (2*N)<3+2*L+E:=Nat.log_lt_of_lt_pow' (by omega:3+2*L+E≠0) ht
  have hlog:logarithm N≤3+2*L+E:=by
    unfold logarithm
    rw [Nat.log2_eq_log_two]
    omega
  have heL:E≤ E*L:=Nat.le_mul_of_pos_right _ hL
  have hLe:L≤ E*L:=Nat.le_mul_of_pos_left _ hE
  have hpos:1≤ E*L:=Nat.mul_pos hE (by omega)
  exact hlog.trans (by nlinarith only [heL,hLe,hpos])

theorem denominator_bound (N:ℕ) (ε:ℚ) (hε:0<ε):
    accuracyDenominator N (ε/2)≤24*⌈ε⁻¹⌉₊*logarithm N:=by
  have hc:=half_accuracy ε hε
  have hd:=Lax263307Proofs.RecursionDepth.logarithmic_bound N
  have hl:=ParameterResources.logarithm_mono N
  have hp:1≤ logarithm N:=by unfold logarithm; omega
  have hdepth:RecursionDepth.depth N+1≤3*logarithm N:=by omega
  unfold accuracyDenominator
  have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left 4 hdepth) hc
  convert hh using 1 <;> ring

theorem weighted_envelope (C d n N:ℕ) (ε:ℚ) (hε:0<ε)
    (hN:N≤2*n^2*⌈ε⁻¹⌉₊):
    NativeRootResource.envelope C d N (accuracyDenominator N (ε/2))≤
      2^((C*864^d)*(⌈ε⁻¹⌉₊*inputLog n)^(3*d)):=by
  let E:= ⌈ε⁻¹⌉₊
  let L:=inputLog n
  let X:=E*L
  have hE:0< E:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hL:1≤ L:=by dsimp [L,inputLog]; omega
  have hl:=blowup_log n N E hE hN
  have hd:=denominator_bound N ε hε
  have hbase:accuracyDenominator N (ε/2)*logarithm N≤864*X^3:=by
    have h1:=Nat.mul_le_mul_right (logarithm N) hd
    have h2:=Nat.pow_le_pow_left hl 2
    have h3:E^3*L^2≤ X^3:=by
      dsimp [X]
      rw [mul_pow]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))
    calc
      _≤24*E*(logarithm N)^2:=by nlinarith only [h1]
      _≤24*E*(6*(E*L))^2:=Nat.mul_le_mul_left _ h2
      _=864*(E^3*L^2):=by ring
      _≤864*X^3:=Nat.mul_le_mul_left _ h3
  apply Nat.pow_le_pow_right (by decide)
  have hh:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase d)
  convert hh using 1 <;> rw [mul_pow] <;> simp only [pow_mul] <;> ring

end Lax263307Proofs.NativeFinalBounds

end

section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax263307Proofs NativeQptasImplementation
open Lax263307.IndependentSetEncoding
open Lax759944.BinaryWordEncoding

 theorem approximation_weightedAlpha {n:ℕ} {G:SimpleGraph (Fin n)} {w:Fin n→ ℚ}
    {ε:ℚ} {I:Finset (Fin n)} (h:Lax263307.WeightedIndependentSet.IsApproximation G w ε I):
    G.IsIndepSet (I:Set (Fin n))∧
      (1-(ε:ℝ))*weightedAlpha G w≤ ∑ v∈I,(w v:ℝ):=by
  obtain ⟨J,hJ,hind,hopt⟩:=WeightedHelpers.weightedAlpha_attained G Finset.univ w
  refine ⟨h.1,?_⟩
  change (1-(ε:ℝ))*weightedAlphaOn G Finset.univ w≤ _
  rw [hopt]
  have hh:=h.2 J hind
  dsimp only [Lax263307.WeightedIndependentSet.weight] at hh
  exact_mod_cast hh

 theorem native_weighted_binary_program:∃ q:ℕ,0<q∧
    ∀ C:EdgeSublinearMWIS.Main.GraphClass,StronglyEdgeSublinear C→
      ∃ (i:Fixed C) (E:Program) (K:ℕ),0<K∧
        ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
          (w:Fin n→ ℚ) (ε:ℚ),C n G→ 0<ε→ ε<1→
          ∀ padding:ℕ,
            NativeQptasWordBounds.width i w ε+
              Lax455465Proofs.RamTransfer.layoutAllowance
                (Lax455465Proofs.RamAutomaticLayout.layout (paddedCommand (NativeWeightedExecution.command i)))≤ padding→
            ∃ I:Finset (Fin n),G.IsIndepSet (I:Set (Fin n))∧
              (1-(ε:ℝ))*weightedAlpha G w≤ ∑ v∈I,(w v:ℝ)∧
              Runs E (wordBits (encodeInput G w ε++List.replicate padding 0))
                (wordBits (encodeOutput I))
                (K*(bitSize (encodeInput G w ε)+padding+NativeWeightedExecution.cost i w ε+1)^q):=by
  obtain ⟨q,hq,hcompile⟩:=padded_bit_program
  refine ⟨q,hq,?_⟩
  intro C hC
  obtain ⟨i⟩:=NativeQptasImplementation.exists_fixed C (hereditary hC.1) (separators hC)
  obtain ⟨E,K,hK,hE⟩:=hcompile (NativeWeightedExecution.command i)
  refine ⟨i,E,K,hK,?_⟩
  intro n G inst w ε hG hε hε1 padding hPadding
  obtain ⟨I,ext,hI,hSpec⟩:=NativeWeightedExecution.command_spec i G hG w ε hε hε1
  obtain ⟨τ,hRun,hout⟩:=hSpec _ rfl
  have hBoolean:∀ a∈encodeOutput I,a≤1:=by
    intro a ha
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp ha
    split_ifs <;> omega
  have hExec:=hE (encodeInput G w ε) (encodeOutput I) (NativeWeightedExecution.cost i w ε)
    (NativeQptasWordBounds.width i w ε) padding ⟨ext,τ,hRun,hout⟩ hBoolean hPadding
  have hAns:=approximation_weightedAlpha hI
  exact ⟨I,hAns.1,hAns.2,hExec⟩

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def value:List Bool→ ℕ
   | [] => 0
   | b::L => b.toNat+2*value L
 def increment:List Bool→ List Bool
   | [] => [true]
   | false::L => true::L
   | true::L => false::increment L

 theorem increment_value (L:List Bool):value (increment L)=value L+1:=by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [increment,value,ih] <;> omega

end EdgeSublinearMWIS.Main.RawStack

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open RawStack
abbrev State:=List Bool × (List Bool × (Bool × List Bool))
 def step (s:State):State:=
   let a:=s.1.headD false
   let b:=s.2.1.headD false
   let c:=s.2.2.1
   (s.1.tail,(s.2.1.tail,((a && b)||(a && c)||(b && c),(xor (xor a b) c)::s.2.2.2)))
 def word (A B:List Bool):List Bool:=
   ((step^[A.length+B.length+1]) (A,(B,(false,[])))).2.2.2.reverse

 theorem value_head_tail (A:List Bool):value A=(A.headD false).toNat+2*value A.tail:=by
   cases A <;> rfl

 theorem value_append (A B:List Bool):value (A++B)=value A+2^A.length*value B:=by
   induction A with
   | nil => simp [value]
   | cons a A ih => simp [value,ih,pow_succ]; ring

 theorem full_adder (a b c:Bool):
    (xor (xor a b) c).toNat+2*((a && b)||(a && c)||(b && c)).toNat=a.toNat+b.toNat+c.toNat:=by
   cases a <;> cases b <;> cases c <;> decide

 theorem step_value (s:State):
    value (step s).2.2.2.reverse+2^(step s).2.2.2.length*(value (step s).1+value (step s).2.1+(step s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat):=by
   rcases s with ⟨A,B,c,R⟩
   have ha:=value_head_tail A
   have hb:=value_head_tail B
   have hf:=full_adder (A.headD false) (B.headD false) c
   simp only [step,List.reverse_cons,value_append,List.length_reverse,List.length_cons,pow_succ,value,List.length_nil,Nat.mul_zero,Nat.add_zero]
   rw [ha,hb]
   have hfm:=congrArg (fun z:ℕ => 2^R.length*z) hf
   nlinarith only [hfm]

 theorem iter_value (s:State) (t:ℕ):
    value ((step^[t]) s).2.2.2.reverse+2^((step^[t]) s).2.2.2.length*(value ((step^[t]) s).1+value ((step^[t]) s).2.1+((step^[t]) s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat):=by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_value ((step^[t]) s)).trans ih

 theorem iter_lists (s:State) (t:ℕ):
    ((step^[t]) s).1=s.1.drop t∧ ((step^[t]) s).2.1=s.2.1.drop t∧
      ((step^[t]) s).2.2.2.length=s.2.2.2.length+t:=by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     constructor
     · exact List.tail_drop
     · constructor
       · exact List.tail_drop
       · omega

 theorem word_value (A B:List Bool):value (word A B)=value A+value B:=by
   let t:=A.length+B.length
   let s:State:=(A,(B,(false,[])))
   have hlist:=iter_lists s t
   have hA:((step^[t]) s).1=[]:=by rw [hlist.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hB:((step^[t]) s).2.1=[]:=by rw [hlist.2.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hzero:((step^[t+1]) s).1=[]∧ ((step^[t+1]) s).2.1=[]∧ ((step^[t+1]) s).2.2.1=false:=by
     rw [Function.iterate_succ_apply']
     simp [step,hA,hB]
   have hi:=iter_value s (t+1)
   rw [hzero.1,hzero.2.1,hzero.2.2] at hi
   simpa only [word,s,t,value,List.reverse_nil,Bool.toNat_false,Nat.add_zero,Nat.mul_zero,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add] using hi

 theorem word_length (A B:List Bool):(word A B).length=A.length+B.length+1:=by
   have hh:=(iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [word,List.length_reverse,List.length_nil,Nat.zero_add] using hh

end EdgeSublinearMWIS.Main.BinaryAdder

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def trim:List Bool→ List Bool
   | [] => []
   | b::L => let T:=trim L
             if T=[] then if b then [true] else [] else b::T

 theorem trim_value (L:List Bool):value (trim L)=value L:=by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT:trim L=[]
     · have hv:value L=0:=by rw [← ih,hT]; rfl
       cases b <;> simp [trim,hT,value,hv]
     · simp only [trim,hT,if_false,value,ih]

 theorem trim_length (L:List Bool):(trim L).length≤L.length:=by
   induction L with
   | nil => simp [trim]
   | cons b L ih =>
     by_cases hT:trim L=[]
     · cases b <;> simp [trim,hT]
     · simp [trim,hT]; omega

 theorem value_lt (L:List Bool):value L<2^L.length:=by
   induction L with
   | nil => simp [value]
   | cons b L ih => cases b <;> simp [value,pow_succ] <;> omega

 theorem trim_lower (L:List Bool) (hL:trim L≠[]):2^((trim L).length-1)≤value (trim L):=by
   induction L with
   | nil => exact False.elim (hL rfl)
   | cons b L ih =>
     by_cases hT:trim L=[]
     · cases b <;> simp_all [trim,value]
     · have hh:=ih hT
       have hlen:0<(trim L).length:=by
         cases he:trim L with
         | nil => exact False.elim (hT he)
         | cons a T => simp
       have hp:2^((trim L).length)=2*2^((trim L).length-1):=by
         rw [← Nat.pow_succ']
         congr 1
         omega
       simp only [trim,hT,if_false,List.length_cons,Nat.add_sub_cancel,value]
       rw [hp]
       omega

 theorem trim_length_of_lt (L:List Bool) (B:ℕ) (hB:value L<2^B):(trim L).length≤B:=by
   by_cases hL:trim L=[]
   · simp [hL]
   · have hp:=trim_lower L hL
     rw [trim_value] at hp
     have hh:(trim L).length-1<B:=by
       by_contra hn
       have hpow:=Nat.pow_le_pow_right (by omega:1≤2) (by omega:B≤(trim L).length-1)
       omega
     omega

 def trimStep (x:Bool×List Bool):List Bool:=
   if x.2=[] then if x.1 then [true] else [] else x.1::x.2

 theorem trim_fold (L:List Bool):L.reverse.foldl (fun T b => trimStep (b,T)) []=trim L:=by
   induction L with
   | nil => rfl
   | cons b L ih =>
     rw [List.reverse_cons,List.foldl_append]
     change trimStep (b,L.reverse.foldl (fun T b => trimStep (b,T)) [])=trim (b::L)
     rw [ih]
     rfl

 theorem trim_idem (L:List Bool):trim (trim L)=trim L:=by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT:trim L=[]
     · cases b <;> simp [trim,hT]
     · simp only [trim,hT,if_false,ih]

end EdgeSublinearMWIS.Main.RawStack

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinarySubtract
open RawStack
abbrev State:=BinaryAdder.State
 def step (s:State):State:=
   let a:=s.1.headD false
   let b:=s.2.1.headD false
   let c:=s.2.2.1
   (s.1.tail,(s.2.1.tail,((!a && (b || c)) || (b && c),(xor (xor a b) c)::s.2.2.2)))
 def raw (A B:List Bool):Bool×List Bool:=
   let s:=(step^[A.length+B.length+1]) (A,(B,(false,[])))
   (s.2.2.1,s.2.2.2.reverse)
 def difference (A B:List Bool):List Bool:=if (raw A B).1 then [] else trim (raw A B).2
 def less (A B:List Bool):Bool:=(raw A B).1

 theorem bit_balance (a b c:Bool):
     a.toNat+2*((!a && (b || c)) || (b && c)).toNat=b.toNat+c.toNat+(xor (xor a b) c).toNat:=by
   cases a <;> cases b <;> cases c <;> decide

 def potential (s:State):ℤ:=
   (value s.2.2.2.reverse:ℤ)+(2:ℤ)^s.2.2.2.length*((value s.1:ℤ)-(value s.2.1:ℤ)-s.2.2.1.toNat)

 theorem step_potential (s:State):potential (step s)=potential s:=by
   rcases s with ⟨A,B,c,R⟩
   have ha:=BinaryAdder.value_head_tail A
   have hb:=BinaryAdder.value_head_tail B
   have hf:=bit_balance (A.headD false) (B.headD false) c
   have haZ:(value A:ℤ)=(A.headD false).toNat+2*(value A.tail:ℤ):=by exact_mod_cast ha
   have hbZ:(value B:ℤ)=(B.headD false).toNat+2*(value B.tail:ℤ):=by exact_mod_cast hb
   have hfZ:((A.headD false).toNat:ℤ)+2*((!A.headD false && (B.headD false || c)) || (B.headD false && c)).toNat=
       (B.headD false).toNat+c.toNat+(xor (xor (A.headD false) (B.headD false)) c).toNat:=by exact_mod_cast hf
   simp only [potential,step,List.reverse_cons,BinaryAdder.value_append,List.length_reverse,List.length_cons,pow_succ,value,Nat.mul_zero,Nat.add_zero]
   push_cast
   rw [haZ,hbZ]
   have hh:=congrArg (fun z:ℤ => (2:ℤ)^R.length*z) hfZ
   nlinarith only [hh]

 theorem iter_potential (s:State) (t:ℕ):potential (step^[t] s)=potential s:=by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_potential _).trans ih

 theorem iter_lists (s:State) (t:ℕ):
     (step^[t] s).1=s.1.drop t∧ (step^[t] s).2.1=s.2.1.drop t∧
       (step^[t] s).2.2.2.length=s.2.2.2.length+t:=by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     exact ⟨List.tail_drop,List.tail_drop,by omega⟩

 theorem raw_balance (A B:List Bool):value A+2^(A.length+B.length+1)*(raw A B).1.toNat=value B+value (raw A B).2:=by
   let n:=A.length+B.length+1
   let s:State:=(A,(B,(false,[])))
   let t:=step^[n] s
   have hh:=iter_potential s n
   have hl:=iter_lists s n
   have hA:t.1=[]:=by rw [hl.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hB:t.2.1=[]:=by rw [hl.2.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hlen:t.2.2.2.length=n:=by simpa only [s,List.length_nil,Nat.zero_add] using hl.2.2
   change potential t=potential s at hh
   dsimp only [potential] at hh
   rw [hA,hB,hlen] at hh
   dsimp only [s] at hh
   simp only [value,List.reverse_nil,List.length_nil,pow_zero,Bool.toNat_false,Int.ofNat_zero,zero_sub,mul_one] at hh
   have heq:(value A:ℤ)+(2:ℤ)^n*(t.2.2.1.toNat:ℤ)=(value B:ℤ)+(value t.2.2.2.reverse:ℤ):=by linarith only [hh]
   exact_mod_cast heq

 theorem raw_length (A B:List Bool):(raw A B).2.length=A.length+B.length+1:=by
   have hh:=(iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [raw,List.length_reverse,List.length_nil,Nat.zero_add] using hh

 theorem less_iff (A B:List Bool):less A B=true↔ value A<value B:=by
   have hb:=raw_balance A B
   have hl:=value_lt (raw A B).2
   rw [raw_length] at hl
   unfold less
   cases h:(raw A B).1 <;> simp only [h,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hb ⊢ <;> simp only [Bool.false_eq_true,false_iff,true_iff] <;> omega

 theorem difference_value (A B:List Bool):value (difference A B)=value A-value B:=by
   unfold difference
   by_cases h:(raw A B).1=true
   · rw [if_pos h]
     have hh:=(less_iff A B).mp h
     simp [value,Nat.sub_eq_zero_of_le hh.le]
   · have hb:=raw_balance A B
     have hf:(raw A B).1=false:=Bool.eq_false_iff.mpr h
     rw [hf,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hb
     rw [if_neg h,trim_value]
     omega

 theorem difference_canonical (A B:List Bool):trim (difference A B)=difference A B:=by
   unfold difference
   split_ifs
   · rfl
   · exact trim_idem _

 theorem difference_length (A B:List Bool):(difference A B).length≤A.length:=by
   rw [← difference_canonical A B]
   apply trim_length_of_lt
   rw [difference_value]
   exact (Nat.sub_le _ _).trans_lt (value_lt A)

end EdgeSublinearMWIS.Main.BinarySubtract

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def multiplyStep (x:Bool×(List Bool×List Bool)):List Bool×List Bool:=
   (false::x.2.1,if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2)
 def multiply (A B:List Bool):List Bool:=
   trim (B.foldl (fun s b => multiplyStep (b,s)) (A,[])).2

 theorem multiply_fold_value (A B S:List Bool):
     value (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=value S+value A*value B:=by
   induction B generalizing A S with
   | nil => simp [value]
   | cons b B ih =>
     rw [List.foldl_cons]
     change value (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).2=_
     rw [ih]
     cases b <;> simp only [Bool.false_eq_true,if_false,if_true,trim_value,BinaryAdder.word_value,value,Bool.toNat_false,Bool.toNat_true] <;> ring

 theorem multiply_value (A B:List Bool):value (multiply A B)=value A*value B:=by
   rw [multiply,trim_value,multiply_fold_value]
   simp [value]

 theorem product_lt (A B:List Bool):value A*value B<2^(A.length+B.length):=by
   calc
     _≤ value A*2^B.length:=Nat.mul_le_mul_left _ (value_lt B).le
     _ < 2^A.length*2^B.length:=Nat.mul_lt_mul_of_pos_right (value_lt A) (by positivity)
     _=_:=(pow_add _ _ _).symm

 theorem multiply_length (A B:List Bool):(multiply A B).length≤A.length+B.length:=by
   apply trim_length_of_lt
   rw [multiply_fold_value]
   simpa only [value,Nat.zero_add] using product_lt A B

 theorem multiply_first_length (A B S:List Bool):
     (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).1.length=A.length+B.length:=by
   induction B generalizing A S with
   | nil => simp
   | cons b B ih =>
     rw [List.foldl_cons]
     change (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).1.length=_
     rw [ih]
     simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

 theorem multiply_canonical (A B S:List Bool) (hS:trim S=S):
     trim (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=(B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2:=by
   induction B generalizing A S with
   | nil => exact hS
   | cons b B ih =>
     rw [List.foldl_cons]
     apply ih
     cases b
     · exact hS
     · exact trim_idem _

 theorem multiply_prefix_length (A B:List Bool) (j:ℕ):
     ((B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])).2.length≤A.length+B.length:=by
   let P:=(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hc:trim P.2=P.2:=multiply_canonical A (B.take j) [] rfl
   rw [← hc]
   apply trim_length_of_lt
   have hfull:=multiply_fold_value A B []
   rw [← List.take_append_drop j B,List.foldl_append] at hfull
   have hpartial:=multiply_fold_value P.1 (B.drop j) P.2
   change value ((B.drop j).foldl _ P).2=_ at hfull
   rw [hpartial,List.take_append_drop] at hfull
   have hle:value P.2≤value A*value B:=by simpa only [value,Nat.zero_add] using (show value P.2≤value []+value A*value B by omega)
   exact hle.trans_lt (product_lt A B)

end EdgeSublinearMWIS.Main.RawStack

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def divideStep (x:Bool×(List Bool×(List Bool×List Bool))):List Bool×(List Bool×List Bool):=
   let B:=x.2.1
   let R:=x.1::x.2.2.1
   if BinarySubtract.less R B then (B,(trim R,false::x.2.2.2))
   else (B,(BinarySubtract.difference R B,true::x.2.2.2))
 def divide (A B:List Bool):List Bool×List Bool:=
   let s:=A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   (trim s.2.2,trim s.2.1)

 theorem divideStep_base (b:Bool) (B R Q:List Bool):(divideStep (b,(B,(R,Q)))).1=B:=by
   dsimp only [divideStep]
   split_ifs <;> rfl

 theorem divideStep_balance (b:Bool) (B R Q:List Bool):
     value (divideStep (b,(B,(R,Q)))).2.1+value B*value (divideStep (b,(B,(R,Q)))).2.2=
       b.toNat+2*(value R+value B*value Q):=by
   unfold divideStep
   by_cases h:BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     have hb:=(BinarySubtract.less_iff _ _).mp h
     simp only [value,Bool.toNat_false]
     ring
   · rw [if_neg h]
     rw [BinarySubtract.difference_value]
     have hb:value B≤value (b::R):=by
       exact Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have he:=Nat.sub_add_cancel hb
     simp only [value,Bool.toNat_true] at he ⊢
     nlinarith only [he]

 theorem divideStep_remainder (b:Bool) (B R Q:List Bool) (hB:0<value B) (hR:value R<value B):
     value (divideStep (b,(B,(R,Q)))).2.1<value B:=by
   unfold divideStep
   by_cases h:BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     exact (BinarySubtract.less_iff _ _).mp h
   · rw [if_neg h,BinarySubtract.difference_value]
     have hb:value B≤value (b::R):=Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have hbit:b.toNat≤1:=by cases b <;> decide
     simp only [value] at hb ⊢
     omega

 theorem divide_fold_base (L B R Q:List Bool):
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).1=B:=by
   induction L generalizing R Q with
   | nil => rfl
   | cons b L ih =>
     rw [List.foldl_cons]
     have hs:=divideStep_base b B R Q
     generalize he:divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hs
     subst B'
     exact ih R' Q'

 theorem divide_fold_balance (L B R Q:List Bool):
     let s:=L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))
     value s.2.1+value B*value s.2.2=value L.reverse+2^L.length*(value R+value B*value Q):=by
   induction L generalizing R Q with
   | nil => simp [value]
   | cons b L ih =>
     dsimp only
     rw [List.foldl_cons]
     have hbase:=divideStep_base b B R Q
     have hstep:=divideStep_balance b B R Q
     generalize he:divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     have hh:=ih R' Q'
     dsimp only at hh
     rw [hh,List.reverse_cons,BinaryAdder.value_append]
     simp only [value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     rw [hstep]
     ring

 theorem divide_fold_remainder (L B R Q:List Bool) (hB:0<value B) (hR:value R<value B):
     value (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1<value B:=by
   induction L generalizing R Q with
   | nil => exact hR
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase:=divideStep_base b B R Q
     have hstep:=divideStep_remainder b B R Q hB hR
     generalize he:divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     exact ih R' Q' hstep

 theorem divide_value (A B:List Bool) (hB:0<value B):
     value (divide A B).1=value A/value B∧ value (divide A B).2=value A%value B:=by
   have hb:=divide_fold_balance A.reverse B [] []
   have hr:=divide_fold_remainder A.reverse B [] [] hB (by simpa only [value] using hB)
   dsimp only at hb
   simp only [List.reverse_reverse,value,Nat.mul_zero,Nat.add_zero] at hb
   have he:=(Nat.div_mod_unique hB).mpr ⟨hb,hr⟩
   dsimp only [divide]
   simp only [trim_value]
   exact ⟨he.1.symm,he.2.symm⟩

 theorem divideStep_qlength (b:Bool) (B R Q:List Bool):
     (divideStep (b,(B,(R,Q)))).2.2.length=Q.length+1:=by
   dsimp only [divideStep]
   split_ifs <;> simp

 theorem divide_fold_qlength (L B R Q:List Bool):
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.2.length=Q.length+L.length:=by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase:=divideStep_base b B R Q
     have hlen:=divideStep_qlength b B R Q
     generalize he:divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     rw [ih,hlen]
     simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

 theorem divideStep_rlength (b:Bool) (B R Q:List Bool):
     (divideStep (b,(B,(R,Q)))).2.1.length≤R.length+1:=by
   dsimp only [divideStep]
   split_ifs
   · exact (trim_length _).trans (by simp)
   · exact (BinarySubtract.difference_length _ _).trans (by simp)

 theorem divide_fold_rlength (L B R Q:List Bool):
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1.length≤R.length+L.length:=by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase:=divideStep_base b B R Q
     have hlen:=divideStep_rlength b B R Q
     generalize he:divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     have hh:=ih R' Q'
     simp only [List.length_cons]
     omega

end EdgeSublinearMWIS.Main.RawStack

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryEuclid

 def step (s:ℕ×ℕ):ℕ×ℕ:=if s.2=0 then s else (s.2,s.1%s.2)

 theorem mod_mod_half (b r:ℕ) (hr:0<r) (hrb:r<b):2*(b%r)<b:=by
   by_cases h:2*r≤b
   · have hm:=Nat.mod_lt b hr
     omega
   · have hb:r≤b:=by omega
     have hsmall:b-r<r:=by omega
     have he:b%r=b-r:=by rw [Nat.mod_eq_sub_mod hb,Nat.mod_eq_of_lt hsmall]
     rw [he]
     omega

 theorem two_step (a b L:ℕ) (hb:b<2^(L+1)):(step^[2] (a,b)).2<2^L:=by
   by_cases hb0:b=0
   · simp [step,hb0]
   · have hbpos:0<b:=by omega
     by_cases hr0:a%b=0
     · simp [Function.iterate_succ_apply,step,hb0,hr0]
     · have hr:0<a%b:=by omega
       have hrb:=Nat.mod_lt a hbpos
       have hh:=mod_mod_half b (a%b) hr hrb
       simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,step,hb0,if_false,hr0]
       rw [pow_succ] at hb
       omega

 theorem terminates (a b L:ℕ) (hb:b<2^L):(step^[2*L] (a,b)).2=0:=by
   induction L generalizing a b with
   | zero =>
     simp only [pow_zero] at hb
     have hb0:b=0:=by omega
     simpa using hb0
   | succ L ih =>
     have hh:=two_step a b L hb
     have ht:=ih (step^[2] (a,b)).1 (step^[2] (a,b)).2 hh
     rw [Nat.mul_succ,Function.iterate_add_apply]
     exact ht

 theorem gcd_step (s:ℕ×ℕ):(step s).1.gcd (step s).2=s.1.gcd s.2:=by
   rcases s with ⟨a,b⟩
   by_cases hb:b=0
   · simp [step,hb]
   · simp only [step,hb,if_false]
     rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

 theorem gcd_iter (s:ℕ×ℕ) (t:ℕ):(step^[t] s).1.gcd (step^[t] s).2=s.1.gcd s.2:=by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (gcd_step _).trans ih

end EdgeSublinearMWIS.Main.BinaryEuclid

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
namespace BinaryGcd

 def step (s:List Bool×List Bool):List Bool×List Bool:=
   if s.2=[] then s else (s.2,(divide s.1 s.2).2)
 def run (A B:List Bool):List Bool×List Bool:=step^[2*B.length] (trim A,trim B)
 def gcd (A B:List Bool):List Bool:=(run A B).1

 theorem divide_lengths (A B:List Bool):
     (divide A B).1.length≤A.length∧ (divide A B).2.length≤A.length:=by
   have hr:=divide_fold_rlength A.reverse B [] []
   have hq:=divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   constructor
   · exact (trim_length _).trans hq.le
   · exact (trim_length _).trans hr

 theorem divide_canonical (A B:List Bool):trim (divide A B).1=(divide A B).1∧
     trim (divide A B).2=(divide A B).2:= ⟨trim_idem _,trim_idem _⟩

 theorem canonical_step (s:List Bool×List Bool) (hA:trim s.1=s.1) (hB:trim s.2=s.2):
     trim (step s).1=(step s).1∧ trim (step s).2=(step s).2:=by
   unfold step
   split_ifs
   · exact ⟨hA,hB⟩
   · exact ⟨hB,(divide_canonical _ _).2⟩

 theorem canonical_iter (s:List Bool×List Bool) (hA:trim s.1=s.1) (hB:trim s.2=s.2) (t:ℕ):
     trim (step^[t] s).1=(step^[t] s).1∧ trim (step^[t] s).2=(step^[t] s).2:=by
   induction t with
   | zero => exact ⟨hA,hB⟩
   | succ t ih => rw [Function.iterate_succ_apply']; exact canonical_step _ ih.1 ih.2

 theorem value_positive (A:List Bool) (hA:trim A=A) (hn:A≠[]):0<value A:=by
   have h:=trim_lower A (by simpa only [hA] using hn)
   rw [hA] at h
   exact lt_of_lt_of_le (by positivity:0<2^(A.length-1)) h

 theorem values_step (s:List Bool×List Bool) (hB:trim s.2=s.2):
     (value (step s).1,value (step s).2)=BinaryEuclid.step (value s.1,value s.2):=by
   by_cases hb:s.2=[]
   · simp [step,hb,value,BinaryEuclid.step]
   · have hp:=value_positive s.2 hB hb
     have he:=(divide_value s.1 s.2 hp).2
     simp only [step,hb,if_false,BinaryEuclid.step,ne_of_gt hp,he]

 theorem values_iter (s:List Bool×List Bool) (hA:trim s.1=s.1) (hB:trim s.2=s.2) (t:ℕ):
     (value (step^[t] s).1,value (step^[t] s).2)=BinaryEuclid.step^[t] (value s.1,value s.2):=by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
     rw [values_step _ (canonical_iter s hA hB t).2,ih]

 theorem run_second (A B:List Bool):(run A B).2=[]:=by
   have hc:=(canonical_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)).2
   have hv:=values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have ht:=BinaryEuclid.terminates (value (trim A)) (value (trim B)) B.length (by rw [trim_value]; exact value_lt B)
   have hz:value (run A B).2=0:=by
     exact (congrArg Prod.snd hv).trans ht
   by_contra hn
   exact (ne_of_gt (value_positive _ hc hn)) hz

 theorem gcd_value (A B:List Bool):value (gcd A B)=(value A).gcd (value B):=by
   have hv:=values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have hg:=BinaryEuclid.gcd_iter (value (trim A),value (trim B)) (2*B.length)
   have hv1:=congrArg Prod.fst hv
   have hv2:=congrArg Prod.snd hv
   change value (run A B).1=_ at hv1
   change value (run A B).2=_ at hv2
   rw [← hv1,← hv2,run_second,value,Nat.gcd_zero_right,trim_value,trim_value] at hg
   exact hg

 theorem length_step (s:List Bool×List Bool):(step s).1.length+(step s).2.length≤ s.1.length+s.2.length:=by
   unfold step
   split_ifs
   · rfl
   · have hh:=(divide_lengths s.1 s.2).2
     dsimp only
     omega

 theorem length_iter (s:List Bool×List Bool) (t:ℕ):
     (step^[t] s).1.length+(step^[t] s).2.length≤ s.1.length+s.2.length:=by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (length_step _).trans ih

end BinaryGcd
end EdgeSublinearMWIS.Main.RawStack

end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 theorem natBits_eq_bits (n:ℕ):natBits n=n.bits:=by
   simp only [natBits,Nat.digits_two_eq_bits,List.map_map]
   have he:((fun b:ℕ => b==1) ∘ (fun b:Bool => cond b 1 0))=id:=by funext b; cases b <;> rfl
   rw [he,List.map_id]

 theorem trim_eq_bits_value (A:List Bool):trim A=(value A).bits:=by
   induction A with
   | nil => exact Nat.zero_bits.symm
   | cons b A ih =>
     by_cases hA:trim A=[]
     · have hv:value A=0:=by rw [← trim_value A,hA]; rfl
       cases b <;> simp [trim,hA,value,hv,Nat.zero_bits,Nat.one_bits]
     · have hp:=BinaryGcd.value_positive (trim A) (trim_idem A) hA
       rw [trim_value] at hp
       have hb:Nat.bit b (value A)=b.toNat+2*value A:=by cases b <;> simp [Nat.bit]; omega
       simp only [trim,hA,if_false]
       rw [ih,value,← hb,Nat.bits_append_bit (value A) b (by omega)]

 theorem trim_eq_natBits (A:List Bool):trim A=natBits (value A):=by
   rw [natBits_eq_bits]
   exact trim_eq_bits_value A

 theorem canonical_eq_natBits (A:List Bool) (hA:trim A=A):A=natBits (value A):=by
   exact hA.symm.trans (trim_eq_natBits A)

 theorem canonical_value_injective (A B:List Bool) (hA:trim A=A) (hB:trim B=B) (h:value A=value B):A=B:=by
   rw [canonical_eq_natBits A hA,canonical_eq_natBits B hB,h]

 theorem value_natBits (n:ℕ):value (natBits n)=n:=by
   rw [natBits_eq_bits]
   induction n using Nat.binaryRecFromOne with
   | zero => simp [Nat.zero_bits,value]
   | one => simp [Nat.one_bits,value]
   | bit b n hn ih =>
     rw [Nat.bits_append_bit n b (fun h => False.elim (hn h))]
     cases b <;> simp [value,ih,Nat.bit] <;> omega

end EdgeSublinearMWIS.Main.RawStack

end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 def headBit:Realizer (fun A:List Bool => A.headD false) where
   transform:=Data.head
   charge:=fun x => x.size+2
   routine:=Routine.select true
   correct A:=by cases A <;> rfl

 def tailBits:Realizer (fun A:List Bool => A.tail) where
   transform:=Data.tail
   charge:=fun x => x.size+2
   routine:=Routine.select false
   correct A:=by cases A <;> rfl

 def xorBits:Realizer (fun x:Bool×Bool => xor x.1 x.2):=
   (Realizer.not.choose Realizer.id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 def bitA:Realizer (fun s:State => s.1.headD false):=Realizer.fst.comp headBit
 def bitB:Realizer (fun s:State => s.2.1.headD false):=(Realizer.snd.comp Realizer.fst).comp headBit
 def bitC:Realizer (fun s:State => s.2.2.1):=(Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def revOutput:Realizer (fun s:State => s.2.2.2):=(Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def sumBit:Realizer (fun s:State => xor (xor (s.1.headD false) (s.2.1.headD false)) s.2.2.1):=
   (((bitA.pair bitB).comp xorBits).pair bitC).comp xorBits
 def carryBit:Realizer (fun s:State =>
     (s.1.headD false && s.2.1.headD false)||(s.1.headD false && s.2.2.1)||(s.2.1.headD false && s.2.2.1)):=
   ((((bitA.pair bitB).comp Realizer.and).pair ((bitA.pair bitC).comp Realizer.and)).comp Realizer.or).pair
     ((bitB.pair bitC).comp Realizer.and) |>.comp Realizer.or

 def stepRealizer:Realizer step:=
   ((Realizer.fst.comp tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp tailBits).pair
       (carryBit.pair ((sumBit.pair revOutput).comp Realizer.cons)))).congr (fun _ => rfl)

 def wordLength:Realizer (fun A:List Bool => A.length):=
   (Uniform.length (I:=Unit) (α:=fun _ => Bool)).specialize ()
 def lengthBound:Realizer (fun x:List Bool×List Bool => x.1.length+x.2.length+1):=
   (((Realizer.fst.comp wordLength).pair (Realizer.snd.comp wordLength)).comp Realizer.add).comp Realizer.succ
 def initialState:Realizer (fun x:List Bool×List Bool => (x.1,(x.2,(false,([]:List Bool))))):=
   Realizer.fst.pair (Realizer.snd.pair (Realizer.false.pair Realizer.nil))
 def wordRealizer:Realizer (fun x:List Bool×List Bool => word x.1 x.2):=
   (((lengthBound.pair initialState).comp stepRealizer.iterate).comp revOutput).comp Realizer.reverse

end EdgeSublinearMWIS.Main.BinaryAdder

end
end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.NativeCompiler
 theorem runs_mono (P:Program) (input output:List Bool) {t u:ℕ}
    (ht:Runs P input output t) (htu:t≤u):Runs P input output u:=by
  obtain ⟨h⟩:=ht
  exact ⟨{h with steps_le_m:=h.steps_le_m.trans htu}⟩
end EdgeSublinearMWIS.Main.NativeCompiler

end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]

 def Linear {f:α→ β} (R:Realizer f):Prop:=
   ∃ C:ℕ,0<C∧ ∀ x,R.time x≤ C*(volume x+1)∧ volume (f x)≤ C*(volume x+1)

 theorem linear_of {f:α→ β} (R:Realizer f) (C:ℕ) (hC:0<C)
    (ht:∀x,R.time x≤C*(volume x+1)) (hv:∀x,volume (f x)≤C*(volume x+1)):Linear R:=
   ⟨C,hC,fun x => ⟨ht x,hv x⟩⟩

 theorem linear_comp {f:α→ β} {g:β→ γ} {R:Realizer f} {S:Realizer g}
    (hR:Linear R) (hS:Linear S):Linear (R.comp S):=by
   obtain ⟨C,hC,hR⟩:=hR
   obtain ⟨D,hD,hS⟩:=hS
   refine ⟨C+(D+10)*(C+1),by positivity,?_⟩
   intro x
   have h1:=hR x
   have h2:=hS (f x)
   have hV:volume (f x)+1≤ (C+1)*(volume x+1):=by nlinarith
   have htime:=(h2.1).trans (Nat.mul_le_mul_left D hV)
   have hout:=(h2.2).trans (Nat.mul_le_mul_left D hV)
   have hcopy:=Nat.mul_le_mul_left 10 hV
   constructor
   · rw [Realizer.time_comp]
     nlinarith
   · change volume (g (f x))≤_
     nlinarith

 theorem linear_pair {f:α→ β} {g:α→ γ} {R:Realizer f} {S:Realizer g}
    (hR:Linear R) (hS:Linear S):Linear (R.pair S):=by
   obtain ⟨C,hC,hR⟩:=hR
   obtain ⟨D,hD,hS⟩:=hS
   refine ⟨100*(C+D+1),by positivity,?_⟩
   intro x
   have h1:=hR x
   have h2:=hS x
   constructor
   · rw [Realizer.time_pair]
     nlinarith
   · simp only [volume_pair]
     nlinarith

 theorem linear_fst:Linear (Realizer.fst:Realizer (Prod.fst:α×β→ α)):=by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_snd:Linear (Realizer.snd:Realizer (Prod.snd:α×β→ β)):=by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_bool {f:α→ Bool} (R:Realizer f) (C:ℕ) (ht:∀x,R.time x≤C*(volume x+1)):Linear R:=by
   refine linear_of R (C+3) (by omega) ?_ ?_
   · intro x; have hh:=ht x; nlinarith
   · intro x; have hh:=volume_bool (f x); nlinarith

 theorem linear_and:Linear Realizer.and:=linear_bool _ 10000 (fun x =>
   (Realizer.time_and_le x).trans (by nlinarith))
 theorem linear_or:Linear Realizer.or:=linear_bool _ 10000 (fun x =>
   (Realizer.time_or_le x).trans (by nlinarith))
 theorem linear_not:Linear Realizer.not:=linear_bool _ 10000 (fun x =>
   (Realizer.time_not_le x).trans (by nlinarith))

theorem linear_finite [Fintype α] {f:α→ β} (R:Realizer f):Linear R:=by
   let C:=(∑ x:α, (R.time x+volume (f x)))+1
   refine ⟨C,by dsimp [C]; omega,?_⟩
   intro x
   have hx:=Finset.single_le_sum (fun z (_:z∈(Finset.univ:Finset α)) => Nat.zero_le (R.time z+volume (f z))) (Finset.mem_univ x)
   have hC:C≤C*(volume x+1):=by nlinarith
   constructor <;> dsimp [C] at * <;> omega

 theorem linear_cons:Linear (Realizer.cons:Realizer (fun x:α×List α => x.1::x.2)):=by
   refine linear_of _ 3 (by omega) ?_ ?_
   · intro x
     change volume x+2≤3*(volume x+1)
     omega
   · rintro ⟨a,L⟩
     simp only [volume_cons,volume_pair]
     omega

 theorem linear_id:Linear (Realizer.id:Realizer (id:α→ α)):=
   linear_of _ 3 (by omega) (fun x => by change volume x+2≤_; omega) (fun x => by change volume x≤3*(volume x+1); omega)

 theorem linear_choose {f g:α→ β} {R:Realizer f} {S:Realizer g}
    (hR:Linear R) (hS:Linear S):Linear (R.choose S):=by
   obtain ⟨C,hC,hR⟩:=hR
   obtain ⟨D,hD,hS⟩:=hS
   refine ⟨200*(C+D+1),by positivity,?_⟩
   rintro ⟨b,x⟩
   have hp:volume x+1≤volume (b,x)+1:=by simp only [volume_pair]; omega
   have h1:=hR x
   have h2:=hS x
   have hc:=Nat.mul_le_mul_left C hp
   have hd:=Nat.mul_le_mul_left D hp
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd,Function.comp_apply]
     nlinarith
   · change volume (if b then f x else g x)≤_
     split_ifs <;> nlinarith

 theorem linear_congr {f f':α→ β} (R:Realizer f) (hf:∀x,f x=f' x) (hR:Linear R):Linear (R.congr hf):=by
   obtain ⟨C,hC,hR⟩:=hR
   refine ⟨C,hC,?_⟩
   intro x
   have hh:=hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem headBit_linear:Linear headBit:=by
   apply linear_bool headBit 3
   intro A
   change volume A+2≤3*(volume A+1)
   omega

 theorem tailBits_linear:Linear tailBits:=by
   refine linear_of tailBits 3 (by omega) ?_ ?_
   · intro A
     change volume A+2≤3*(volume A+1)
     omega
   · intro A
     cases A with
     | nil => simp
     | cons a A => simp only [List.tail_cons,volume_cons]; omega

 theorem bitA_linear:Linear bitA:=linear_comp linear_fst headBit_linear
 theorem bitB_linear:Linear bitB:=linear_comp (linear_comp linear_snd linear_fst) headBit_linear
 theorem bitC_linear:Linear bitC:=linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem revOutput_linear:Linear revOutput:=linear_comp (linear_comp linear_snd linear_snd) linear_snd
 theorem sumBit_linear:Linear sumBit:=
   linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) (linear_finite xorBits)) bitC_linear) (linear_finite xorBits)
 theorem carryBit_linear:Linear carryBit:=
   linear_comp (linear_pair (linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) linear_and)
     (linear_comp (linear_pair bitA_linear bitC_linear) linear_and)) linear_or)
     (linear_comp (linear_pair bitB_linear bitC_linear) linear_and)) linear_or
 theorem step_linear:Linear stepRealizer:=by
   have hh:=linear_pair (linear_comp (linear_fst:Linear (Realizer.fst:Realizer (Prod.fst:State→ List Bool))) tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) tailBits_linear)
       (linear_pair carryBit_linear (linear_comp (linear_pair sumBit_linear revOutput_linear) linear_cons)))
   exact hh

 theorem step_volume (s:State):volume (step s)≤volume s+6:=by
   rcases s with ⟨A,B,c,R⟩
   have hA:volume A.tail≤volume A:=by cases A <;> simp [volume_cons] <;> omega
   have hB:volume B.tail≤volume B:=by cases B <;> simp [volume_cons] <;> omega
   have hsum:=volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry:=volume_bool ((A.headD false && B.headD false)||(A.headD false && c)||(B.headD false && c))
   have hc:1≤volume c:=volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinaryAdder

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 theorem volume_bits (A:List Bool):volume A≤4*A.length+1:=
   (volume_list_le A 3 (fun b _ => volume_bool b)).trans (by omega)

 theorem length_step_time (a:Bool) (b:ℕ):
     ((Realizer.snd:Realizer (Prod.snd:Bool×ℕ→ ℕ)).comp Realizer.succ).time (a,b)≤1000*(b+1):=by
   rw [Realizer.time_comp,Realizer.time_snd]
   have ht:=Realizer.time_succ_le b
   simp only [volume_pair,volume_nat]
   have hb:=volume_bool a
   nlinarith

 theorem length_fold_time (A:List Bool) (b:ℕ):
     Realizer.foldTime ((Realizer.snd:Realizer (Prod.snd:Bool×ℕ→ ℕ)).comp Realizer.succ) b A≤
       10000*(A.length+1)*(volume A+2*b+2*A.length+1):=by
   induction A generalizing b with
   | nil => simp [Realizer.foldTime,volume_nil]; omega
   | cons a A ih =>
     have hh:=ih (b+1)
     have ht:=length_step_time a b
     have ha:=volume_bool a
     have hp:=volume_pos A
     change _+Realizer.foldTime _ (b+1) A+20*(volume (a::A)+volume b+volume (b+1)+1)≤ _
     simp only [volume_cons,volume_nat,List.length_cons] at hh ⊢
     nlinarith

 theorem wordLength_time (A:List Bool):wordLength.time A≤1000000*(A.length+1)^2:=by
   have hf:=length_fold_time A 0
   have hv:=volume_bits A
   change (Uniform.length (I:=Unit) (α:=fun _ => Bool)).time () A≤_
   rw [Uniform.length,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,Uniform.time_id,Uniform.time_zero,Uniform.time_fold]
   simp only [Uniform.time_uniform,Function.comp_apply,volume_pair,volume_nat,Nat.mul_zero,Nat.add_zero] at hf ⊢
   have hfold:Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤
       10000*(A.length+1)*(volume A+2*A.length+1):=hf
   have hf':Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤100000*(A.length+1)^2:=by
     calc
       _≤ 10000*(A.length+1)*(volume A+2*A.length+1):=hfold
       _≤ 10000*(A.length+1)*(6*A.length+2):=Nat.mul_le_mul_left _ (by omega)
       _≤ _:=by nlinarith
   nlinarith

end EdgeSublinearMWIS.Main.BinaryAdder

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem iter_volume (s:State) (t:ℕ):volume ((step^[t]) s)≤volume s+6*t:=by
   induction t with
   | zero => simp
   | succ t ih => rw [Function.iterate_succ_apply']; have hh:=step_volume ((step^[t]) s); omega

 theorem initial_volume (A B:List Bool):volume (A,(B,(false,([]:List Bool))))≤4*(A.length+B.length)+7:=by
   have hA:=volume_bits A
   have hB:=volume_bits B
   simp only [volume_pair,volume_bool_false,volume_nil]
   omega

 theorem iterate_time:∃ C:ℕ,0<C∧ ∀ A B:List Bool,
     stepRealizer.iterate.time (A.length+B.length+1,(A,(B,(false,([]:List Bool)))))≤C*(A.length+B.length+1)^2:=by
   obtain ⟨C,hC,hlinear⟩:=step_linear
   refine ⟨1000000*(C+1),by positivity,?_⟩
   intro A B
   let z:=A.length+B.length+1
   let s:State:=(A,(B,(false,[])))
   have hz:1≤z:=by dsimp [z]; omega
   have hvol (j:ℕ) (hj:j≤z):volume ((step^[j]) s)≤14*z:=by
     have hi:=initial_volume A B
     have hv:=iter_volume s j
     dsimp [s,z] at *
     omega
   have htime (j:ℕ) (hj:j<z):stepRealizer.time ((step^[j]) s)≤C*(14*z+1):=
     ((hlinear _).1).trans (Nat.mul_le_mul_left C (by have hh:=hvol j hj.le; omega))
   have hh:=Realizer.time_iterate_le stepRealizer z s (C*(14*z+1)) (14*z) htime hvol
   calc
     _≤ 10000*(z+1)*(C*(14*z+1)+14*z+z+1):=hh
     _≤ 10000*(2*z)*((15*C+16)*z):=by
       apply Nat.mul_le_mul
       · exact Nat.mul_le_mul_left _ (by omega)
       · have hc:=Nat.mul_le_mul_left C (show 14*z+1≤15*z by omega)
         nlinarith
     _=(20000*(15*C+16))*z^2:=by ring
     _≤ (1000000*(C+1))*z^2:=Nat.mul_le_mul_right _ (by omega)

 theorem lengthBound_time (A B:List Bool):
     lengthBound.time (A,B)≤1000000000*(A.length+B.length+1)^2:=by
   have hA:=wordLength_time A
   have hB:=wordLength_time B
   have hvA:=volume_bits A
   have hvB:=volume_bits B
   have ha:=Realizer.time_add_le A.length B.length
   have hs:=Realizer.time_succ_le (A.length+B.length)
   simp only [lengthBound,Realizer.time_comp,Realizer.time_pair,Realizer.time_fst,Realizer.time_snd,Function.comp_apply,volume_pair,volume_nat]
   have hLA:(A.length+1)^2≤(A.length+B.length+1)^2:=Nat.pow_le_pow_left (by omega) 2
   have hLB:(B.length+1)^2≤(A.length+B.length+1)^2:=Nat.pow_le_pow_left (by omega) 2
   have hA':=hA.trans (Nat.mul_le_mul_left 1000000 hLA)
   have hB':=hB.trans (Nat.mul_le_mul_left 1000000 hLB)
   nlinarith

 theorem initial_linear:Linear initialState:=by
   have hfalse:Linear (Realizer.false:Realizer (fun _:List Bool×List Bool => false)):=by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   have hnil:Linear (Realizer.nil:Realizer (fun _:List Bool×List Bool => ([]:List Bool))):=by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact linear_pair linear_fst (linear_pair linear_snd (linear_pair hfalse hnil))

 theorem reverse_time (A:List Bool):(Realizer.reverse:Realizer (fun A:List Bool => A.reverse)).time A≤200*(A.length+1)*(volume A+1):=
   Uniform.time_reverse (I:=Unit) (α:=fun _ => Bool) () A

end EdgeSublinearMWIS.Main.BinaryAdder

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem word_time:∃ C:ℕ,0<C∧ ∀ A B:List Bool,
     wordRealizer.time (A,B)≤C*(A.length+B.length+1)^2:=by
   obtain ⟨C,hC,hiter⟩:=iterate_time
   obtain ⟨I,hI,hinit⟩:=initial_linear
   obtain ⟨O,hO,hout⟩:=revOutput_linear
   refine ⟨1000000000+C+5*I+15*O+20000,by positivity,?_⟩
   intro A B
   let z:=A.length+B.length+1
   let s:State:=(A,(B,(false,[])))
   let t:State:=(step^[z]) s
   have hz:1≤z:=by dsimp [z]; omega
   have hzsq:z≤z^2:=by nlinarith
   have hvA:=volume_bits A
   have hvB:=volume_bits B
   have hvx:volume (A,B)≤4*z:=by simp only [volume_pair]; dsimp [z]; omega
   have hvs:volume s≤7*z:=by have hh:=initial_volume A B; dsimp [s,z] at *; omega
   have hvt:volume t≤14*z:=by have hh:=iter_volume s z; dsimp [t]; omega
   have hvr:volume t.2.2.2≤volume t:=by
     rcases t with ⟨T,U,c,R⟩
     simp only [volume_pair]
     omega
   have hlen:t.2.2.2.length=z:=by
     have hh:=(iter_lists s z).2.2
     simpa [s] using hh
   have hinit0:=(hinit (A,B)).1
   have hinit1:initialState.time (A,B)≤5*I*z^2:=by
     calc
       _≤ I*(volume (A,B)+1):=hinit0
       _≤ I*(5*z):=Nat.mul_le_mul_left _ (by omega)
       _≤ 5*I*z^2:=by nlinarith [Nat.mul_le_mul_left (5*I) hzsq]
   have hout0:=(hout t).1
   have hout1:revOutput.time t≤15*O*z^2:=by
     calc
       _≤ O*(volume t+1):=hout0
       _≤ O*(15*z):=Nat.mul_le_mul_left _ (by omega)
       _≤ 15*O*z^2:=by nlinarith [Nat.mul_le_mul_left (15*O) hzsq]
   have hr:=reverse_time t.2.2.2
   have hr1:(Realizer.reverse:Realizer (fun A:List Bool => A.reverse)).time t.2.2.2≤6000*z^2:=by
     calc
       _≤ 200*(z+1)*(volume t.2.2.2+1):=by simpa only [hlen] using hr
       _≤ 200*(2*z)*(15*z):=Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
       _=6000*z^2:=by ring
   have hiter1:stepRealizer.iterate.time (z,s)≤C*z^2:=hiter A B
   have hlen1:lengthBound.time (A,B)≤1000000000*z^2:=lengthBound_time A B
   have hvolZ:volume z=2*z+1:=volume_nat z
   have hcopy0:20*(volume (A,B)+volume z+volume s+1)+10*(volume (z,s)+1)+10*(volume t+1)+10*(volume t.2.2.2+1)≤10000*z^2:=by
     simp only [volume_pair,hvolZ]
     omega
   have hrealtime:wordRealizer.time (A,B)=lengthBound.time (A,B)+initialState.time (A,B)+
       20*(volume (A,B)+volume z+volume s+1)+stepRealizer.iterate.time (z,s)+10*(volume (z,s)+1)+
       revOutput.time t+10*(volume t+1)+
       (Realizer.reverse:Realizer (fun A:List Bool => A.reverse)).time t.2.2.2+10*(volume t.2.2.2+1):=by
     dsimp only [wordRealizer,word]
     simp only [Realizer.time_comp,Realizer.time_pair,Function.comp_apply,volume_reverse]
     rfl
   rw [hrealtime]
   change _≤(1000000000+C+5*I+15*O+20000)*z^2
   nlinarith only [hinit1,hout1,hr1,hiter1,hlen1,hcopy0]

end EdgeSublinearMWIS.Main.BinaryAdder

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonemptyBits:Realizer (fun L:List Bool => !L.isEmpty):=
   (Uniform.isCons (I:=Unit) (α:=fun _ => Bool)).specialize ()
 def keepBit:Realizer (fun x:Bool×List Bool => x.1 || !x.2.isEmpty):=
   (Realizer.fst.pair (Realizer.snd.comp nonemptyBits)).comp Realizer.or
 def trimStepRealizer:Realizer trimStep:=
   ((keepBit.pair Realizer.id).comp (Realizer.cons.choose Realizer.nil)).congr (fun x => by
     rcases x with ⟨b,L⟩
     cases L with
     | nil => cases b <;> rfl
     | cons a L => cases b <;> rfl)
 def trimRealizer:Realizer trim:=
   (((Realizer.reverse:Realizer (fun L:List Bool => L.reverse)).pair Realizer.nil).comp trimStepRealizer.fold).congr (fun L => trim_fold L)

 theorem nonempty_linear:Linear nonemptyBits:=by
   apply linear_bool nonemptyBits 10000
   intro L
   exact Realizer.time_test_le (fun L:List Bool => !L.isEmpty) (by intro L; cases L <;> rfl) L

 theorem trimStep_linear:Linear trimStepRealizer:=by
   have hkeep:Linear keepBit:=linear_comp (linear_pair linear_fst (linear_comp linear_snd nonempty_linear)) linear_or
   have hcons:Linear (Realizer.cons:Realizer (fun x:Bool×List Bool => x.1::x.2)):=linear_cons
   have hnil:Linear (Realizer.nil:Realizer (fun _:Bool×List Bool => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun x => by change 2≤_; omega) (fun x => by simp; omega)
   unfold trimStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair hkeep linear_id) (linear_choose hcons hnil)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem trimStep_volume (b:Bool) (T:List Bool):volume (trimStep (b,T))≤volume T+4:=by
   cases T with
   | nil => cases b <;> decide
   | cons a T => simp only [trimStep,List.cons_ne_nil,if_false,volume_cons]; have hb:=volume_bool b; omega

 theorem trim_fold_time:∃ C:ℕ,0<C∧ ∀ (L T:List Bool),
     Realizer.foldTime trimStepRealizer T L≤C*(L.length+1)*(volume L+volume T+4*L.length+1):=by
   obtain ⟨C,hC,hlin⟩:=trimStep_linear
   let K:=100*(C+1)
   refine ⟨K,by dsimp [K]; positivity,?_⟩
   intro L
   induction L with
   | nil =>
     intro T
     simp only [Realizer.foldTime,List.length_nil,volume_nil,Nat.zero_mul,Nat.zero_add,Nat.mul_one]
     dsimp [K]
     nlinarith
   | cons b L ih =>
     intro T
     let V:=volume (b::L)+volume T+4*(b::L).length+1
     have hVpos:1≤V:=by dsimp [V]; omega
     have hL:=volume_pos L
     have hT:=volume_pos T
     have hb:=volume_bool b
     have hstep:=trimStep_volume b T
     have hrec:=ih (trimStep (b,T))
     have hsub:volume L+volume (trimStep (b,T))+4*L.length+1≤V:=by
       dsimp [V]
       simp only [volume_cons,List.length_cons]
       omega
     have hrec':Realizer.foldTime trimStepRealizer (trimStep (b,T)) L≤K*(L.length+1)*V:=
       hrec.trans (Nat.mul_le_mul_left _ hsub)
     have harg:volume (b,T)+1≤V:=by dsimp [V]; simp only [volume_cons,volume_pair,List.length_cons]; omega
     have htime:trimStepRealizer.time (b,T)≤C*V:=
       ((hlin (b,T)).1).trans (Nat.mul_le_mul_left _ harg)
     have hcopy:20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤80*V:=by
       have hh1:volume (b::L)≤V:=by dsimp [V]; omega
       have hh2:volume T≤V:=by dsimp [V]; omega
       have hh3:volume (trimStep (b,T))≤V:=by dsimp [V]; omega
       omega
     have hcoeff:(C+80)*V≤K*V:=Nat.mul_le_mul_right _ (by dsimp [K]; omega)
     change trimStepRealizer.time (b,T)+Realizer.foldTime trimStepRealizer (trimStep (b,T)) L+
       20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤K*((b::L).length+1)*V
     simp only [List.length_cons]
     nlinarith only [htime,hrec',hcopy,hcoeff]

 theorem trim_time:∃ C:ℕ,0<C∧ ∀ L:List Bool,trimRealizer.time L≤C*(L.length+1)^2:=by
   obtain ⟨C,hC,hfold⟩:=trim_fold_time
   refine ⟨10000*(C+1),by positivity,?_⟩
   intro L
   have hv:=BinaryAdder.volume_bits L
   have hr:=BinaryAdder.reverse_time L
   have hf:=hfold L.reverse []
   simp only [List.length_reverse,volume_reverse,volume_nil] at hf
   have hf':Realizer.foldTime trimStepRealizer [] L.reverse≤8*C*(L.length+1)^2:=by
     calc
       _≤ C*(L.length+1)*(volume L+1+4*L.length+1):=hf
       _≤ C*(L.length+1)*(8*(L.length+1)):=Nat.mul_le_mul_left _ (by omega)
       _=_:=by ring
   have hr':(Realizer.reverse:Realizer (fun L:List Bool => L.reverse)).time L≤1000*(L.length+1)^2:=by
     calc
       _≤ 200*(L.length+1)*(volume L+1):=hr
       _≤ 200*(L.length+1)*(5*(L.length+1)):=Nat.mul_le_mul_left _ (by omega)
       _=_:=by ring
   have hnil:(Realizer.nil:Realizer (fun _:List Bool => ([]:List Bool))).time L=2:=rfl
   have he:trimRealizer.time L=(Realizer.reverse:Realizer (fun L:List Bool => L.reverse)).time L+2+
       20*(volume L+volume L+1+1)+(2*volume (L.reverse,([]:List Bool))+6+Realizer.foldTime trimStepRealizer [] L.reverse)+
       10*(volume (L.reverse,([]:List Bool))+1):=by
     simp only [trimRealizer,Realizer.time_congr,Realizer.time_comp,Realizer.time_pair,hnil,volume_nil,Realizer.time_fold,Function.comp_apply,volume_reverse]
   rw [he]
   simp only [volume_pair,volume_reverse,volume_nil]
   nlinarith only [hr',hf',hv]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def addThenTrim:Realizer (fun x:List Bool×List Bool => trim (BinaryAdder.word x.2 x.1)):=
   ((Realizer.snd.pair Realizer.fst).comp BinaryAdder.wordRealizer).comp trimRealizer
 def selectedSum:Realizer (fun x:Bool×(List Bool×List Bool) =>
     if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2):=
   addThenTrim.choose Realizer.snd
 def shiftedWord:Realizer (fun x:Bool×(List Bool×List Bool) => false::x.2.1):=
   (Realizer.false.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons
 def multiplyStepRealizer:Realizer multiplyStep:=
   (shiftedWord.pair selectedSum).congr (fun _ => rfl)
 def multiplyInitial:Realizer (fun x:List Bool×List Bool => (x.2,(x.1,([]:List Bool)))):=
   Realizer.snd.pair (Realizer.fst.pair Realizer.nil)
 def multiplyRealizer:Realizer (fun x:List Bool×List Bool => multiply x.1 x.2):=
   (((multiplyInitial.comp multiplyStepRealizer.fold).comp Realizer.snd).comp trimRealizer).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]

 def PolyBound {f:α→ β} (R:Realizer f):Prop:=
   ∃ C q:ℕ,0<C∧ ∀ x,R.time x≤C*(volume x+1)^q∧ volume (f x)≤C*(volume x+1)^q

 theorem linear_polynomial {f:α→ β} {R:Realizer f} (hR:Linear R):PolyBound R:=by
   obtain ⟨C,hC,hR⟩:=hR
   exact ⟨C,1,hC,by simpa only [pow_one] using hR⟩

 theorem polynomial_comp {f:α→ β} {g:β→ γ} {R:Realizer f} {S:Realizer g}
    (hR:PolyBound R) (hS:PolyBound S):PolyBound (R.comp S):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   refine ⟨C+D*(C+1)^r+10*(C+1),q+q*r,by positivity,?_⟩
   intro x
   let z:=volume x+1
   have hz:1≤z:=by dsimp [z]; omega
   have hq:1≤z^q:=one_le_pow₀ hz
   have h1:=hR x
   change R.time x≤C*z^q∧ volume (f x)≤C*z^q at h1
   have h2:=hS (f x)
   have hV:volume (f x)+1≤(C+1)*z^q:=by change volume (f x)+1≤_; nlinarith
   have hVp:=Nat.pow_le_pow_left hV r
   have hPow:((C+1)*z^q)^r=(C+1)^r*z^(q*r):=by rw [mul_pow,pow_mul]
   rw [hPow] at hVp
   have hqr:z^q≤z^(q+q*r):=Nat.pow_le_pow_right hz (by omega)
   have hrr:z^(q*r)≤z^(q+q*r):=Nat.pow_le_pow_right hz (by omega)
   have htime1:=h1.1.trans (Nat.mul_le_mul_left C hqr)
   have htime2:=h2.1.trans (Nat.mul_le_mul_left D hVp)
   have htime2:=htime2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   have hcopy:=(Nat.mul_le_mul_left 10 hV).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqr)
   have hout:=h2.2.trans (Nat.mul_le_mul_left D hVp)
   have hout:=hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     nlinarith only [htime1,htime2,hcopy]
   · change volume (g (f x))≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     exact hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^(q+q*r)) (show D*(C+1)^r≤C+D*(C+1)^r+10*(C+1) by omega))

 theorem polynomial_pair {f:α→ β} {g:α→ γ} {R:Realizer f} {S:Realizer g}
    (hR:PolyBound R) (hS:PolyBound S):PolyBound (R.pair S):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   refine ⟨100*(C+D+1),q+r+1,by positivity,?_⟩
   intro x
   let z:=volume x+1
   have hz:1≤z:=by dsimp [z]; omega
   have hp:z≤z^(q+r+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+r+1)
   have hq:z^q≤z^(q+r+1):=Nat.pow_le_pow_right hz (by omega)
   have hr:z^r≤z^(q+r+1):=Nat.pow_le_pow_right hz (by omega)
   have h1:=hR x
   have h2:=hS x
   have ht1:=h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1:=h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2:=h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · rw [Realizer.time_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     change z≤z^(q+r+1) at hp
     have hsmall:R.time x+S.time x+20*(volume x+volume (f x)+volume (g x)+1)≤(21*C+21*D+20)*z^(q+r+1):=by
       have hp':volume x+1≤z^(q+r+1):=hp
       nlinarith only [ht1,ht2,hv1,hv2,hp']
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · simp only [volume_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     have hp1:1≤z^(q+r+1):=one_le_pow₀ hz
     have hsmall:volume (f x)+volume (g x)+1≤(C+D+1)*z^(q+r+1):=by nlinarith only [hv1,hv2,hp1]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))

 theorem polynomial_congr {f f':α→ β} (R:Realizer f) (hf:∀x,f x=f' x)
    (hR:PolyBound R):PolyBound (R.congr hf):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   refine ⟨C,q,hC,?_⟩
   intro x
   have hh:=hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

 theorem polynomial_choose {f g:α→ β} {R:Realizer f} {S:Realizer g}
    (hR:PolyBound R) (hS:PolyBound S):PolyBound (R.choose S):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   refine ⟨200*(C+D+1),q+r+1,by positivity,?_⟩
   rintro ⟨b,x⟩
   let z:=volume (b,x)+1
   let p:=z^(q+r+1)
   have hz:1≤z:=by dsimp [z]; omega
   have hx:volume x+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hq:(volume x+1)^q≤p:=(Nat.pow_le_pow_left hx q).trans (Nat.pow_le_pow_right hz (by omega))
   have hr:(volume x+1)^r≤p:=(Nat.pow_le_pow_left hx r).trans (Nat.pow_le_pow_right hz (by omega))
   have hp:z≤p:=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+r+1)
   have h1:=hR x
   have h2:=hS x
   have ht1:=h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1:=h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2:=h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd]
     change _≤200*(C+D+1)*p
     have hsmall:volume (b,x)+2+R.time x+10*(volume x+1)+(volume (b,x)+2+S.time x+10*(volume x+1))+
         30*(volume (b,x)+volume (f x)+volume (g x)+1)≤(31*C+31*D+100)*p:=by
       dsimp [z] at hx hp
       nlinarith only [ht1,ht2,hv1,hv2,hx,hp]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (if b then f x else g x)≤200*(C+D+1)*p
     split_ifs
     · exact hv1.trans (Nat.mul_le_mul_right _ (by omega))
     · exact hv2.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem bits_length_volume (L:List Bool):L.length≤volume L:=by
   induction L with
   | nil => simp
   | cons b L ih => simp only [List.length_cons,volume_cons]; omega

 theorem word_polynomial:PolyBound BinaryAdder.wordRealizer:=by
   obtain ⟨C,hC,hT⟩:=BinaryAdder.word_time
   refine ⟨C+5,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have ha:=bits_length_volume A
   have hb:=bits_length_volume B
   have hV:A.length+B.length+1≤volume (A,B)+1:=by simp only [volume_pair]; omega
   have hp:=Nat.pow_le_pow_left hV 2
   have ht:=(hT A B).trans (Nat.mul_le_mul_left C hp)
   have hv:=BinaryAdder.volume_bits (BinaryAdder.word A B)
   rw [BinaryAdder.word_length] at hv
   have hz:1≤volume (A,B)+1:=by omega
   have hsq:volume (A,B)+1≤(volume (A,B)+1)^2:=by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (BinaryAdder.word A B)≤_
     have hv':volume (BinaryAdder.word A B)≤5*(volume (A,B)+1)^2:=by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem trim_polynomial:PolyBound trimRealizer:=by
   obtain ⟨C,hC,hT⟩:=trim_time
   refine ⟨C+5,2,by omega,?_⟩
   intro L
   have hlen:=bits_length_volume L
   have hp:=Nat.pow_le_pow_left (show L.length+1≤volume L+1 by omega) 2
   have ht:=(hT L).trans (Nat.mul_le_mul_left C hp)
   have hv:=BinaryAdder.volume_bits (trim L)
   have htrim:=trim_length L
   have hz:1≤volume L+1:=by omega
   have hsq:volume L+1≤(volume L+1)^2:=by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · have hv':volume (trim L)≤5*(volume L+1)^2:=by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem addThenTrim_polynomial:PolyBound addThenTrim:=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial linear_fst)) word_polynomial) trim_polynomial
 theorem selectedSum_polynomial:PolyBound selectedSum:=
   polynomial_choose addThenTrim_polynomial (linear_polynomial linear_snd)
 theorem shiftedWord_polynomial:PolyBound shiftedWord:=by
   have hf:Linear (Realizer.false:Realizer (fun _:Bool×(List Bool×List Bool) => false)):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact linear_polynomial (linear_comp (linear_pair hf (linear_comp linear_snd linear_fst)) linear_cons)
 theorem multiplyStep_polynomial:PolyBound multiplyStepRealizer:=by
   unfold multiplyStepRealizer
   apply polynomial_congr
   exact polynomial_pair shiftedWord_polynomial selectedSum_polynomial

 theorem reverse_polynomial:PolyBound (Realizer.reverse:Realizer (fun L:List Bool => L.reverse)):=by
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen:=bits_length_volume L
   have hT:=BinaryAdder.reverse_time L
   have hmul:=Nat.mul_le_mul_right (200*(volume L+1)) (show L.length+1≤volume L+1 by omega)
   have hv:volume L≤(volume L+1)^2:=by nlinarith
   constructor
   · have hh:200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2:=by nlinarith only [hmul]
     exact (hT.trans hh).trans (Nat.mul_le_mul_right _ (by omega))
   · rw [volume_reverse]
     exact hv.trans (Nat.le_mul_of_pos_left _ (by omega))

 theorem lengthBound_polynomial:PolyBound BinaryAdder.lengthBound:=by
   refine ⟨1000000001,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have hA:=bits_length_volume A
   have hB:=bits_length_volume B
   have hbase:A.length+B.length+1≤volume (A,B)+1:=by simp only [volume_pair]; omega
   have hp:=Nat.pow_le_pow_left hbase 2
   have ht:=(BinaryAdder.lengthBound_time A B).trans (Nat.mul_le_mul_left 1000000000 hp)
   have hz:volume (A,B)+1≤(volume (A,B)+1)^2:=by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (A.length+B.length+1)≤_
     rw [volume_nat]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 theorem iterate_coefficient (F D:ℕ):10000*F+10000*(D+3)≤100000*(F+D+10):=by omega
 theorem iterate_output_coefficient (F D:ℕ):D+1≤100000*(F+D+10):=by omega

 theorem polynomial_iterate {f:α→ α} {R:Realizer f} (hR:PolyBound R) (D:ℕ)
    (hg:∀x,volume (f x)≤volume x+D):PolyBound R.iterate:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   let F:=C*(D+2)^q
   refine ⟨100000*(F+D+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z:=volume (n,a)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hn:n+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha:volume a≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hiter (j:ℕ):volume (f^[j] a)≤volume a+D*j:=by
     induction j with
     | zero => simp
     | succ j ih => rw [Function.iterate_succ_apply']; have hh:=hg (f^[j] a); nlinarith
   have hV (j:ℕ) (hj:j≤n):volume (f^[j] a)≤(D+1)*z:=by
     have hh:=hiter j
     have hd:=Nat.mul_le_mul_left D (show j≤z by omega)
     nlinarith
   have hT (j:ℕ) (hj:j<n):R.time (f^[j] a)≤F*z^q:=by
     have hh:=(hR (f^[j] a)).1
     have hv:=hV j hj.le
     have hbase:volume (f^[j] a)+1≤(D+2)*z:=by nlinarith
     have ht:=hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht:=Realizer.time_iterate_le R n a (F*z^q) ((D+1)*z) hT hV
   have hq:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hq2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hze:z≤z^(q+2):=by exact (show z≤z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+D+10)*z^(q+2)
     have hmul:(n+1)*(F*z^q+(D+1)*z+n+1)≤z*(F*z^q+(D+3)*z):=
       Nat.mul_le_mul hn (by nlinarith)
     have hmul':=Nat.mul_le_mul_left 10000 hmul
     have hp1:=Nat.mul_le_mul_left (10000*F) hq
     have hp2:=Nat.mul_le_mul_left (10000*(D+3)) hq2
     have hsmall:R.iterate.time (n,a)≤(10000*F+10000*(D+3))*z^(q+2):=by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     have hcoef:=iterate_coefficient F D
     exact hsmall.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (f^[n] a)≤100000*(F+D+10)*z^(q+2)
     have hcoef:=iterate_output_coefficient F D
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left (D+1) hze).trans (Nat.mul_le_mul_right (z^(q+2)) hcoef))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def notA:Realizer (fun s:State => !s.1.headD false):=BinaryAdder.bitA.comp Realizer.not
 def borrowBit:Realizer (fun s:State =>
     (!s.1.headD false && (s.2.1.headD false || s.2.2.1))||(s.2.1.headD false && s.2.2.1)):=
   ((notA.pair ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.or)).comp Realizer.and).pair
     ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.and) |>.comp Realizer.or
 def stepRealizer:Realizer step:=
   ((Realizer.fst.comp BinaryAdder.tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
       (borrowBit.pair ((BinaryAdder.sumBit.pair BinaryAdder.revOutput).comp Realizer.cons)))).congr (fun _ => rfl)
 def rawRealizer:Realizer (fun x:List Bool×List Bool => raw x.1 x.2):=
   (((BinaryAdder.lengthBound.pair BinaryAdder.initialState).comp stepRealizer.iterate).comp
     (BinaryAdder.bitC.pair (BinaryAdder.revOutput.comp Realizer.reverse))).congr (fun _ => rfl)
 def lessRealizer:Realizer (fun x:List Bool×List Bool => less x.1 x.2):=rawRealizer.comp Realizer.fst
 def differenceRealizer:Realizer (fun x:List Bool×List Bool => difference x.1 x.2):=
   (rawRealizer.comp (Realizer.nil.choose RawStack.trimRealizer)).congr (fun _ => rfl)

 theorem step_linear:Linear stepRealizer:=by
   have hnot:Linear notA:=linear_comp BinaryAdder.bitA_linear linear_not
   have hborrow:Linear borrowBit:=linear_comp
     (linear_pair (linear_comp (linear_pair hnot (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_or)) linear_and)
       (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_and)) linear_or
   unfold stepRealizer
   apply linear_congr
   exact linear_pair (linear_comp linear_fst BinaryAdder.tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.tailBits_linear)
       (linear_pair hborrow (linear_comp (linear_pair BinaryAdder.sumBit_linear BinaryAdder.revOutput_linear) linear_cons)))

 theorem step_volume (s:State):volume (step s)≤volume s+6:=by
   rcases s with ⟨A,B,c,R⟩
   have hA:volume A.tail≤volume A:=by cases A <;> simp [volume_cons] <;> omega
   have hB:volume B.tail≤volume B:=by cases B <;> simp [volume_cons] <;> omega
   have hsum:=volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry:=volume_bool ((!A.headD false && (B.headD false || c))||(B.headD false && c))
   have hc:1≤volume c:=volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinarySubtract

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem raw_polynomial:PolyBound rawRealizer:=by
   have hpre:=polynomial_pair RawStack.lengthBound_polynomial (linear_polynomial BinaryAdder.initial_linear)
   have hiter:=polynomial_iterate (linear_polynomial step_linear) 6 step_volume
   have hpost:=polynomial_pair (linear_polynomial BinaryAdder.bitC_linear)
     (polynomial_comp (linear_polynomial BinaryAdder.revOutput_linear) RawStack.reverse_polynomial)
   unfold rawRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp hpre hiter) hpost

 theorem less_polynomial:PolyBound lessRealizer:=
   polynomial_comp raw_polynomial (linear_polynomial linear_fst)

 theorem difference_polynomial:PolyBound differenceRealizer:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List Bool => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold differenceRealizer
   apply polynomial_congr
   exact polynomial_comp raw_polynomial (polynomial_choose (linear_polynomial hn) RawStack.trim_polynomial)

end EdgeSublinearMWIS.Main.BinarySubtract

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
abbrev DivisionState:=List Bool×(List Bool×List Bool)
abbrev DivisionInput:=Bool×DivisionState

 def divisionDen:Realizer (fun x:DivisionInput => x.2.1):=Realizer.snd.comp Realizer.fst
 def divisionOldR:Realizer (fun x:DivisionInput => x.2.2.1):=(Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def divisionOldQ:Realizer (fun x:DivisionInput => x.2.2.2):=(Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def divisionNewR:Realizer (fun x:DivisionInput => x.1::x.2.2.1):=
   (Realizer.fst.pair divisionOldR).comp Realizer.cons
 def divisionPair:Realizer (fun x:DivisionInput => (x.1::x.2.2.1,x.2.1)):=divisionNewR.pair divisionDen
 def divisionTest:Realizer (fun x:DivisionInput => BinarySubtract.less (x.1::x.2.2.1) x.2.1):=
   divisionPair.comp BinarySubtract.lessRealizer
 def divisionRemainder:Realizer (fun x:DivisionInput =>
     if BinarySubtract.less (x.1::x.2.2.1) x.2.1 then trim (x.1::x.2.2.1) else BinarySubtract.difference (x.1::x.2.2.1) x.2.1):=
   (divisionTest.pair divisionPair).comp ((Realizer.fst.comp trimRealizer).choose BinarySubtract.differenceRealizer)
 def divisionQ:Realizer (fun x:DivisionInput => (!BinarySubtract.less (x.1::x.2.2.1) x.2.1)::x.2.2.2):=
   ((divisionTest.comp Realizer.not).pair divisionOldQ).comp Realizer.cons
 def divideStepRealizer:Realizer divideStep:=
   (divisionDen.pair (divisionRemainder.pair divisionQ)).congr (fun x => by
     rcases x with ⟨b,B,R,Q⟩
     cases h:BinarySubtract.less (b::R) B <;> simp [divideStep,h])
 def divideInitial:Realizer (fun x:List Bool×List Bool => (x.1.reverse,(x.2,(([]:List Bool),([]:List Bool))))):=
   (Realizer.fst.comp Realizer.reverse).pair (Realizer.snd.pair (Realizer.nil.pair Realizer.nil))
 def divisionFinish:Realizer (fun x:DivisionState => (trim x.2.2,trim x.2.1)):=
   ((Realizer.snd.comp Realizer.snd).comp trimRealizer).pair ((Realizer.snd.comp Realizer.fst).comp trimRealizer)
 def divideRealizer:Realizer (fun x:List Bool×List Bool => divide x.1 x.2):=
   ((divideInitial.comp divideStepRealizer.fold).comp divisionFinish).congr (fun _ => rfl)

 theorem divideStep_polynomial:PolyBound divideStepRealizer:=by
   have hden:PolyBound divisionDen:=linear_polynomial (linear_comp linear_snd linear_fst)
   have hr:PolyBound divisionOldR:=linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst)
   have hq:PolyBound divisionOldQ:=linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd)
   have hnew:PolyBound divisionNewR:=polynomial_comp (polynomial_pair (linear_polynomial linear_fst) hr) (linear_polynomial linear_cons)
   have hp:PolyBound divisionPair:=polynomial_pair hnew hden
   have ht:PolyBound divisionTest:=polynomial_comp hp BinarySubtract.less_polynomial
   have hrem:PolyBound divisionRemainder:=polynomial_comp (polynomial_pair ht hp)
     (polynomial_choose (polynomial_comp (linear_polynomial linear_fst) trim_polynomial) BinarySubtract.difference_polynomial)
   have hQ:PolyBound divisionQ:=polynomial_comp (polynomial_pair (polynomial_comp ht (linear_polynomial linear_not)) hq) (linear_polynomial linear_cons)
   unfold divideStepRealizer
   apply polynomial_congr
   exact polynomial_pair hden (polynomial_pair hrem hQ)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β:Type} [Coding α] [Coding β]

 theorem fold_prefix_bound {f:α×β→ β} (R:Realizer f) (xs:List α) (b:β) (T V:ℕ)
    (hvol:∀j,j≤xs.length→ volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤V)
    (htime:∀j (hj:j<xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤T):
    Realizer.foldTime R b xs≤xs.length*(T+20*(volume xs+2*V+1))+1:=by
   induction xs generalizing b with
   | nil => simp [Realizer.foldTime]
   | cons a xs ih =>
     have hb:volume b≤V:=by simpa using hvol 0 (by simp)
     have hb':volume (f (a,b))≤V:=by simpa using hvol 1 (by simp)
     have ht:R.time (a,b)≤T:=by
       have ht0:=htime 0 (by simp)
       change R.time (a,b)≤T at ht0
       exact ht0
     have hvol':∀j,j≤xs.length→ volume ((xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤V:=by
       intro j hj
       have hh:=hvol (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons] using hh
     have htime':∀j (hj:j<xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤T:=by
       intro j hj
       have hh:=htime (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons,List.getElem_cons_succ] using hh
     have hh:=ih (f (a,b)) hvol' htime'
     simp only [Realizer.foldTime,List.length_cons] at hh ⊢
     have hvolxs:volume xs≤volume (a::xs):=by simp only [volume_cons]; omega
     have hbound:xs.length*(T+20*(volume xs+2*V+1))≤xs.length*(T+20*(volume (a::xs)+2*V+1)):=
       Nat.mul_le_mul_left _ (by omega)
     nlinarith only [hh,ht,hb,hb',hbound]

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {β:Type} [Coding β]

 theorem bit_fold_envelope {f:Bool×β→ β} (R:Realizer f) (C q:ℕ)
    (htime:∀x,R.time x≤C*(volume x+1)^q)
    (xs:List Bool) (acc:β) (z:ℕ) (hz:1≤z) (hlen:xs.length≤z)
    (hxs:volume xs≤5*z)
    (hvol:∀j,j≤xs.length→ volume ((xs.take j).foldl (fun b a => f (a,b)) acc)≤12*z):
    R.fold.time (xs,acc)≤(C*17^q+2000)*z^(q+2):=by
   have hT (j:ℕ) (hj:j<xs.length):R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)≤C*17^q*z^q:=by
     have hh:=htime (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)
     have hb:=volume_bool xs[j]
     have hs:=hvol j hj.le
     have hv:volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)+1≤17*z:=by simp only [volume_pair]; omega
     have ht:=hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hv q))
     simpa only [mul_pow,Nat.mul_assoc] using ht
   have hf:=fold_prefix_bound R xs acc (C*17^q*z^q) (12*z) hvol hT
   have hq1:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hq2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hzgrow:z≤z^2:=by nlinarith
   have hmul:xs.length*(C*17^q*z^q+20*(volume xs+2*(12*z)+1))≤z*(C*17^q*z^q+600*z):=Nat.mul_le_mul hlen (by omega)
   have hqprod:z*(C*17^q*z^q)=C*17^q*z^(q+1):=by rw [pow_succ]; ring
   have hf':Realizer.foldTime R acc xs≤(C*17^q+1000)*z^(q+2):=by
     have ht:=Nat.mul_le_mul_left (C*17^q) hq1
     have hc:=Nat.mul_le_mul_left 1000 hq2
     simp only [Nat.mul_add,hqprod] at hmul
     nlinarith only [hf,hmul,ht,hc,hzgrow,hz]
   have hacc:volume acc≤12*z:=by simpa only [List.take_zero,List.foldl_nil] using hvol 0 (by omega)
   have hpow:z≤z^(q+2):=hzgrow.trans hq2
   rw [Realizer.time_fold]
   simp only [volume_pair]
   nlinarith only [hf',hxs,hacc,hpow,hz]

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem division_prefix_volume (A B:List Bool) (j:ℕ) (hj:j≤A.length):
     volume ((A.reverse.take j).foldl (fun s b => divideStep (b,s)) (B,([],[])))≤12*(A.length+B.length+1):=by
   let L:=A.reverse.take j
   let s:=L.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hb:=divide_fold_base L B [] []
   have hr:=divide_fold_rlength L B [] []
   have hq:=divide_fold_qlength L B [] []
   have hlen:L.length≤A.length:=by dsimp [L]; simp only [List.length_take,List.length_reverse]; omega
   change s.1=B at hb
   change s.2.1.length≤[].length+L.length at hr
   change s.2.2.length=[].length+L.length at hq
   simp only [List.length_nil,Nat.zero_add] at hr hq
   have hvB:=BinaryAdder.volume_bits s.1
   have hvR:=BinaryAdder.volume_bits s.2.1
   have hvQ:=BinaryAdder.volume_bits s.2.2
   rw [hb] at hvB
   change volume (s.1,(s.2.1,s.2.2))≤_
   simp only [volume_pair]
   rw [hb]
   omega

 theorem division_fold_time:∃ C q:ℕ,0<C∧ ∀ A B:List Bool,
     divideStepRealizer.fold.time (A.reverse,(B,([],[])))≤C*(A.length+B.length+1)^q:=by
   obtain ⟨C,q,hC,hR⟩:=divideStep_polynomial
   refine ⟨C*17^q+2000,q+2,by positivity,?_⟩
   intro A B
   apply bit_fold_envelope divideStepRealizer C q (fun x => (hR x).1)
   · omega
   · simp only [List.length_reverse]; omega
   · rw [volume_reverse]
     have hA:=BinaryAdder.volume_bits A
     omega
   · intro j hj
     exact division_prefix_volume A B j (by simpa only [List.length_reverse] using hj)

 theorem divideInitial_polynomial:PolyBound divideInitial:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List Bool×List Bool => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (polynomial_pair (linear_polynomial linear_snd) (polynomial_pair (linear_polynomial hn) (linear_polynomial hn)))

 theorem divisionFinish_polynomial:PolyBound divisionFinish:=
   polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) trim_polynomial)
     (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)

 theorem divide_time:∃ C q:ℕ,0<C∧ ∀ A B:List Bool,
     divideRealizer.time (A,B)≤C*(A.length+B.length+1)^q:=by
   obtain ⟨C,q,hC,hfold⟩:=division_fold_time
   obtain ⟨I,p,hI,hinit⟩:=divideInitial_polynomial
   obtain ⟨D,r,hD,hpost⟩:=divisionFinish_polynomial
   let e:=p+q+r+2
   refine ⟨I*5^p+C+D*13^r+1000,e,by positivity,?_⟩
   intro A B
   let z:=A.length+B.length+1
   let initial:List Bool×DivisionState:=(A.reverse,(B,([],[])))
   let final:=A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hz:1≤z:=by dsimp [z]; omega
   have hp:z^p≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq:z^q≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr:z^r≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze:z≤z^e:=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega:1≤e)
   have hA:=BinaryAdder.volume_bits A
   have hB:=BinaryAdder.volume_bits B
   have hvx:volume (A,B)+1≤5*z:=by simp only [volume_pair]; dsimp [z]; omega
   have hvi:volume initial≤7*z:=by dsimp [initial]; simp only [volume_pair,volume_nil,volume_reverse]; dsimp [z]; omega
   have hvf:volume final≤12*z:=by
     have hh:=division_prefix_volume A B A.length le_rfl
     rw [← List.length_reverse (as:=A),List.take_length] at hh
     simpa only [List.length_reverse] using hh
   have hi:divideInitial.time (A,B)≤I*5^p*z^e:=by
     have hh:=((hinit (A,B)).1).trans (Nat.mul_le_mul_left I (Nat.pow_le_pow_left hvx p))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (I*5^p) hp)
   have hf:divideStepRealizer.fold.time initial≤C*z^e:=(hfold A B).trans (Nat.mul_le_mul_left C hq)
   have ho:divisionFinish.time final≤D*13^r*z^e:=by
     have hh:=((hpost final).1).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left (show volume final+1≤13*z by omega) r))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*13^r) hr)
   have hcopy:10*(volume initial+1)+10*(volume final+1)≤1000*z^e:=by omega
   have heq:divideRealizer.time (A,B)=divideInitial.time (A,B)+divideStepRealizer.fold.time initial+
       10*(volume initial+1)+divisionFinish.time final+10*(volume final+1):=by
     dsimp only [divideRealizer,divide]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
     rfl
   rw [heq]
   change _≤(I*5^p+C+D*13^r+1000)*z^e
   nlinarith only [hi,hf,ho,hcopy]

 theorem divide_lengths (A B:List Bool):
     (divide A B).1.length≤A.length∧ (divide A B).2.length≤A.length:=by
   have hr:=divide_fold_rlength A.reverse B [] []
   have hq:=divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   exact ⟨(trim_length _).trans hq.le,(trim_length _).trans hr⟩

 theorem divide_polynomial:PolyBound divideRealizer:=by
   obtain ⟨C,q,hC,hT⟩:=divide_time
   refine ⟨C+12,q+1,by omega,?_⟩
   rintro ⟨A,B⟩
   let z:=volume (A,B)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hA:=bits_length_volume A
   have hB:=bits_length_volume B
   have hbase:A.length+B.length+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hp:(A.length+B.length+1)^q≤z^(q+1):=(Nat.pow_le_pow_left hbase q).trans (Nat.pow_le_pow_right hz (by omega))
   have ht:=(hT A B).trans (Nat.mul_le_mul_left C hp)
   have hvQ:=BinaryAdder.volume_bits (divide A B).1
   have hvR:=BinaryAdder.volume_bits (divide A B).2
   have hlen:=divide_lengths A B
   have hpow:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume ((divide A B).1,(divide A B).2)≤_
     simp only [volume_pair]
     have hv:volume (divide A B).1+volume (divide A B).2+1≤12*z^(q+1):=by omega
     simpa only [z,volume_pair] using hv.trans (Nat.mul_le_mul_right (z^(q+1)) (show 12≤C+12 from Nat.le_add_left _ _))

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 theorem polynomial_iterate_bounded {f:α→ α} {R:Realizer f} (hR:PolyBound R) (E:ℕ)
    (hg:∀x j,volume (f^[j] x)≤E*(volume x+1)):PolyBound R.iterate:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   let F:=C*(E+1)^q
   refine ⟨100000*(F+E+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z:=volume (n,a)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hn:n+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha:volume a+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hV (j:ℕ) (_hj:j≤n):volume (f^[j] a)≤E*z:=
     (hg a j).trans (Nat.mul_le_mul_left E ha)
   have hT (j:ℕ) (hj:j<n):R.time (f^[j] a)≤F*z^q:=by
     have hh:=(hR (f^[j] a)).1
     have hv:=hV j hj.le
     have hbase:volume (f^[j] a)+1≤(E+1)*z:=by nlinarith
     have ht:=hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht:=Realizer.time_iterate_le R n a (F*z^q) (E*z) hT hV
   have hq:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hq2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hze:z≤z^(q+2):=(show z≤z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+E+10)*z^(q+2)
     have hmul:(n+1)*(F*z^q+E*z+n+1)≤z*(F*z^q+(E+3)*z):=Nat.mul_le_mul hn (by nlinarith)
     have hmul':=Nat.mul_le_mul_left 10000 hmul
     have hp1:=Nat.mul_le_mul_left (10000*F) hq
     have hp2:=Nat.mul_le_mul_left (10000*(E+3)) hq2
     have hs:R.iterate.time (n,a)≤(10000*F+10000*(E+3))*z^(q+2):=by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     exact hs.trans (Nat.mul_le_mul_right _ (iterate_coefficient F E))
   · change volume (f^[n] a)≤100000*(F+E+10)*z^(q+2)
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left E hze).trans
       (Nat.mul_le_mul_right _ (by have:=iterate_output_coefficient F E; omega)))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack.BinaryGcd
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def stepRealizer:Realizer step:=
   (((Realizer.snd.comp nonemptyBits).pair Realizer.id).comp
     ((Realizer.snd.pair (divideRealizer.comp Realizer.snd)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨A,B⟩
       cases B <;> simp [step,nonemptyBits])

 theorem step_polynomial:PolyBound stepRealizer:=by
   unfold stepRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (linear_polynomial (linear_comp linear_snd nonempty_linear)) (linear_polynomial linear_id))
     (polynomial_choose (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_comp divide_polynomial (linear_polynomial linear_snd))) (linear_polynomial linear_id))

 theorem iterate_volume (s:List Bool×List Bool) (t:ℕ):volume (step^[t] s)≤5*(volume s+1):=by
   rcases s with ⟨A,B⟩
   have hlen:=length_iter (A,B) t
   dsimp only at hlen
   have hA:=bits_length_volume A
   have hB:=bits_length_volume B
   have hvA:=BinaryAdder.volume_bits (step^[t] (A,B)).1
   have hvB:=BinaryAdder.volume_bits (step^[t] (A,B)).2
   change volume ((step^[t] (A,B)).1,(step^[t] (A,B)).2)≤_
   simp only [volume_pair]
   omega

 theorem iterate_polynomial:PolyBound stepRealizer.iterate:=
   polynomial_iterate_bounded step_polynomial 5 iterate_volume

 def iterationCount:Realizer (fun s:List Bool×List Bool => 2*s.2.length):=
   ((Realizer.snd.comp BinaryAdder.wordLength).pair (Realizer.snd.comp BinaryAdder.wordLength)).comp Realizer.add
     |>.congr (fun s => by dsimp only [Function.comp_apply]; omega)
 def initialRealizer:Realizer (fun s:List Bool×List Bool => (trim s.1,trim s.2)):=
   (Realizer.fst.comp trimRealizer).pair (Realizer.snd.comp trimRealizer)
 def runRealizer:Realizer (fun s:List Bool×List Bool => run s.1 s.2):=
   ((iterationCount.pair initialRealizer).comp stepRealizer.iterate).congr (fun _ => rfl)
 def gcdRealizer:Realizer (fun s:List Bool×List Bool => gcd s.1 s.2):=runRealizer.comp Realizer.fst

 theorem wordLength_polynomial:PolyBound BinaryAdder.wordLength:=by
   refine ⟨1000002,2,by omega,?_⟩
   intro A
   have ht:=BinaryAdder.wordLength_time A
   have hlen:=bits_length_volume A
   have hp:=Nat.pow_le_pow_left (show A.length+1≤volume A+1 by omega) 2
   have hz:1≤volume A+1:=by omega
   have hpow:volume A+1≤(volume A+1)^2:=by nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 1000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · simp only [volume_nat]
     omega

 theorem nat_add_polynomial:PolyBound Realizer.add:=by
   refine ⟨10000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht:=Realizer.time_add_le a b
   have hbase:a+b+1≤volume (a,b)+1:=by simp only [volume_pair,volume_nat]; omega
   have hp:=Nat.pow_le_pow_left hbase 2
   have hv:volume (a+b)≤2*(volume (a,b)+1)^2:=by
     simp only [volume_nat,volume_pair]
     nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 10000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · exact hv.trans (Nat.mul_le_mul_right _ (by omega))

 theorem iterationCount_polynomial:PolyBound iterationCount:=by
   unfold iterationCount
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial)
       (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial))
     nat_add_polynomial

 theorem initial_polynomial:PolyBound initialRealizer:=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) trim_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) trim_polynomial)

 theorem gcd_polynomial:PolyBound gcdRealizer:=by
   apply polynomial_comp _ (linear_polynomial linear_fst)
   unfold runRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair iterationCount_polynomial initial_polynomial) iterate_polynomial

end EdgeSublinearMWIS.Main.RawStack.BinaryGcd

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def normalizeWords (A B:List Bool):List Bool×List Bool:=
   let D:=BinaryGcd.gcd A B
   ((divide A D).1,(divide B D).1)

 def gcdArguments:Realizer (fun x:List Bool×List Bool => (x,BinaryGcd.gcd x.1 x.2)):=
   Realizer.id.pair BinaryGcd.gcdRealizer
 def normalizeFirst:Realizer (fun x:(List Bool×List Bool)×List Bool => (divide x.1.1 x.2).1):=
   (((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeSecond:Realizer (fun x:(List Bool×List Bool)×List Bool => (divide x.1.2 x.2).1):=
   (((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeWordsRealizer:Realizer (fun x:List Bool×List Bool => normalizeWords x.1 x.2):=
   (gcdArguments.comp (normalizeFirst.pair normalizeSecond)).congr (fun _ => rfl)

 theorem normalizeWords_polynomial:PolyBound normalizeWordsRealizer:=by
   have h1:PolyBound normalizeFirst:=polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   have h2:PolyBound normalizeSecond:=polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_snd)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   unfold normalizeWordsRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) BinaryGcd.gcd_polynomial) (polynomial_pair h1 h2)

 theorem normalizeWords_values (A B:List Bool) (hB:0<value B):
     value (normalizeWords A B).1=value A/(value A).gcd (value B)∧
     value (normalizeWords A B).2=value B/(value A).gcd (value B):=by
   have hD:0<value (BinaryGcd.gcd A B):=by rw [BinaryGcd.gcd_value]; exact Nat.gcd_pos_of_pos_right _ hB
   exact ⟨(divide_value A _ hD).1.trans (by rw [BinaryGcd.gcd_value]),
     (divide_value B _ hD).1.trans (by rw [BinaryGcd.gcd_value])⟩

 theorem normalizeWords_canonical (A B:List Bool):
     trim (normalizeWords A B).1=(normalizeWords A B).1∧ trim (normalizeWords A B).2=(normalizeWords A B).2:=
   ⟨trim_idem _,trim_idem _⟩

 def signedValue (b:Bool) (A:List Bool):ℤ:=if b then -(value A:ℤ) else value A

 theorem signedValue_natAbs (b:Bool) (A:List Bool):(signedValue b A).natAbs=value A:=by
   cases b <;> simp [signedValue]

 theorem normalized_rat_num_den (z:ℤ) (d:ℕ) (hd:0<d):
     ((z:ℚ)/d).num.natAbs=z.natAbs/(z.natAbs.gcd d)∧
     ((z:ℚ)/d).den=d/(z.natAbs.gcd d):=by
   have he:(z:ℚ)/(d:ℚ)=Rat.normalize z d (by omega):=by
     rw [Rat.normalize_eq_mkRat,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
     norm_cast
   rw [he,Rat.num_normalize,Rat.den_normalize]
   constructor
   · rw [Int.natAbs_ediv_of_dvd]
     · simp
     · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
   · rfl

 theorem normalizeWords_rat (b:Bool) (A B:List Bool) (hB:0<value B):
     (normalizeWords A B).1=natBits (((signedValue b A:ℚ)/value B).num.natAbs)∧
     (normalizeWords A B).2=natBits (((signedValue b A:ℚ)/value B).den):=by
   have hv:=normalizeWords_values A B hB
   have hr:=normalized_rat_num_den (signedValue b A) (value B) hB
   rw [signedValue_natAbs] at hr
   have hc:=normalizeWords_canonical A B
   constructor
   · rw [canonical_eq_natBits _ hc.1,hv.1,← hr.1]
   · rw [canonical_eq_natBits _ hc.2,hv.2,← hr.2]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def appendBits:Realizer (fun x:List Bool×List Bool => x.1++x.2):=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun x => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

 theorem cons_fold_polynomial:PolyBound (Realizer.cons:Realizer (fun x:Bool×List Bool => x.1::x.2)).fold:=by
   refine ⟨100000,3,by omega,?_⟩
   rintro ⟨A,B⟩
   let z:=A.length+B.length+1
   have hz:1≤z:=by dsimp [z]; omega
   have hvol:∀j,j≤A.length→ volume ((A.take j).foldl (fun s b => b::s) B)≤12*z:=by
     intro j hj
     rw [Realizer.fold_cons_eq]
     have hv:=BinaryAdder.volume_bits ((A.take j).reverse++B)
     simp only [List.length_append,List.length_reverse,List.length_take] at hv
     dsimp [z]
     omega
   have ht:=bit_fold_envelope (Realizer.cons:Realizer (fun x:Bool×List Bool => x.1::x.2)) 3 1
     (fun x => by change volume x+2≤3*(volume x+1)^1; simp only [pow_one]; omega) A B z hz (by dsimp [z]; omega)
     (by have hh:=BinaryAdder.volume_bits A; dsimp [z]; omega) hvol
   have hbase:z≤volume (A,B)+1:=by
     have hA:=bits_length_volume A
     have hB:=bits_length_volume B
     dsimp [z]; simp only [volume_pair]; omega
   have hp:=Nat.pow_le_pow_left hbase 3
   constructor
   · have he:3*17^1+2000≤100000:=by norm_num
     exact ht.trans ((Nat.mul_le_mul_left _ hp).trans (Nat.mul_le_mul_right _ he))
   · change volume (A.foldl (fun s b => b::s) B)≤_
     have hv:=hvol A.length le_rfl
     rw [List.take_length] at hv
     have hh:z≤(volume (A,B)+1)^3:=hbase.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1≤volume (A,B)+1) (by omega:1≤3))
     have hs:volume (A.foldl (fun s b => b::s) B)≤12*(volume (A,B)+1)^3:=by omega
     exact hs.trans (Nat.mul_le_mul_right _ (by omega))

 theorem appendBits_polynomial:PolyBound appendBits:=by
   unfold appendBits
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (linear_polynomial linear_snd)) cons_fold_polynomial

 def prependTrue:Realizer (fun L:List Bool => true::L):=((Realizer.constant true).pair Realizer.id).comp Realizer.cons
 theorem prependTrue_linear:Linear prependTrue:=by
   have ht:Linear (Realizer.constant true:Realizer (fun _:List Bool => true)):=linear_bool _ 2000 (fun L => by change (2*3+1)*(20*volume L+50*3+50)≤_; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def replicateTrue:Realizer (fun n:ℕ => List.replicate n true):=
   ((Realizer.id.pair Realizer.nil).comp prependTrue.iterate).congr (fun n => by
     change (fun L:List Bool => true::L)^[n] []=List.replicate n true
     induction n with
     | zero => rfl
     | succ n ih => rw [Function.iterate_succ_apply',ih,List.replicate_succ])
 theorem replicateTrue_polynomial:PolyBound replicateTrue:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:ℕ => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold replicateTrue
   apply polynomial_congr
   apply polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
   exact polynomial_iterate (linear_polynomial prependTrue_linear) 4 (fun L => by simp only [volume_cons,volume_bool_true]; omega)

 def prefixBits (A:List Bool):List Bool:=List.replicate A.length true++false::A
 def falseCons:Realizer (fun L:List Bool => false::L):=(Realizer.false.pair Realizer.id).comp Realizer.cons
 theorem falseCons_linear:Linear falseCons:=by
   have ht:Linear (Realizer.false:Realizer (fun _:List Bool => false)):=linear_bool _ 3 (fun _ => by change 2≤_; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def prefixRealizer:Realizer prefixBits:=
   ((BinaryAdder.wordLength.comp replicateTrue).pair falseCons).comp appendBits
 theorem prefix_polynomial:PolyBound prefixRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp BinaryGcd.wordLength_polynomial replicateTrue_polynomial)
     (linear_polynomial falseCons_linear)) appendBits_polynomial

 theorem prefix_natBits (n:ℕ):prefixBits (natBits n)=encodeNat n:=by
   simp only [prefixBits,encodeNat,List.append_assoc,List.singleton_append]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedWords:=Bool×(List Bool×List Bool)
 def rationalSign (s:SignedWords):Bool:=s.1 && !(trim s.2.1).isEmpty

 def signRealizer:Realizer rationalSign:=
   (Realizer.fst.pair (((Realizer.snd.comp Realizer.fst).comp trimRealizer).comp nonemptyBits)).comp Realizer.and
 def normalizedRealizer:Realizer (fun s:SignedWords => normalizeWords s.2.1 s.2.2):=Realizer.snd.comp normalizeWordsRealizer

 theorem rational_sign (b:Bool) (A B:List Bool) (hB:0<value B):
     rationalSign (b,(A,B))=decide ((((signedValue b A:ℚ)/value B).num)<0):=by
   have hv:(trim A).isEmpty=false↔ 0<value A:=by
     constructor
     · intro h
       have hn:trim A≠[]:=by intro he; simp [he] at h
       have hh:=BinaryGcd.value_positive (trim A) (trim_idem A) hn
       rwa [trim_value] at hh
     · intro h
       cases he:trim A with
       | nil => have hh:=trim_value A; rw [he] at hh; simp [value] at hh; omega
       | cons a L => rfl
   have hneg:(((signedValue b A:ℚ)/value B).num<0)↔ b=true∧ 0<value A:=by
     have hp:(0:ℚ)<value B:=by exact_mod_cast hB
     rw [Rat.num_neg,div_neg_iff]
     cases b <;> simp [signedValue,hp,not_lt_of_gt hp]
   cases b <;> cases he:(trim A).isEmpty <;> simp_all [rationalSign]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def takeWordStep (s:List Bool×List Bool):List Bool×List Bool:=
   if s.1.isEmpty then s else (s.1.tail,s.1.headD false::s.2)
 def takeWordStepRealizer:Realizer takeWordStep:=
   (((Realizer.fst.comp nonemptyBits).pair Realizer.id).comp
     (((Realizer.fst.comp BinaryAdder.tailBits).pair
       (((Realizer.fst.comp BinaryAdder.headBit).pair Realizer.snd).comp Realizer.cons)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨L,R⟩
       cases L <;> rfl)

 theorem takeWordStep_linear:Linear takeWordStepRealizer:=by
   unfold takeWordStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair (linear_comp linear_fst nonempty_linear) linear_id)
     (linear_choose (linear_pair (linear_comp linear_fst BinaryAdder.tailBits_linear)
       (linear_comp (linear_pair (linear_comp linear_fst BinaryAdder.headBit_linear) linear_snd) linear_cons)) linear_id)

 theorem takeWordStep_volume (s:List Bool×List Bool):volume (takeWordStep s)≤volume s:=by
   rcases s with ⟨L,R⟩
   cases L with
   | nil => rfl
   | cons a L => simp only [takeWordStep,List.isEmpty_cons,Bool.false_eq_true,if_false,List.tail_cons,List.headD_cons,volume_pair,volume_cons]; omega

 theorem takeWordStep_iterate (L R:List Bool) (k:ℕ):
     takeWordStep^[k] (L,R)=(L.drop k,(L.take k).reverse++R):=by
   induction k generalizing L R with
   | zero => simp
   | succ k ih =>
     rw [Function.iterate_succ_apply]
     cases L with
     | nil => simpa only [takeWordStep,List.isEmpty_nil,if_true,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append] using ih [] R
     | cons a L =>
       change takeWordStep^[k] (L,a::R)=_
       rw [ih,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons]
       simp only [List.append_assoc,List.singleton_append]

 def splitWord (L:List Bool) (k:ℕ):List Bool×List Bool:=(L.take k,L.drop k)
 def splitWordRealizer:Realizer (fun x:List Bool×ℕ => splitWord x.1 x.2):=
   (((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp takeWordStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst)).congr (fun x => by
       dsimp only [Function.comp_apply,splitWord]
       rw [takeWordStep_iterate]
       simp)

 theorem splitWord_polynomial:PolyBound splitWordRealizer:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List Bool×ℕ => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   have hi:=polynomial_iterate (linear_polynomial takeWordStep_linear) 0 (fun x => by simpa only [Nat.add_zero] using takeWordStep_volume x)
   unfold splitWordRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_pair (linear_polynomial linear_fst) (linear_polynomial hn))) hi)
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial) (linear_polynomial linear_fst))

 def readWord (L:List Bool):List Bool×List Bool:=
   let k:=(L.takeWhile id).length
   splitWord (L.drop (k+1)) k

 theorem readWord_prefix (A rest:List Bool):readWord (prefixBits A++rest)=(A,rest):=by
   have hk:((prefixBits A++rest).takeWhile id).length=A.length:=by
     simp only [prefixBits,List.append_assoc]
     have h (n:ℕ):((List.replicate n true++false::(A++rest)).takeWhile id).length=n:=by
       induction n with
       | zero => simp
       | succ n ih => simpa using congrArg Nat.succ ih
     exact h A.length
   dsimp only [readWord]
   rw [hk]
   have hd:(prefixBits A++rest).drop (A.length+1)=A++rest:=by
     simp only [prefixBits,List.append_assoc]
     rw [← List.drop_drop,List.drop_left' (by simp)]
     rfl
   rw [hd]
   simp only [splitWord,List.take_left,List.drop_left]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β:Type} [Coding α] [Coding β]

 theorem linear_constant (b:β):Linear (Realizer.constant b:Realizer (fun _:α => b)):=by
   let C:=(2*volume b+1)*(50*volume b+70)+volume b+1
   refine linear_of _ C (by dsimp [C]; positivity) ?_ ?_
   · intro x
     change (2*volume b+1)*(20*volume x+50*volume b+50)≤C*(volume x+1)
     have hb:20*volume x+50*volume b+50≤(50*volume b+70)*(volume x+1):=by
       nlinarith [Nat.zero_le (volume b*volume x)]
     have hh:=Nat.mul_le_mul_left (2*volume b+1) hb
     have hc:(2*volume b+1)*(50*volume b+70)≤C:=by dsimp [C]; omega
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (volume x+1) hc)
   · intro x
     change volume b≤C*(volume x+1)
     have hc:volume b≤C:=by dsimp [C]; omega
     exact hc.trans (Nat.le_mul_of_pos_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def leadingStepRealizer:Realizer Binary.leadingStep:=(Uniform.binaryLeadingStep (I:=Unit)).specialize ()
 theorem leadingStep_polynomial:PolyBound leadingStepRealizer:=by
   obtain ⟨C,hC⟩:=Costs.leadingStepCost
   refine ⟨C+10,1,by omega,?_⟩
   rintro ⟨a,b,k⟩
   have ht:=hC (a,(b,k))
   simp only [pow_one] at ht
   have hbase:k+2≤volume (a,(b,k))+1:=by simp only [volume_pair,volume_nat]; omega
   have hv:volume (Binary.leadingStep (a,(b,k)))≤volume (a,(b,k))+5:=by
     cases a <;> cases b <;> simp [Binary.leadingStep,volume_pair,volume_nat] <;> omega
   constructor
   · change _≤(C+10)*(volume (a,(b,k))+1)^1
     rw [pow_one]
     exact ht.trans ((Nat.mul_le_mul_left C hbase).trans (by nlinarith))
   · rw [pow_one]
     nlinarith

 theorem leading_fold_volume (L:List Bool) (b:Bool) (k:ℕ):
     volume (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤2*(k+L.length)+5:=by
   have hc:=Binary.leading_fold L b k
   have hlen:Binary.leading L≤L.length:=by exact (List.takeWhile_sublist _).length_le
   have hb:=volume_bool (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).1
   change volume ((L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).1,
     (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k)).2)≤_
   simp only [volume_pair,volume_nat,hc]
   split_ifs <;> omega

 theorem leading_fold_polynomial:PolyBound leadingStepRealizer.fold:=by
   obtain ⟨C,q,hC,hR⟩:=leadingStep_polynomial
   refine ⟨C*17^q+2010,q+2,by positivity,?_⟩
   rintro ⟨L,b,k⟩
   let z:=volume (L,(b,k))+1
   have hz:1≤z:=by dsimp [z]; omega
   have hL:=bits_length_volume L
   have hbase:k+L.length+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hvol:∀j,j≤L.length→ volume ((L.take j).foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤12*z:=by
     intro j hj
     have hh:=leading_fold_volume (L.take j) b k
     simp only [List.length_take] at hh
     omega
   have ht:=bit_fold_envelope leadingStepRealizer C q (fun x => (hR x).1) L (b,k) z hz
     (by omega) (by dsimp [z]; simp only [volume_pair]; omega) hvol
   have hv:=hvol L.length le_rfl
   rw [List.take_length] at hv
   have hp:z≤z^(q+2):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+2)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (L.foldl (fun s a => Binary.leadingStep (a,s)) (b,k))≤_
     exact hv.trans ((Nat.mul_le_mul_left 12 hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def leadingRealizer:Realizer (fun L:List Bool => (L.takeWhile id).length):=
   (((Realizer.id.pair (Realizer.constant (true,0))).comp leadingStepRealizer.fold).comp Realizer.snd).congr
     (fun L => by simpa only [Function.comp_apply,id_eq,Nat.zero_add,ite_true,Binary.leading] using Binary.leading_fold L true 0)
 theorem leading_polynomial:PolyBound leadingRealizer:=by
   unfold leadingRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant (true,0)))) leading_fold_polynomial) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem succ_linear:Linear Realizer.succ:=by
   refine linear_of _ 300 (by omega) (fun n => (Realizer.time_succ_le n).trans (by simp only [volume_nat]; omega)) ?_
   intro n
   simp only [volume_nat]
   omega

 def skipPrefixRealizer:Realizer (fun L:List Bool => L.drop ((L.takeWhile id).length+1)):=
   (((Realizer.id.pair (leadingRealizer.comp Realizer.succ)).comp splitWordRealizer).comp Realizer.snd).congr (fun _ => rfl)
 def readWordRealizer:Realizer readWord:=
   ((skipPrefixRealizer.pair leadingRealizer).comp splitWordRealizer).congr (fun _ => rfl)
 theorem skipPrefix_polynomial:PolyBound skipPrefixRealizer:=by
   unfold skipPrefixRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp
     (polynomial_pair (linear_polynomial linear_id) (polynomial_comp leading_polynomial (linear_polynomial succ_linear)))
     splitWord_polynomial) (linear_polynomial linear_snd)
 theorem readWord_polynomial:PolyBound readWordRealizer:=by
   unfold readWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair skipPrefix_polynomial leading_polynomial) splitWord_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readRational (L:List Bool):SignedWords×List Bool:=
   let A:=readWord L.tail
   let B:=readWord A.2
   ((L.headD false,(A.1,B.1)),B.2)
 def numeratorRealizer:Realizer (fun L:List Bool => readWord L.tail):=BinaryAdder.tailBits.comp readWordRealizer
 def denominatorRealizer:Realizer (fun L:List Bool => readWord (readWord L.tail).2):=
   (numeratorRealizer.comp Realizer.snd).comp readWordRealizer
 def readRationalRealizer:Realizer readRational:=
   (BinaryAdder.headBit.pair ((numeratorRealizer.comp Realizer.fst).pair (denominatorRealizer.comp Realizer.fst))).pair
     (denominatorRealizer.comp Realizer.snd)
 theorem readRational_polynomial:PolyBound readRationalRealizer:=by
   have hn:PolyBound numeratorRealizer:=polynomial_comp (linear_polynomial BinaryAdder.tailBits_linear) readWord_polynomial
   have hd:PolyBound denominatorRealizer:=polynomial_comp (polynomial_comp hn (linear_polynomial linear_snd)) readWord_polynomial
   exact polynomial_pair (polynomial_pair (linear_polynomial BinaryAdder.headBit_linear)
     (polynomial_pair (polynomial_comp hn (linear_polynomial linear_fst)) (polynomial_comp hd (linear_polynomial linear_fst))))
     (polynomial_comp hd (linear_polynomial linear_snd))

 theorem readRational_prefix (b:Bool) (A B rest:List Bool):
     readRational (b::(prefixBits A++prefixBits B++rest))=((b,(A,B)),rest):=by
   simp only [readRational,List.tail_cons,List.headD_cons,List.append_assoc,readWord_prefix]

 theorem readRational_code (q:RationalCode) (rest:List Bool):
     readRational (q.bits++rest)=((decide (q.numerator<0),(natBits q.numerator.natAbs,natBits q.denominator)),rest):=by
   have he:q.bits++rest=decide (q.numerator<0)::
       (prefixBits (natBits q.numerator.natAbs)++prefixBits (natBits q.denominator)++rest):=by
     simp only [RationalCode.bits,encodeInt,prefix_natBits,List.singleton_append,List.cons_append,List.append_assoc,List.nil_append]
   rw [he,readRational_prefix]

 theorem signedValue_encode (z:ℤ):signedValue (decide (z<0)) (natBits z.natAbs)=z:=by
   cases z <;> simp [signedValue,value_natBits] <;> omega

end EdgeSublinearMWIS.Main.RawStack

end
end

section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def capStep (x:Bool×(ℕ×ℕ)):ℕ×ℕ:=(min x.2.2 (2*x.2.1+x.1.toNat),x.2.2)

 theorem capStep_first (b:Bool) (v c:ℕ):(capStep (b,(v,c))).1≤c:=Nat.min_le_left _ _
 theorem capFold_second (L:List Bool) (v c:ℕ):
     (L.foldl (fun s b => capStep (b,s)) (v,c)).2=c:=by
   induction L generalizing v with
   | nil => rfl
   | cons b L ih => exact ih _
 theorem capFold_bound (L:List Bool) (v c:ℕ):
     (L.foldl (fun s b => capStep (b,s)) (v,c)).1≤v+c:=by
   cases L with
   | nil => simp
   | cons b L =>
     have h (L:List Bool) (v:ℕ) (hv:v≤c):(L.foldl (fun s b => capStep (b,s)) (v,c)).1≤c:=by
       induction L generalizing v with
       | nil => exact hv
       | cons b L ih => exact ih _ (capStep_first b v c)
     exact (h L _ (capStep_first b v c)).trans (by omega)

 theorem capFold_value (L:List Bool) (v c:ℕ) (hv:v≤c):
     (L.foldl (fun s b => capStep (b,s)) (v,c)).1=min c (value L.reverse+2^L.length*v):=by
   induction L generalizing v with
   | nil => simp only [List.foldl_nil,List.reverse_nil,value,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add,Nat.min_eq_right hv]
   | cons b L ih =>
     rw [List.foldl_cons]
     change (L.foldl (fun s b => capStep (b,s)) (min c (2*v+b.toNat),c)).1=_
     rw [ih _ (Nat.min_le_left _ _),List.reverse_cons,BinaryAdder.value_append]
     simp only [value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     have h (X P v c:ℕ) (hP:1≤P):min c (X+P*min c v)=min c (X+P*v):=by
       by_cases hh:v≤c
       · rw [Nat.min_eq_right hh]
       · have hc:c≤v:=by omega
         rw [Nat.min_eq_left hc,Nat.min_eq_left (by nlinarith),Nat.min_eq_left (by nlinarith)]
     rw [h _ _ _ _ (one_le_pow₀ (by omega:1≤2))]
     congr 1
     ring

 def cappedValue (A:List Bool) (c:ℕ):ℕ:=
   (A.reverse.foldl (fun s b => capStep (b,s)) (0,c)).1
 theorem cappedValue_eq (A:List Bool) (c:ℕ):cappedValue A c=min c (value A):=by
   have hh:=capFold_value A.reverse 0 c (by omega)
   simpa only [cappedValue,List.reverse_reverse,Nat.mul_zero,Nat.add_zero] using hh

end EdgeSublinearMWIS.Main.RawStack

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem realizer_poly_program {f:List Bool→ List Bool} (R:Realizer f) (hR:PolyBound R):
     ∃ (P:EdgeSublinearMWIS.Main.Program) (K q:ℕ),0<K∧ 0<q∧
       ∀ input,EdgeSublinearMWIS.Main.Runs P input (f input) (K*(input.length+1)^q):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨P,F,hF,hRuns⟩:=EdgeSublinearMWIS.Main.realizer_native_program f R
   refine ⟨P,F*(2*C*5^q+2),q+1,by positivity,by omega,?_⟩
   intro input
   have hRun:=hRuns input
   apply NativeCompiler.runs_mono _ _ _ hRun
   let z:=input.length+1
   have hz:1≤z:=by dsimp [z]; omega
   have hv:=EdgeSublinearMWIS.Main.BinaryAdder.volume_bits input
   have hi:volume input+1≤5*z:=by dsimp [z]; omega
   have hp:=Nat.pow_le_pow_left hi q
   rw [mul_pow] at hp
   have hq:z^q≤z^(q+1):=Nat.pow_le_pow_right hz (by omega)
   have hqp:(volume input+1)^q≤5^q*z^(q+1):=hp.trans (Nat.mul_le_mul_left _ hq)
   have ht:=((hR input).1).trans (Nat.mul_le_mul_left C hqp)
   have ho:=((hR input).2).trans (Nat.mul_le_mul_left C hqp)
   have hl:=EdgeSublinearMWIS.Main.RawStack.bits_length_volume (f input)
   have hze:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   change input.length+1≤z^(q+1) at hze
   have hs:R.time input+input.length+(f input).length+1≤(2*C*5^q+2)*z^(q+1):=by
     nlinarith only [ht,ho,hl,hze]
   change F*(R.time input+input.length+(f input).length+1)≤F*(2*C*5^q+2)*z^(q+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left F hs

end EdgeSublinearMWIS.Main.TreeToTM2

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def boolNat:Realizer Bool.toNat:=Realizer.reinterpret _ (by intro b; cases b <;> rfl)
 theorem boolNat_linear:Linear boolNat:=by
   refine linear_of _ 3 (by omega) (fun b => by change volume b+2≤_; omega) ?_
   intro b
   cases b <;> decide
 theorem nat_le_polynomial:PolyBound Realizer.le:=by
   refine ⟨1000000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht:=Realizer.time_le_le a b
   have hbase:a+b+1≤volume (a,b)+1:=by simp only [volume_pair,volume_nat]; omega
   have hp:=Nat.pow_le_pow_left hbase 2
   have hv:=volume_bool (decide (a≤b))
   have hz:1≤(volume (a,b)+1)^2:=one_le_pow₀ (by omega)
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 1000000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · change volume (decide (a≤b))≤_
     omega
 def minRealizer:Realizer (fun x:ℕ×ℕ => min x.1 x.2):=
   ((Realizer.le.pair Realizer.id).comp (Realizer.fst.choose Realizer.snd)).congr (fun x => by simp [min_def])
 theorem min_polynomial:PolyBound minRealizer:=by
   unfold minRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair nat_le_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_fst) (linear_polynomial linear_snd))

 def capCurrent:Realizer (fun x:Bool×(ℕ×ℕ) => x.2.1):=Realizer.snd.comp Realizer.fst
 def capLimit:Realizer (fun x:Bool×(ℕ×ℕ) => x.2.2):=Realizer.snd.comp Realizer.snd
 def capNext:Realizer (fun x:Bool×(ℕ×ℕ) => 2*x.2.1+x.1.toNat):=
   ((((capCurrent.pair capCurrent).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply]; omega)
 def capStepRealizer:Realizer capStep:=((capLimit.pair capNext).comp minRealizer).pair capLimit
 theorem capStep_polynomial:PolyBound capStepRealizer:=by
   have hc:PolyBound capCurrent:=linear_polynomial (linear_comp linear_snd linear_fst)
   have hl:PolyBound capLimit:=linear_polynomial (linear_comp linear_snd linear_snd)
   have hn:PolyBound capNext:=by
     unfold capNext
     apply polynomial_congr
     exact polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair hc hc) BinaryGcd.nat_add_polynomial)
       (linear_polynomial (linear_comp linear_fst boolNat_linear))) BinaryGcd.nat_add_polynomial
   exact polynomial_pair (polynomial_comp (polynomial_pair hl hn) min_polynomial) hl

 theorem capFold_volume (L:List Bool) (v c:ℕ):
     volume (L.foldl (fun s b => capStep (b,s)) (v,c))≤2*v+4*c+3:=by
   have h1:=capFold_bound L v c
   have h2:=capFold_second L v c
   change volume ((L.foldl (fun s b => capStep (b,s)) (v,c)).1,
     (L.foldl (fun s b => capStep (b,s)) (v,c)).2)≤_
   simp only [volume_pair,volume_nat,h2]
   omega
 theorem cap_fold_polynomial:PolyBound capStepRealizer.fold:=by
   obtain ⟨C,q,hC,hR⟩:=capStep_polynomial
   refine ⟨C*17^q+2010,q+2,by positivity,?_⟩
   rintro ⟨L,v,c⟩
   let z:=volume (L,(v,c))+1
   have hz:1≤z:=by dsimp [z]; omega
   have hL:=bits_length_volume L
   have hsmall:v+c+L.length+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hvol:∀j,j≤L.length→ volume ((L.take j).foldl (fun s b => capStep (b,s)) (v,c))≤12*z:=by
     intro j _
     have hh:=capFold_volume (L.take j) v c
     omega
   have ht:=bit_fold_envelope capStepRealizer C q (fun x => (hR x).1) L (v,c) z hz
     (by omega) (by dsimp [z]; simp only [volume_pair]; omega) hvol
   have hv:=hvol L.length le_rfl
   rw [List.take_length] at hv
   have hp:z≤z^(q+2):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+2)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (L.foldl (fun s b => capStep (b,s)) (v,c))≤_
     exact hv.trans ((Nat.mul_le_mul_left 12 hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def cappedValueRealizer:Realizer (fun x:List Bool×ℕ => cappedValue x.1 x.2):=
   (((Realizer.fst.comp Realizer.reverse).pair ((Realizer.constant 0).pair Realizer.snd)).comp capStepRealizer.fold).comp Realizer.fst
 theorem cappedValue_polynomial:PolyBound cappedValueRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (polynomial_pair (linear_polynomial (linear_constant (0:ℕ))) (linear_polynomial linear_snd))) cap_fold_polynomial)
     (linear_polynomial linear_fst)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem trim_volume (A:List Bool):volume (trim A)≤volume A:=by
   induction A with
   | nil => rfl
   | cons b A ih =>
     by_cases ht:trim A=[]
     · cases b <;> simp [trim,ht,volume_cons] <;> have hh:=volume_pos A <;> omega
     · simp only [trim,ht,if_false,volume_cons]
       omega
 theorem increment_volume (A:List Bool):volume (increment A)≤volume A+4:=by
   induction A with
   | nil => decide
   | cons b A ih => cases b <;> simp [increment,volume_cons] at * <;> omega

 def nextWord (A:List Bool):List Bool:=trim (BinaryAdder.word A [true])
 def nextWordRealizer:Realizer nextWord:=
   ((Realizer.id.pair (Realizer.constant [true])).comp BinaryAdder.wordRealizer).comp trimRealizer
 theorem nextWord_polynomial:PolyBound nextWordRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant [true]))) word_polynomial) trim_polynomial
 theorem nextWord_value (A:List Bool):value (nextWord A)=value A+1:=by
   rw [nextWord,trim_value,BinaryAdder.word_value]
   simp [value]
 theorem nextWord_canonical (A:List Bool):trim (nextWord A)=nextWord A:=trim_idem _
 theorem nextWord_eq (A:List Bool):nextWord A=trim (increment A):=by
   apply canonical_value_injective _ _ (nextWord_canonical A) (trim_idem _)
   rw [nextWord_value,trim_value,increment_value]
 theorem nextWord_volume (A:List Bool):volume (nextWord A)≤volume A+4:=by
   rw [nextWord_eq]
   exact (trim_volume _).trans (increment_volume A)
 theorem nextWord_iter_value (n:ℕ):value (nextWord^[n] [])=n:=by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',nextWord_value,ih]
 theorem nextWord_iter_canonical (n:ℕ):trim (nextWord^[n] [])=nextWord^[n] []:=by
   cases n with
   | zero => rfl
   | succ n => rw [Function.iterate_succ_apply']; exact nextWord_canonical _
 def naturalWordRealizer:Realizer natBits:=
   ((Realizer.id.pair Realizer.nil).comp nextWordRealizer.iterate).congr (fun n => by
     change nextWord^[n] []=natBits n
     rw [canonical_eq_natBits _ (nextWord_iter_canonical n),nextWord_iter_value])
 theorem naturalWord_polynomial:PolyBound naturalWordRealizer:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:ℕ => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold naturalWordRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
     (polynomial_iterate nextWord_polynomial 4 nextWord_volume)
 def naturalCodeRealizer:Realizer encodeNat:=(naturalWordRealizer.comp prefixRealizer).congr prefix_natBits
 theorem naturalCode_polynomial:PolyBound naturalCodeRealizer:=by
   unfold naturalCodeRealizer
   apply polynomial_congr
   exact polynomial_comp naturalWord_polynomial prefix_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

 theorem natBits_length (n:ℕ):(natBits n).length≤ n:=by
  simpa only [natBits,List.length_map] using
    (Nat.digits_length_le_iff (by decide:1 < 2) n).mpr (show n < 2 ^ n from Nat.lt_two_pow_self)

 theorem encodeNat_length (n:ℕ):(encodeNat n).length≤ 2 * n + 1:=by
  have h:=natBits_length n
  simp only [encodeNat,List.length_append,List.length_replicate,List.length_singleton]
  omega

 theorem rationalBits_length (r:RationalCode):1≤ r.bits.length:=by
  simp only [RationalCode.bits,encodeInt,List.length_append,List.length_singleton]
  omega

 theorem order_le_data {n:ℕ} (w:Fin n→ RationalCode) (ε:RationalCode):
    n≤ (rationalData w ε).length:=by
  have hsum:(∑ _v:Fin n,1)≤ ∑ v:Fin n, (w v).bits.length:=
    Finset.sum_le_sum (fun v hv => rationalBits_length (w v))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hsum
  have heq:(rationalData w ε).length=(∑ v, (w v).bits.length) + ε.bits.length:=by
    simp [rationalData,List.length_flatten,List.map_ofFn,List.sum_ofFn]
  omega

 theorem graphBits_length {n:ℕ} (G:SimpleGraph (Fin n)):
    (graphBits G).length≤ (n + 1) ^ 2:=by
  classical
  have hpart (u:Fin n):((List.finRange n).filter (fun v => u < v)).length≤ n:=by
    simpa using (List.length_filter_le (fun v:Fin n => decide (u < v)) (List.finRange n))
  have hsum:(∑ u:Fin n, ((List.finRange n).filter (fun v => u < v)).length)≤ n * n:=by
    calc
      _≤ ∑ _u:Fin n,n:=Finset.sum_le_sum (fun v hv => hpart v)
      _=n * n:=by simp
  have heq:(graphBits G).length=(encodeNat n).length +
      ∑ u:Fin n, ((List.finRange n).filter (fun v => u < v)).length:=by
    simp [graphBits,List.length_flatMap,List.finRange,List.map_ofFn,List.sum_ofFn]
  have henc:=encodeNat_length n
  nlinarith

 theorem input_length {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode) (ε:RationalCode):
    (weightedInput G w ε).length + 1≤ 3 * ((rationalData w ε).length + 1) ^ 2:=by
  have hn:=order_le_data w ε
  have hg:=graphBits_length G
  simp only [weightedInput,List.length_append]
  nlinarith

end EdgeSublinearMWIS.Main.EncodingBounds

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readNatural (L:List Bool):ℕ×List Bool:=
   let A:=readWord L
   (cappedValue A.1 (L.length+1),A.2)
 def parserCap:Realizer (fun L:List Bool => L.length+1):=BinaryAdder.wordLength.comp Realizer.succ
 def readNaturalRealizer:Realizer readNatural:=
   ((((readWordRealizer.comp Realizer.fst).pair parserCap).comp cappedValueRealizer).pair (readWordRealizer.comp Realizer.snd))
 theorem readNatural_polynomial:PolyBound readNaturalRealizer:=
   polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp readWord_polynomial (linear_polynomial linear_fst))
     (polynomial_comp BinaryGcd.wordLength_polynomial (linear_polynomial succ_linear))) cappedValue_polynomial)
     (polynomial_comp readWord_polynomial (linear_polynomial linear_snd))

 theorem readWord_encoded (n:ℕ) (rest:List Bool):readWord (encodeNat n++rest)=(natBits n,rest):=by
   rw [← prefix_natBits,readWord_prefix]
 theorem readNatural_encoded (n:ℕ) (rest:List Bool) (h:n≤(encodeNat n++rest).length+1):
     readNatural (encodeNat n++rest)=(n,rest):=by
   dsimp only [readNatural]
   rw [readWord_encoded,cappedValue_eq,value_natBits,Nat.min_eq_right h]

 theorem weighted_order_bound {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode) (ε:RationalCode):
     n≤(weightedInput G w ε).length+1:=by
   have h:=EncodingBounds.order_le_data w ε
   simp only [weightedInput,List.length_append]
   omega

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem volume_take_drop (L:List Bool) (k:ℕ):volume (L.take k)+volume (L.drop k)=volume L+1:=by
   have hh:=volume_append (L.take k) (L.drop k)
   rw [List.take_append_drop] at hh
   omega
 theorem volume_drop_le (L:List Bool) (k:ℕ):volume (L.drop k)≤volume L:=by
   have hh:=volume_take_drop L k
   have hp:=volume_pos (L.take k)
   omega
 theorem readWord_volume (L:List Bool):volume (readWord L).1+volume (readWord L).2≤volume L+1:=by
   dsimp only [readWord,splitWord]
   have hh:=volume_take_drop (L.drop ((L.takeWhile id).length+1)) ((L.takeWhile id).length)
   have hd:=volume_drop_le L ((L.takeWhile id).length+1)
   omega
 theorem readRational_volume (L:List Bool):volume (readRational L).1+volume (readRational L).2≤volume L+7:=by
   have hA:=readWord_volume L.tail
   have hB:=readWord_volume (readWord L.tail).2
   have ht:volume L.tail≤volume L:=by cases L <;> simp [volume_cons] <;> omega
   have hs:=volume_bool (L.headD false)
   dsimp only [readRational]
   simp only [volume_pair]
   omega

 abbrev BatchState:=List Bool×List SignedWords
 def batchStep (s:BatchState):BatchState:=
   let A:=readRational s.1
   (A.2,A.1::s.2)
 def batchStepRealizer:Realizer batchStep:=
   (((Realizer.fst.comp readRationalRealizer).comp Realizer.snd).pair
     ((((Realizer.fst.comp readRationalRealizer).comp Realizer.fst).pair Realizer.snd).comp Realizer.cons))
 theorem batchStep_polynomial:PolyBound batchStepRealizer:=
   polynomial_pair (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readRational_polynomial) (linear_polynomial linear_snd))
     (polynomial_comp (polynomial_pair
       (polynomial_comp (polynomial_comp (linear_polynomial linear_fst) readRational_polynomial) (linear_polynomial linear_fst))
       (linear_polynomial linear_snd)) (linear_polynomial linear_cons))
 theorem batchStep_volume (s:BatchState):volume (batchStep s)≤volume s+8:=by
   rcases s with ⟨L,R⟩
   have hv:=readRational_volume L
   simp only [batchStep,volume_pair,volume_cons]
   omega

 def readMany (n:ℕ) (L:List Bool):List SignedWords×List Bool:=
   let s:=batchStep^[n] (L,[])
   (s.2.reverse,s.1)
 def readManyRealizer:Realizer (fun x:ℕ×List Bool => readMany x.1 x.2):=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp batchStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst))
 theorem readMany_polynomial:PolyBound readManyRealizer:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:ℕ×List Bool => ([]:List SignedWords))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold readManyRealizer
   refine polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn)))
       (polynomial_iterate batchStep_polynomial 8 batchStep_volume))
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) ?_) (linear_polynomial linear_fst))

   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen:L.length≤volume L:=by
     induction L with
     | nil => simp
     | cons a L ih => simp only [List.length_cons,volume_cons]; omega
   have ht:=Uniform.time_reverse (I:=Unit) (α:=fun _ => SignedWords) () L
   have hp:L.length+1≤volume L+1:=by omega
   have hm:=Nat.mul_le_mul_right (200*(volume L+1)) hp
   constructor
   · change Realizer.reverse.time L≤_
     have he:200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2:=by nlinarith only [hm]
     exact ht.trans (he.trans (Nat.mul_le_mul_right _ (by omega)))
   · rw [volume_reverse]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 def codeWords (q:RationalCode):SignedWords:=
   (decide (q.numerator<0),(natBits q.numerator.natAbs,natBits q.denominator))
 theorem batchStep_codes (qs:List RationalCode) (rest:List Bool) (acc:List SignedWords):
     batchStep^[qs.length] (qs.flatMap RationalCode.bits++rest,acc)=
       (rest,(qs.map codeWords).reverse++acc):=by
   induction qs generalizing acc with
   | nil => simp
   | cons q qs ih =>
     rw [List.length_cons,Function.iterate_succ_apply]
     simp only [List.flatMap_cons,List.append_assoc,batchStep,readRational_code]
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append,codeWords]
 theorem readMany_codes (qs:List RationalCode) (rest:List Bool):
     readMany qs.length (qs.flatMap RationalCode.bits++rest)=(qs.map codeWords,rest):=by
   dsimp only [readMany]
   rw [batchStep_codes]
   simp
end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 theorem growth_coefficient (F E:ℕ):10000*F+10000*E+10000≤100000*(F+E+10):=by omega
 theorem growth_output_coefficient (F E:ℕ):E≤100000*(F+E+10):=by omega

 theorem polynomial_iterate_growth {f:α→ α} {R:Realizer f} (hR:PolyBound R) (E r:ℕ)
    (hg:∀x j,volume (f^[j] x)≤E*(volume x+j+1)^r):PolyBound R.iterate:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   let F:=C*(E+1)^q
   let e:=r*q+r+2
   refine ⟨100000*(F+E+10),e,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z:=volume (n,a)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hn:n+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha:volume a+n+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hV (j:ℕ) (hj:j≤n):volume (f^[j] a)≤E*z^r:=
     (hg a j).trans (Nat.mul_le_mul_left E (Nat.pow_le_pow_left (by omega) r))
   have hT (j:ℕ) (hj:j<n):R.time (f^[j] a)≤F*z^(r*q):=by
     have hh:=(hR (f^[j] a)).1
     have hv:=hV j hj.le
     have hp:1≤z^r:=one_le_pow₀ hz
     have hbase:volume (f^[j] a)+1≤(E+1)*z^r:=by nlinarith
     have ht:=hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,pow_mul,Nat.mul_assoc] using ht
   have ht:=Realizer.time_iterate_le R n a (F*z^(r*q)) (E*z^r) hT hV
   have hq:z^(r*q+1)≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr:z^(r+1)≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have h2:z^2≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   constructor
   · change _≤100000*(F+E+10)*z^e
     have hm:=Nat.mul_le_mul hn (show F*z^(r*q)+E*z^r+n+1≤F*z^(r*q)+E*z^r+z by omega)
     have hm':=Nat.mul_le_mul_left 10000 hm
     have hpq:=Nat.mul_le_mul_left (10000*F) hq
     have hpr:=Nat.mul_le_mul_left (10000*E) hr
     have hp2:=Nat.mul_le_mul_left 10000 h2
     have hs:R.iterate.time (n,a)≤(10000*F+10000*E+10000)*z^e:=by
       rw [pow_succ] at hpq hpr
       nlinarith only [ht,hm',hpq,hpr,hp2]
     exact hs.trans (Nat.mul_le_mul_right _ (growth_coefficient F E))
   · change volume (f^[n] a)≤100000*(F+E+10)*z^e
     have hp:=Nat.pow_le_pow_right hz (by dsimp [e]; omega:r≤e)
     have hh:=(hV n le_rfl).trans (Nat.mul_le_mul_left E hp)
     exact hh.trans (Nat.mul_le_mul_right _ (growth_output_coefficient F E))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def triStep (s:ℕ×ℕ):ℕ×ℕ:=(s.1+1,s.2+s.1)
 def triStepRealizer:Realizer triStep:=(Realizer.fst.comp Realizer.succ).pair
   ((Realizer.snd.pair Realizer.fst).comp Realizer.add)
 theorem triStep_polynomial:PolyBound triStepRealizer:=
   polynomial_pair (linear_polynomial (linear_comp linear_fst succ_linear))
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) BinaryGcd.nat_add_polynomial)

 theorem triStep_first (i s j:ℕ):(triStep^[j] (i,s)).1=i+j:=by
   induction j with
   | zero => rfl
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only [triStep]; omega
 theorem triStep_second (i s j:ℕ):(triStep^[j] (i,s)).2≤ s+j*(i+j):=by
   induction j with
   | zero => simp
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only [triStep]; rw [triStep_first]; nlinarith
 theorem triStep_growth (s:ℕ×ℕ) (j:ℕ):volume (triStep^[j] s)≤10*(volume s+j+1)^2:=by
   rcases s with ⟨i,s⟩
   let z:=volume (i,s)+j+1
   have hz:1≤z:=by dsimp [z]; omega
   have hbase:i+s+j+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have h1:=triStep_first i s j
   have h2:=triStep_second i s j
   have hp:j*(i+j)≤z*z:=Nat.mul_le_mul (by omega) (by omega)
   change volume ((triStep^[j] (i,s)).1,(triStep^[j] (i,s)).2)≤10*z^2
   simp only [volume_pair,volume_nat,h1]
   nlinarith
 theorem triStep_iterate_poly:PolyBound triStepRealizer.iterate:=
   polynomial_iterate_growth triStep_polynomial 10 2 triStep_growth

 def triangular (n:ℕ):ℕ:=(triStep^[n] (0,0)).2
 theorem triStep_sum (n:ℕ):triStep^[n] (0,0)=(n,∑ i∈ Finset.range n,i):=by
   induction n with
   | zero => simp
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp [triStep,Finset.sum_range_succ]
 theorem triangular_eq (n:ℕ):triangular n=n*(n-1)/2:=by
   rw [triangular,triStep_sum,Finset.sum_range_id]
 def triangularRealizer:Realizer triangular:=
   (((Realizer.id.pair (Realizer.constant (0,0))).comp triStepRealizer.iterate).comp Realizer.snd)
 theorem triangular_polynomial:PolyBound triangularRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_constant ((0:ℕ),(0:ℕ))))) triStep_iterate_poly) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 noncomputable def adjacencyBits {n:ℕ} (G:SimpleGraph (Fin n)):List Bool:=
   (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => u<v)).map (fun v => decide (G.Adj u v)))
 theorem adjacency_row_length {n:ℕ} (u:Fin n):
     ((List.finRange n).filter (fun v => u<v)).length=n-1-u.val:=by
   rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_finRange n))]
   have he:((List.finRange n).filter (fun v => u<v)).toFinset=Finset.Ioi u:=by
     ext v
     simp
   rw [he,Fin.card_Ioi]
 theorem adjacencyBits_length {n:ℕ} (G:SimpleGraph (Fin n)):(adjacencyBits G).length=triangular n:=by
   have he:(adjacencyBits G).length=∑ u:Fin n,((List.finRange n).filter (fun v => u<v)).length:=by
     simp [adjacencyBits,List.length_flatMap,List.finRange,List.map_ofFn,List.sum_ofFn]
   rw [he]
   simp_rw [adjacency_row_length]
   rw [Fin.sum_univ_eq_sum_range (fun u => n-1-u) n,Finset.sum_range_reflect (fun u => u) n,
     Finset.sum_range_id,triangular_eq]
 theorem graphBits_eq {n:ℕ} (G:SimpleGraph (Fin n)):graphBits G=encodeNat n++adjacencyBits G:=rfl

 def graphStart (L:List Bool):ℕ×(List Bool×List Bool):=
   let p:=readNatural L
   (p.1,splitWord p.2 (triangular p.1))
 def graphStartRealizer:Realizer graphStart:=
   (readNaturalRealizer.comp Realizer.fst).pair
     (((readNaturalRealizer.comp Realizer.snd).pair ((readNaturalRealizer.comp Realizer.fst).comp triangularRealizer)).comp splitWordRealizer)
 theorem graphStart_polynomial:PolyBound graphStartRealizer:=
   polynomial_pair (polynomial_comp readNatural_polynomial (linear_polynomial linear_fst))
     (polynomial_comp (polynomial_pair (polynomial_comp readNatural_polynomial (linear_polynomial linear_snd))
       (polynomial_comp (polynomial_comp readNatural_polynomial (linear_polynomial linear_fst)) triangular_polynomial)) splitWord_polynomial)

 theorem graphStart_weighted {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode) (ε:RationalCode):
     graphStart (weightedInput G w ε)=(n,(adjacencyBits G,rationalData w ε)):=by
   have he:weightedInput G w ε=encodeNat n++(adjacencyBits G++rationalData w ε):=by
     rw [weightedInput,graphBits_eq,List.append_assoc]
   have hb:=weighted_order_bound G w ε
   rw [he] at hb ⊢
   dsimp only [graphStart]
   rw [readNatural_encoded n _ hb,← adjacencyBits_length G]
   simp only [splitWord,List.take_left,List.drop_left]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]

 theorem length_volume (L:List α):L.length≤volume L:=by
   induction L with
   | nil => simp
   | cons a L ih => simp only [List.length_cons,volume_cons]; omega
 def mapEnvironment {f:α×γ→ β} (R:Realizer f):
     Realizer (fun x:List α×γ => x.1.map (fun a => f (a,x.2))):=(R.uniform Unit).map.specialize ()
 theorem mapEnvironment_time {f:α×γ→ β} (R:Realizer f) (x:List α×γ):
     (mapEnvironment R).time x=(R.uniform Unit).map.time () x:=rfl

 theorem polynomial_mapEnvironment {f:α×γ→ β} {R:Realizer f} (hR:PolyBound R):PolyBound (mapEnvironment R):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   refine ⟨100000*(C+10),q+2,by positivity,?_⟩
   rintro ⟨xs,e⟩
   let z:=volume (xs,e)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hlen:=length_volume xs
   have hlenz:xs.length+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hvolz:volume xs+volume e+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hq:z^q≤z^(q+1):=Nat.pow_le_pow_right hz (by omega)
   have hze:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   have hp1:1≤z^(q+1):=one_le_pow₀ hz
   have hbounds (a:α) (ha:a∈xs):R.time (a,e)≤C*z^q∧ volume (f (a,e))≤C*z^q:=by
     have hv:=volume_mem_le ha
     have hbase:volume (a,e)+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
     have hh:=hR (a,e)
     exact ⟨hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)),
       hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))⟩
   have hout:volume (xs.map (fun a => f (a,e)))≤(C+2)*z^(q+1):=by
     have hh:=volume_list_le (xs.map (fun a => f (a,e))) (C*z^q) (by
       intro b hb
       obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hb
       exact (hbounds a ha).2)
     rw [List.length_map] at hh
     have hm:=Nat.mul_le_mul (show xs.length≤z by omega) (show C*z^q+1≤C*z^q+1 by rfl)
     have he:z*(C*z^q+1)=C*z^(q+1)+z:=by rw [pow_succ]; ring
     rw [he] at hm
     nlinarith only [hh,hm,hze,hp1]
   have ht:=Uniform.time_map (R.uniform Unit) () xs e (C*z^q) (fun a ha => (hbounds a ha).1)
   rw [Nat.mul_assoc] at ht
   have hinner:C*z^q+volume xs+volume e+volume (xs.map (fun a => f (a,e)))+1≤(2*C+6)*z^(q+1):=by
     have htime:=Nat.mul_le_mul_left C hq
     nlinarith only [htime,hout,hvolz,hze,hp1]
   have hmul:=Nat.mul_le_mul_left 30000 (Nat.mul_le_mul hlenz hinner)
   have he:30000*(z*((2*C+6)*z^(q+1)))=30000*(2*C+6)*z^(q+2):=by rw [pow_succ]; ring
   rw [he] at hmul
   have hcoef:30000*(2*C+6)≤100000*(C+10):=by omega
   constructor
   · rw [mapEnvironment_time]
     change (R.uniform Unit).map.time () (xs,e)≤100000*(C+10)*z^(q+2)
     have hh:(R.uniform Unit).map.time () (xs,e)≤30000*(2*C+6)*z^(q+2):=ht.trans hmul
     exact hh.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (xs.map (fun a => f (a,e)))≤_
     have hp:=Nat.pow_le_pow_right hz (by omega:q+1≤q+2)
     exact hout.trans ((Nat.mul_le_mul_left (C+2) hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def mapList {f:α→ β} (R:Realizer f):Realizer (fun xs:List α => xs.map f):=
   ((Realizer.id.pair Realizer.unit).comp (mapEnvironment (Realizer.fst.comp R))).congr (fun _ => rfl)
 theorem polynomial_mapList {f:α→ β} {R:Realizer f} (hR:PolyBound R):PolyBound (mapList R):=by
   have hu:Linear (Realizer.unit:Realizer (fun _:List α => ())):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold mapList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hu))
     (polynomial_mapEnvironment (polynomial_comp (linear_polynomial linear_fst) hR))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem multiply_prefix_volume (A B:List Bool) (j:ℕ) (hj:j≤B.length):
     volume ((B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))≤12*(A.length+B.length+1):=by
   let s:=(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hfirst:=multiply_first_length A (B.take j) []
   have hsecond:=multiply_prefix_length A B j
   have htake:(B.take j).length≤B.length:=by simpa only [List.length_take] using Nat.min_le_right j B.length
   have hvA:=BinaryAdder.volume_bits s.1
   have hvB:=BinaryAdder.volume_bits s.2
   change s.1.length=A.length+(B.take j).length at hfirst
   change s.2.length≤A.length+B.length at hsecond
   change volume (s.1,s.2)≤_
   simp only [volume_pair]
   omega

 theorem multiply_fold_time:∃ C q:ℕ,0<C∧ ∀ A B:List Bool,
     multiplyStepRealizer.fold.time (B,(A,[]))≤C*(A.length+B.length+1)^q:=by
   obtain ⟨C,q,hC,hpoly⟩:=multiplyStep_polynomial
   refine ⟨C*17^q+2000,q+2,by positivity,?_⟩
   intro A B
   let z:=A.length+B.length+1
   have hz:1≤z:=by dsimp [z]; omega
   have hvB:volume B≤5*z:=by have hh:=BinaryAdder.volume_bits B; dsimp [z]; omega
   have hvA:volume A≤5*z:=by have hh:=BinaryAdder.volume_bits A; dsimp [z]; omega
   have hvol:=multiply_prefix_volume A B
   have htime (j:ℕ) (hj:j<B.length):
       multiplyStepRealizer.time (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))≤C*17^q*z^q:=by
     have hh:=(hpoly (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))).1
     have hb:=volume_bool B[j]
     have hs:=hvol j hj.le
     have hv:volume (B[j],(B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[]))+1≤17*z:=by
       simp only [volume_pair]
       change _≤17*z
       change _≤12*z at hs
       omega
     have hp:=Nat.pow_le_pow_left hv q
     have ht:=hh.trans (Nat.mul_le_mul_left C hp)
     simpa only [mul_pow,Nat.mul_assoc] using ht
   have hf:=fold_prefix_bound multiplyStepRealizer B (A,[]) (C*17^q*z^q) (12*z) hvol htime
   have hBL:B.length≤z:=by dsimp [z]; omega
   have hq1:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hq2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hzgrow:z≤z^2:=by nlinarith
   have hmul:B.length*(C*17^q*z^q+20*(volume B+2*(12*z)+1))≤z*(C*17^q*z^q+600*z):=by
     apply Nat.mul_le_mul hBL
     omega
   have hqprod:z*(C*17^q*z^q)=C*17^q*z^(q+1):=by rw [pow_succ]; ring
   have hf':Realizer.foldTime multiplyStepRealizer (A,[]) B≤(C*17^q+1000)*z^(q+2):=by
     have ht:=Nat.mul_le_mul_left (C*17^q) hq1
     have hc:=Nat.mul_le_mul_left 1000 hq2
     simp only [Nat.mul_add,hqprod] at hmul
     nlinarith only [hf,hmul,ht,hc,hzgrow,hz]
   rw [Realizer.time_fold]
   simp only [volume_pair,volume_nil]
   change _≤(C*17^q+2000)*z^(q+2)
   have hpow:z≤z^(q+2):=hzgrow.trans hq2
   nlinarith only [hf',hvA,hvB,hpow,hz]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem multiplyInitial_linear:Linear multiplyInitial:=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List Bool×List Bool => ([]:List Bool))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact linear_pair linear_snd (linear_pair linear_fst hn)

 theorem multiply_time:∃ C q:ℕ,0<C∧ ∀ A B:List Bool,
     multiplyRealizer.time (A,B)≤C*(A.length+B.length+1)^q:=by
   obtain ⟨C,q,hC,hfold⟩:=multiply_fold_time
   obtain ⟨I,hI,hinit⟩:=multiplyInitial_linear
   let post:=(Realizer.snd:Realizer (Prod.snd:List Bool×List Bool→ List Bool)).comp trimRealizer
   have hp:PolyBound post:=polynomial_comp (linear_polynomial linear_snd) trim_polynomial
   obtain ⟨D,r,hD,hpost⟩:=hp
   let e:=q+r+2
   refine ⟨5*I+C+D*13^r+1000,e,by positivity,?_⟩
   intro A B
   let z:=A.length+B.length+1
   let initial:List Bool×(List Bool×List Bool):=(B,(A,[]))
   let final:=B.foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hz:1≤z:=by dsimp [z]; omega
   have he1:1≤e:=by dsimp [e]; omega
   have hq:z^q≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr:z^r≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze:z≤z^e:=by simpa only [pow_one] using Nat.pow_le_pow_right hz he1
   have hA:=BinaryAdder.volume_bits A
   have hB:=BinaryAdder.volume_bits B
   have hvx:volume (A,B)≤4*z:=by simp only [volume_pair]; dsimp [z]; omega
   have hvi:volume initial≤6*z:=by dsimp [initial]; simp only [volume_pair,volume_nil]; dsimp [z]; omega
   have hvf:volume final≤12*z:=by
     have hh:=multiply_prefix_volume A B B.length le_rfl
     simpa only [List.take_length] using hh
   have hi:multiplyInitial.time (A,B)≤5*I*z^e:=by
     have hh:=(hinit (A,B)).1
     have hh':=hh.trans (Nat.mul_le_mul_left I (show volume (A,B)+1≤5*z by omega))
     exact hh'.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left (5*I) hze)
   have hf:multiplyStepRealizer.fold.time initial≤C*z^e:=(hfold A B).trans (Nat.mul_le_mul_left C hq)
   have ho:post.time final≤D*13^r*z^e:=by
     have hh:=(hpost final).1
     have hbase:volume final+1≤13*z:=by omega
     have hh':=hh.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hbase r))
     simp only [mul_pow] at hh'
     exact hh'.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*13^r) hr)
   have hcopy:10*(volume initial+1)+10*(volume final+1)≤1000*z^e:=by omega
   have heq:multiplyRealizer.time (A,B)=multiplyInitial.time (A,B)+multiplyStepRealizer.fold.time initial+
       10*(volume initial+1)+post.time final+10*(volume final+1):=by
     dsimp only [multiplyRealizer,multiply]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
     dsimp only [post,initial,final]
     rw [Realizer.time_comp]
     ring
   rw [heq]
   change _≤(5*I+C+D*13^r+1000)*z^e
   nlinarith only [hi,hf,ho,hcopy]

 theorem multiply_polynomial:PolyBound multiplyRealizer:=by
   obtain ⟨C,q,hC,hT⟩:=multiply_time
   refine ⟨C+5,q+1,by omega,?_⟩
   rintro ⟨A,B⟩
   let z:=volume (A,B)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hA:=bits_length_volume A
   have hB:=bits_length_volume B
   have hbase:A.length+B.length+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hp:(A.length+B.length+1)^q≤z^(q+1):=(Nat.pow_le_pow_left hbase q).trans (Nat.pow_le_pow_right hz (by omega))
   have ht:=(hT A B).trans (Nat.mul_le_mul_left C hp)
   have hv:=BinaryAdder.volume_bits (multiply A B)
   have hlen:=multiply_length A B
   have hpow:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (multiply A B)≤_
     have hv':volume (multiply A B)≤5*z^(q+1):=by omega
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev FractionWords:=List Bool×List Bool
 def fractionValue (s:FractionWords):ℚ:=(value s.1:ℚ)/(value s.2:ℚ)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 theorem fold_select_mem (f:α×α→ α) (h:∀a b,f (a,b)=a∨ f (a,b)=b) (xs:List α) (b:α):
     xs.foldl (fun b a => f (a,b)) b=b∨ xs.foldl (fun b a => f (a,b)) b∈xs:=by
   induction xs generalizing b with
   | nil => exact Or.inl rfl
   | cons a xs ih =>
     rw [List.foldl_cons]
     rcases ih (f (a,b)) with he|hm
     · rw [he]
       rcases h a b with ha|hb
       · exact Or.inr (by simp [ha])
       · exact Or.inl hb
     · exact Or.inr (List.mem_cons_of_mem a hm)

 theorem polynomial_fold_select {f:α×α→ α} {R:Realizer f} (hR:PolyBound R)
     (hf:∀a b,f (a,b)=a∨ f (a,b)=b):PolyBound R.fold:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   refine ⟨C*3^q+1000,q+2,by positivity,?_⟩
   rintro ⟨xs,b⟩
   let z:=volume (xs,b)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hlen:xs.length≤z:=by have hh:=length_volume xs; dsimp [z]; simp only [volume_pair]; omega
   have hbase:volume xs+volume b+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hv (j:ℕ) (_hj:j≤xs.length):volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤z:=by
     rcases fold_select_mem f hf (xs.take j) b with he|hm
     · rw [he]; omega
     · have hm':(xs.take j).foldl (fun b a => f (a,b)) b∈xs:=List.mem_of_mem_take hm
       exact (volume_mem_le hm').trans (by omega)
   have ht (j:ℕ) (hj:j<xs.length):
       R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤C*3^q*z^q:=by
     have ha:=volume_mem_le (List.getElem_mem hj)
     have hb:=hv j hj.le
     have he:volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤3*z:=by simp only [volume_pair]; omega
     have hh:=((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left he q))
     simpa only [mul_pow,Nat.mul_assoc] using hh
   have hh:=fold_prefix_bound R xs b (C*3^q*z^q) z hv ht
   have hp1:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hp2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hp:z≤z^(q+2):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+2)
   change volume (xs,b)+1≤z^(q+2) at hp
   have hm:=Nat.mul_le_mul hlen (show C*3^q*z^q+20*(volume xs+2*z+1)≤C*3^q*z^q+100*z by omega)
   have he:z*(C*3^q*z^q+100*z)=C*3^q*z^(q+1)+100*z^2:=by rw [pow_succ]; ring
   rw [he] at hm
   have htime:=Nat.mul_le_mul_left (C*3^q) hp1
   have hcopy:=Nat.mul_le_mul_left 100 hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(C*3^q+1000)*z^(q+2)
     nlinarith only [hh,hm,htime,hcopy,hp,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤_
     have hv':=hv xs.length le_rfl
     rw [List.take_length] at hv'
     exact hv'.trans (hp.trans (Nat.le_mul_of_pos_left _ (by positivity)))

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def valueStep (x:Bool×ℕ):ℕ:=2*x.2+x.1.toNat
 def valueStepRealizer:Realizer valueStep:=
   ((((Realizer.snd.pair Realizer.snd).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply,valueStep]; omega)
 theorem valueStep_polynomial:PolyBound valueStepRealizer:=by
   unfold valueStepRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_snd)) BinaryGcd.nat_add_polynomial)
     (linear_polynomial (linear_comp linear_fst boolNat_linear))) BinaryGcd.nat_add_polynomial
 theorem valueFold (L:List Bool) (v:ℕ):
     L.foldl (fun v b => valueStep (b,v)) v=value L.reverse+2^L.length*v:=by
   induction L generalizing v with
   | nil => simp [value]
   | cons b L ih =>
     rw [List.foldl_cons,ih,List.reverse_cons,BinaryAdder.value_append]
     simp only [valueStep,value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     ring
 theorem value_drop_le (A:List Bool) (k:ℕ):value (A.drop k)≤value A:=by
   induction k generalizing A with
   | zero => rfl
   | succ k ih =>
     cases A with
     | nil => simp [value]
     | cons b A => rw [List.drop_succ_cons]; exact (ih A).trans (by dsimp only [value]; omega)
 theorem valuePrefix (A:List Bool) (j:ℕ):
     (A.reverse.take j).foldl (fun v b => valueStep (b,v)) 0≤value A:=by
   rw [valueFold,Nat.mul_zero,Nat.add_zero,List.reverse_take,List.reverse_reverse,List.length_reverse]
   exact value_drop_le A _
 def valueInitial:Realizer (fun A:List Bool => (A.reverse,(0:ℕ))):=Realizer.reverse.pair (Realizer.constant 0)
 def valueRealizer:Realizer value:=(valueInitial.comp valueStepRealizer.fold).congr (fun A => by
   change A.reverse.foldl (fun v b => valueStep (b,v)) 0=value A
   rw [valueFold,List.reverse_reverse]
   simp only [Nat.mul_zero,Nat.add_zero])
 theorem valueInitial_polynomial:PolyBound valueInitial:=polynomial_pair reverse_polynomial (linear_polynomial (linear_constant (0:ℕ)))
 theorem value_time:∃ C q:ℕ,0<C∧ ∀ A:List Bool,
     valueRealizer.time A≤C*(value A+A.length+1)^q:=by
   obtain ⟨C,q,hC,hR⟩:=valueStep_polynomial
   obtain ⟨I,p,hI,hinit⟩:=valueInitial_polynomial
   let F:=C*17^q+2000
   let e:=p+q+3
   refine ⟨I*5^p+F+100,e,by dsimp [F]; positivity,?_⟩
   intro A
   let z:=value A+A.length+1
   have hz:1≤z:=by dsimp [z]; omega
   have hL:A.length≤z:=by dsimp [z]; omega
   have hV:value A≤z:=by dsimp [z]; omega
   have hvolA:=BinaryAdder.volume_bits A
   have hprefix:∀j,j≤A.reverse.length→ volume ((A.reverse.take j).foldl (fun v b => valueStep (b,v)) 0)≤12*z:=by
     intro j _
     have hh:=valuePrefix A j
     simp only [volume_nat]
     omega
   have hfold:=bit_fold_envelope valueStepRealizer C q (fun x => (hR x).1) A.reverse 0 z hz
     (by simpa only [List.length_reverse] using hL) (by rw [volume_reverse]; omega) hprefix
   have hp:z^p≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq:z^(q+2)≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze:z≤z^e:=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega:1≤e)
   have hi:valueInitial.time A≤I*5^p*z^e:=by
     have hh:=((hinit A).1).trans (Nat.mul_le_mul_left I (Nat.pow_le_pow_left (show volume A+1≤5*z by omega) p))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (I*5^p) hp)
   have hf:=hfold.trans (Nat.mul_le_mul_left F hq)
   have hcopy:10*(volume (A.reverse,(0:ℕ))+1)≤100*z^e:=by
     simp only [volume_pair,volume_nat,volume_reverse]
     omega
   have heq:valueRealizer.time A=valueInitial.time A+valueStepRealizer.fold.time (A.reverse,0)+10*(volume (A.reverse,(0:ℕ))+1):=by
     dsimp only [valueRealizer]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
   rw [heq]
   change _≤(I*5^p+F+100)*z^e
   nlinarith only [hi,hf,hcopy]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 theorem reverse_polynomial_generic:PolyBound (Realizer.reverse:Realizer (fun L:List α => L.reverse)):=by
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen:=length_volume L
   have ht:=Uniform.time_reverse (I:=Unit) (α:=fun _ => α) () L
   have hm:=Nat.mul_le_mul_right (200*(volume L+1)) (show L.length+1≤volume L+1 by omega)
   constructor
   · have he:200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2:=by nlinarith only [hm]
     exact ht.trans (he.trans (Nat.mul_le_mul_right _ (by omega)))
   · rw [volume_reverse]
     nlinarith
 theorem take_volume_le (L:List α) (j:ℕ):volume (L.take j)≤volume L:=by
   have hh:=volume_append (L.take j) (L.drop j)
   rw [List.take_append_drop] at hh
   have hp:=volume_pos (L.drop j)
   omega
 theorem cons_fold_polynomial_generic:PolyBound (Realizer.cons:Realizer (fun x:α×List α => x.1::x.2)).fold:=by
   refine ⟨200,2,by omega,?_⟩
   rintro ⟨A,B⟩
   let z:=volume (A,B)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hlen:A.length≤z:=by have hh:=length_volume A; dsimp [z]; simp only [volume_pair]; omega
   have hbase:volume A+volume B+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hv (j:ℕ) (_hj:j≤A.length):volume ((A.take j).foldl (fun s a => a::s) B)≤z:=by
     rw [Realizer.fold_cons_eq]
     have hh:=volume_append (A.take j).reverse B
     rw [volume_reverse] at hh
     have ht:=take_volume_le A j
     omega
   have ht (j:ℕ) (hj:j<A.length):
       (Realizer.cons:Realizer (fun x:α×List α => x.1::x.2)).time (A[j],(A.take j).foldl (fun s a => a::s) B)≤5*z:=by
     have ha:=volume_mem_le (List.getElem_mem hj)
     have hb:=hv j hj.le
     change volume (A[j],(A.take j).foldl (fun s a => a::s) B)+2≤_
     simp only [volume_pair]
     omega
   have hh:=fold_prefix_bound (Realizer.cons:Realizer (fun x:α×List α => x.1::x.2)) A B (5*z) z hv ht
   have hm:=Nat.mul_le_mul hlen (show 5*z+20*(volume A+2*z+1)≤100*z by omega)
   have hp:z≤z^2:=by nlinarith
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (A,B)+6+Realizer.foldTime Realizer.cons B A≤200*z^2
     have he:volume (A,B)+1=z:=rfl
     nlinarith only [hh,hm,hp,he,hz]
   · change volume (A.foldl (fun s a => a::s) B)≤_
     have ho:=hv A.length le_rfl
     rw [List.take_length] at ho
     exact ho.trans (hp.trans (Nat.le_mul_of_pos_left _ (by omega)))

 def appendList:Realizer (fun x:List α×List α => x.1++x.2):=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun _ => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])
 theorem appendList_polynomial:PolyBound (appendList:Realizer (fun x:List α×List α => x.1++x.2)):=by
   unfold appendList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial_generic)
     (linear_polynomial linear_snd)) cons_fold_polynomial_generic

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β:Type} [Coding α] [Coding β]

 theorem polynomial_fold_bounded {f:α×β→ β} {R:Realizer f} (hR:PolyBound R) (E:ℕ)
     (hV:∀ (xs:List α) b j,j≤xs.length→ volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤E*(volume (xs,b)+1)):
     PolyBound R.fold:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   let F:=C*(E+3)^q
   refine ⟨F+100*E+200,q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨xs,b⟩
   let z:=volume (xs,b)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hlen:xs.length≤z:=by have hh:=length_volume xs; dsimp [z]; simp only [volume_pair]; omega
   have hxs:volume xs≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hv (j:ℕ) (hj:j≤xs.length):volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤E*z:=hV xs b j hj
   have ht (j:ℕ) (hj:j<xs.length):R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤F*z^q:=by
     have ha:=volume_mem_le (List.getElem_mem hj)
     have hb:=hv j hj.le
     have hbase:volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)+1≤(E+3)*z:=by simp only [volume_pair]; nlinarith
     have hh:=((hR _).1).trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using hh
   have hh:=fold_prefix_bound R xs b (F*z^q) (E*z) hv ht
   have hp1:z^(q+1)≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hp2:z^2≤z^(q+2):=Nat.pow_le_pow_right hz (by omega)
   have hp:z≤z^(q+2):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+2)
   have hm:=Nat.mul_le_mul hlen (show F*z^q+20*(volume xs+2*(E*z)+1)≤F*z^q+(40*E+40)*z by nlinarith)
   have he:z*(F*z^q+(40*E+40)*z)=F*z^(q+1)+(40*E+40)*z^2:=by rw [pow_succ]; ring
   rw [he] at hm
   have htime:=Nat.mul_le_mul_left F hp1
   have hcopy:=Nat.mul_le_mul_left (40*E+40) hp2
   constructor
   · rw [Realizer.time_fold]
     change 2*volume (xs,b)+6+Realizer.foldTime R b xs≤(F+100*E+200)*z^(q+2)
     have hinput:volume (xs,b)+1=z:=rfl
     nlinarith only [hh,hm,htime,hcopy,hp,hinput,hz]
   · change volume (xs.foldl (fun b a => f (a,b)) b)≤_
     have hv':=hv xs.length le_rfl
     rw [List.take_length] at hv'
     have hout:=hv'.trans (Nat.mul_le_mul_left E hp)
     have hcoef:E≤F+100*E+200:=by omega
     exact hout.trans (Nat.mul_le_mul_right _ hcoef)

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def sumWords (A B:List Bool):List Bool:=trim (BinaryAdder.word A B)
 theorem sumWords_value (A B:List Bool):value (sumWords A B)=value A+value B:=by
   rw [sumWords,trim_value,BinaryAdder.word_value]

 def sumWordsRealizer:Realizer (fun s:List Bool×List Bool => sumWords s.1 s.2):=
   BinaryAdder.wordRealizer.comp trimRealizer
 theorem sumWords_polynomial:PolyBound sumWordsRealizer:=polynomial_comp word_polynomial trim_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedFractionValue (s:SignedWords):ℚ:=(signedValue s.1 s.2.1:ℚ)/(value s.2.2:ℚ)
 theorem signedFractionValue_code (q:RationalCode):signedFractionValue (codeWords q)=q.value:=by
   simp only [signedFractionValue,codeWords,signedValue_encode,value_natBits,RationalCode.value]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedReduced (s:SignedWords):SignedWords:=
   (rationalSign s,normalizeWords s.2.1 s.2.2)
 def signedReducedRealizer:Realizer signedReduced:=signRealizer.pair normalizedRealizer
 theorem signedReduced_polynomial:PolyBound signedReducedRealizer:=
   polynomial_pair
     (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
       (polynomial_comp (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)
         (linear_polynomial nonempty_linear))) (linear_polynomial linear_and))
     (polynomial_comp (linear_polynomial linear_snd) normalizeWords_polynomial)
 theorem signedReduced_canonical (s:SignedWords) (hd:0<value s.2.2):
     signedReduced s=(decide ((signedFractionValue s).num<0),
       (natBits (signedFractionValue s).num.natAbs,natBits (signedFractionValue s).den)):=by
   rcases s with ⟨b,N,D⟩
   have hn:=normalizeWords_rat b N D hd
   dsimp only [signedReduced,signedFractionValue,Prod.fst,Prod.snd]
   exact Prod.ext (rational_sign b N D hd) (Prod.ext hn.1 hn.2)

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α:Type} [Coding α]

 def flattenStep (s:List α×List α):List α:=s.2++s.1
 def flattenStepRealizer:Realizer (flattenStep (α:=α)):=(Realizer.snd.pair Realizer.fst).comp appendList
 theorem flattenStep_polynomial:PolyBound (flattenStepRealizer (α:=α)):=
   polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) appendList_polynomial
 theorem flattenFold (xs:List (List α)) (acc:List α):xs.foldl (fun b a => flattenStep (a,b)) acc=acc++xs.flatten:=by
   induction xs generalizing acc with
   | nil => simp
   | cons a xs ih => rw [List.foldl_cons,ih]; simp [flattenStep,List.append_assoc]
 theorem flatten_fold_polynomial:PolyBound (flattenStepRealizer (α:=α)).fold:=by
   apply polynomial_fold_bounded flattenStep_polynomial 1
   intro xs acc j _
   rw [flattenFold]
   have hflat:=volume_flatten (xs.take j)
   have ht:=take_volume_le xs j
   have ha:=volume_append acc (xs.take j).flatten
   simp only [volume_pair,one_mul]
   omega
 def flattenList:Realizer (fun xs:List (List α) => xs.flatten):=
   ((Realizer.id.pair Realizer.nil).comp flattenStepRealizer.fold).congr (fun xs => by change xs.foldl (fun b a => flattenStep (a,b)) []=xs.flatten; rw [flattenFold]; rfl)
 theorem flattenList_polynomial:PolyBound (flattenList (α:=α)):=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List (List α) => ([]:List α))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold flattenList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn)) flatten_fold_polynomial

 def repeatStep (s:α×List α):α×List α:=(s.1,s.1::s.2)
 def repeatStepRealizer:Realizer (repeatStep (α:=α)):=Realizer.fst.pair Realizer.cons
 theorem repeatStep_linear:Linear (repeatStepRealizer (α:=α)):=linear_pair linear_fst linear_cons
 theorem repeatStep_iterate (n:ℕ) (a:α) (L:List α):repeatStep^[n] (a,L)=(a,List.replicate n a++L):=by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp only [repeatStep,List.replicate_succ,List.cons_append]
 theorem volume_replicate (n:ℕ) (a:α):volume (List.replicate n a)=n*(volume a+1)+1:=by
   induction n with
   | zero => simp
   | succ n ih => rw [List.replicate_succ,volume_cons,ih]; ring
 theorem repeatStep_growth (s:α×List α) (j:ℕ):volume (repeatStep^[j] s)≤3*(volume s+j+1)^2:=by
   rcases s with ⟨a,L⟩
   let z:=volume (a,L)+j+1
   have hz:1≤z:=by dsimp [z]; omega
   have hbase:volume a+volume L+j+1≤z:=by dsimp [z]; simp only [volume_pair]; omega
   have hp:j*(volume a+1)≤z*z:=Nat.mul_le_mul (by omega) (by omega)
   have ha:=volume_append (List.replicate j a) L
   rw [volume_replicate] at ha
   rw [repeatStep_iterate,volume_pair]
   change _≤3*z^2
   nlinarith
 def replicateList:Realizer (fun x:ℕ×α => List.replicate x.1 x.2):=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp repeatStepRealizer.iterate).comp Realizer.snd).congr
     (fun x => by dsimp only [Function.comp_apply]; rw [repeatStep_iterate]; simp)
 theorem replicateList_polynomial:PolyBound (replicateList (α:=α)):=by
   have hn:Linear (Realizer.nil:Realizer (fun _:ℕ×α => ([]:List α))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold replicateList
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn)))
       (polynomial_iterate_growth (linear_polynomial repeatStep_linear) 3 2 repeatStep_growth)) (linear_polynomial linear_snd)

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
open EdgeSublinearMWIS.Main.TernaryAdapter Lax759944.BinaryWordEncoding

 def nativeBit (b:Bool):List Bool:=if b then [true,false] else [false,true]
 def nativeBitRealizer:Realizer nativeBit:=
   ((Realizer.id.pair Realizer.id).comp
     ((Realizer.constant [true,false]).choose (Realizer.constant [false,true]))).congr (fun b => rfl)
 theorem nativeBit_polynomial:PolyBound nativeBitRealizer:=by
   unfold nativeBitRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_id linear_id))
     (polynomial_choose (linear_polynomial (linear_constant [true,false]))
       (linear_polynomial (linear_constant [false,true])))

 def nativeWord (A:List Bool):List Bool:= [false,false]++A.flatMap nativeBit
 def nativeWordRealizer:Realizer nativeWord:=
   ((Realizer.constant [false,false]).pair ((mapList nativeBitRealizer).comp flattenList)).comp appendBits
 theorem nativeWord_polynomial:PolyBound nativeWordRealizer:=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_constant [false,false]))
     (polynomial_comp (polynomial_mapList nativeBit_polynomial) flattenList_polynomial)) appendBits_polynomial
 theorem nativeWord_natBits (n:ℕ):
     nativeWord (natBits n)=binarySymbols (Lax759944.BinaryWordEncoding.encodeNat n):=by
   rw [natBits_eq_bits]
   simp only [nativeWord,Lax759944.BinaryWordEncoding.encodeNat,binarySymbols,List.flatMap_cons,
     symbolBits,firstBit,secondBit,List.flatMap_map]
   congr 1
   apply congrArg (fun f => n.bits.flatMap f)
   funext b
   cases b <;> rfl

 def nativeNaturalRealizer:Realizer (fun n:ℕ => nativeWord (natBits n)):=
   naturalWordRealizer.comp nativeWordRealizer
 theorem nativeNatural_polynomial:PolyBound nativeNaturalRealizer:=
   polynomial_comp naturalWord_polynomial nativeWord_polynomial

 def nativeBooleanWord (b:Bool):List Bool:=if b then [false,false,true,false] else [false,false]
 def nativeBooleanRealizer:Realizer nativeBooleanWord:=
   ((Realizer.id.pair Realizer.id).comp
     ((Realizer.constant [false,false,true,false]).choose (Realizer.constant [false,false]))).congr (fun _ => rfl)
 theorem nativeBoolean_polynomial:PolyBound nativeBooleanRealizer:=by
   unfold nativeBooleanRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_id linear_id))
     (polynomial_choose (linear_polynomial (linear_constant [false,false,true,false]))
       (linear_polynomial (linear_constant [false,false])))
 theorem nativeBoolean_code (b:Bool):
     nativeBooleanWord b=binarySymbols (Lax759944.BinaryWordEncoding.encodeNat (if b then 1 else 0)):=by
   cases b <;> decide

 def nativeSigned (s:SignedWords):List Bool:=
   nativeBooleanWord s.1++nativeWord s.2.1++nativeWord s.2.2
 def nativeSignedRealizer:Realizer nativeSigned:=
   (((Realizer.fst.comp nativeBooleanRealizer).pair ((Realizer.snd.comp Realizer.fst).comp nativeWordRealizer)).comp appendBits).pair
     ((Realizer.snd.comp Realizer.snd).comp nativeWordRealizer) |>.comp appendBits
 theorem nativeSigned_polynomial:PolyBound nativeSignedRealizer:=
   polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_pair
       (polynomial_comp (linear_polynomial linear_fst) nativeBoolean_polynomial)
       (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) nativeWord_polynomial)) appendBits_polynomial)
     (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) nativeWord_polynomial)) appendBits_polynomial

 def nativeRationalRealizer:Realizer (nativeSigned ∘ signedReduced):=signedReducedRealizer.comp nativeSignedRealizer
 theorem nativeRational_polynomial:PolyBound nativeRationalRealizer:=
   polynomial_comp signedReduced_polynomial nativeSigned_polynomial
 theorem nativeRational_code (q:RationalCode):
     nativeSigned (signedReduced (codeWords q))=
       binarySymbols (encode [if q.value.num<0 then 1 else 0,q.value.num.natAbs,q.value.den]):=by
   have hd:0<value (codeWords q).2.2:=by simpa only [codeWords,value_natBits] using q.positive
   rw [signedReduced_canonical _ hd,signedFractionValue_code]
   simp only [nativeSigned,nativeBoolean_code,nativeWord_natBits,encode,List.flatMap_cons,List.flatMap_nil,
     List.append_nil,binarySymbols,List.flatMap_append]
   simp

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack

 theorem rangeStep_first (i:ℕ) (L:List ℕ) (j:ℕ):
     ((fun s:ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).1=i+j:=by
   induction j with
   | zero => rfl
   | succ j ih => rw [Function.iterate_succ_apply']; dsimp only; omega
 theorem rangeStep_list_volume (i:ℕ) (L:List ℕ) (j:ℕ):
     volume ((fun s:ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).2≤volume L+j*(2*i+2*j+2):=by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply']
     dsimp only
     rw [volume_cons,volume_nat,rangeStep_first]
     nlinarith
 theorem rangeStep_growth (s:ℕ×List ℕ) (j:ℕ):
     volume ((fun s:ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] s)≤10*(volume s+j+1)^2:=by
   rcases s with ⟨i,L⟩
   let z:=volume (i,L)+j+1
   have hz:1≤z:=by dsimp [z]; omega
   have hbase:i+volume L+j+1≤z:=by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have hfirst:=rangeStep_first i L j
   have hlist:=rangeStep_list_volume i L j
   have hp:j*(2*i+2*j+2)≤z*(2*z+2):=Nat.mul_le_mul (by omega) (by omega)
   change volume (((fun s:ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).1,
     ((fun s:ℕ×List ℕ => (s.1+1,s.1::s.2))^[j] (i,L)).2)≤10*z^2
   rw [volume_pair,volume_nat,hfirst]
   nlinarith
 theorem range_polynomial:PolyBound Realizer.range:=by
   have hs:Linear Realizer.rangeStep:=linear_pair (linear_comp linear_fst succ_linear) linear_cons
   have hi:PolyBound Realizer.rangeStep.iterate:=polynomial_iterate_growth (linear_polynomial hs) 10 2 rangeStep_growth
   have hz:Linear (Realizer.zero:Realizer (fun _:ℕ => (0:ℕ))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   have hn:Linear (Realizer.nil:Realizer (fun _:ℕ => ([]:List ℕ))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   unfold Realizer.range
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_id)
     (linear_polynomial (linear_pair hz hn))) hi)
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic)

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α γ:Type} [Coding α] [Coding γ]

 def selectSingleton {p:α×γ→ Bool} (P:Realizer p):Realizer (fun x:α×γ => if p x then [x.1] else []):=
   (P.pair Realizer.id).comp ((((Realizer.fst.pair Realizer.nil).comp Realizer.cons)).choose Realizer.nil)
 theorem selectSingleton_polynomial {p:α×γ→ Bool} {P:Realizer p} (hP:PolyBound P):PolyBound (selectSingleton P):=by
   have hn:Linear (Realizer.nil:Realizer (fun _:α×γ => ([]:List α))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_pair hP (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial (linear_comp (linear_pair linear_fst hn) linear_cons)) (linear_polynomial hn))
 theorem filter_flatten (p:α×γ→ Bool) (xs:List α) (e:γ):
     (xs.map (fun a => if p (a,e) then [a] else [])).flatten=xs.filter (fun a => p (a,e)):=by
   induction xs with
   | nil => rfl
   | cons a xs ih => cases hp:p (a,e) <;> simp [hp,ih]
 def filterEnvironment {p:α×γ→ Bool} (P:Realizer p):
     Realizer (fun x:List α×γ => x.1.filter (fun a => p (a,x.2))):=
   ((mapEnvironment (selectSingleton P)).comp flattenList).congr (fun x => filter_flatten p x.1 x.2)
 theorem filterEnvironment_polynomial {p:α×γ→ Bool} {P:Realizer p} (hP:PolyBound P):PolyBound (filterEnvironment P):=by
   unfold filterEnvironment
   apply polynomial_congr
   exact polynomial_comp (polynomial_mapEnvironment (selectSingleton_polynomial hP)) flattenList_polynomial

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack
variable {α:Type} [Coding α]

 def tailList:Realizer (fun L:List α => L.tail):=(Uniform.tail (I:=Unit) (α:=fun _ => α)).specialize ()
 theorem tailList_linear:Linear (tailList (α:=α)):=by
   refine linear_of _ 3 (by omega) (fun L => by change volume L+2≤_; omega) ?_
   intro L
   cases L with
   | nil => simp
   | cons a L => simp only [List.tail_cons,volume_cons]; omega
 theorem tailList_volume (L:List α):volume L.tail≤volume L:=by
   cases L with
   | nil => rfl
   | cons a L => simp only [List.tail_cons,volume_cons]; omega
 theorem tail_iterate (L:List α) (k:ℕ):List.tail^[k] L=L.drop k:=by
   induction k with
   | zero => rfl
   | succ k ih => rw [Function.iterate_succ_apply',ih,List.tail_drop]
 def dropList:Realizer (fun x:List α×ℕ => x.1.drop x.2):=
   ((Realizer.snd.pair Realizer.fst).comp tailList.iterate).congr (fun x => by
     change List.tail^[x.2] x.1=x.1.drop x.2
     exact tail_iterate _ _)
 theorem dropList_polynomial:PolyBound (dropList (α:=α)):=by
   unfold dropList
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst))
     (polynomial_iterate (linear_polynomial tailList_linear) 0 (fun L => by simpa only [Nat.add_zero] using tailList_volume L))

 def countStep:Realizer (fun x:α×ℕ => x.2+1):=Realizer.snd.comp Realizer.succ
 theorem count_fold (L:List α) (k:ℕ):L.foldl (fun k (_:α) => k+1) k=k+L.length:=by
   induction L generalizing k with
   | nil => simp
   | cons a L ih => rw [List.foldl_cons,ih,List.length_cons]; omega
 theorem countStep_fold_polynomial:PolyBound (countStep (α:=α)).fold:=by
   apply polynomial_fold_bounded (linear_polynomial (linear_comp linear_snd succ_linear)) 3
   intro L k j hj
   dsimp only [Function.comp_apply]
   rw [count_fold]
   have hlen:=length_volume L
   simp only [volume_nat,volume_pair,List.length_take]
   omega
 def listLength:Realizer (fun L:List α => L.length):=
   ((Realizer.id.pair (Realizer.constant 0)).comp countStep.fold).congr (fun L => by
     change L.foldl (fun k (_:α) => k+1) 0=L.length
     simp only [count_fold,Nat.zero_add])
 theorem listLength_polynomial:PolyBound (listLength (α:=α)):=by
   unfold listLength
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial (linear_constant (0:ℕ)))) countStep_fold_polynomial

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ltNatRealizer:Realizer (fun x:ℕ×ℕ => decide (x.1<x.2)):=
   (((Realizer.snd.pair Realizer.fst).comp Realizer.le).comp Realizer.not).congr (fun x => by
     dsimp only [Function.comp_apply]
     by_cases h:x.1<x.2
     · have hn:¬x.2≤x.1:=by omega
       simp [h,hn]
     · have hn:x.2≤x.1:=by omega
       simp [h,hn])
 theorem ltNat_polynomial:PolyBound ltNatRealizer:=by
   unfold ltNatRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) nat_le_polynomial) (linear_polynomial linear_not)
 def upperRow (u n:ℕ):List (ℕ×ℕ):=((List.range n).filter (fun v => u<v)).map (fun v => (u,v))
 def largerRealizer:Realizer (fun x:ℕ×ℕ => decide (x.2<x.1)):=(Realizer.snd.pair Realizer.fst).comp ltNatRealizer
 def upperColumns:Realizer (fun x:ℕ×ℕ => (List.range x.2).filter (fun v => x.1<v)):=
   (((Realizer.snd.comp Realizer.range).pair Realizer.fst).comp (filterEnvironment largerRealizer))
 def upperRowRealizer:Realizer (fun x:ℕ×ℕ => upperRow x.1 x.2):=
   ((upperColumns.pair Realizer.fst).comp (mapEnvironment (Realizer.snd.pair Realizer.fst)))
 theorem upperRow_polynomial:PolyBound upperRowRealizer:=by
   have hc:PolyBound upperColumns:=polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) range_polynomial) (linear_polynomial linear_fst))
     (filterEnvironment_polynomial (polynomial_comp (linear_polynomial (linear_pair linear_snd linear_fst)) ltNat_polynomial))
   exact polynomial_comp (polynomial_pair hc (linear_polynomial linear_fst))
     (polynomial_mapEnvironment (linear_polynomial (linear_pair linear_snd linear_fst)))
 def vertexPairs (n:ℕ):List (ℕ×ℕ):=(List.range n).flatMap (fun u => upperRow u n)
 def vertexPairsRealizer:Realizer vertexPairs:=
   ((((Realizer.range.pair Realizer.id).comp (mapEnvironment upperRowRealizer)).comp flattenList))
 theorem vertexPairs_polynomial:PolyBound vertexPairsRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair range_polynomial (linear_polynomial linear_id))
     (polynomial_mapEnvironment upperRow_polynomial)) flattenList_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α:Type} [Coding α]

 def zipBitsStep (s:α×(List Bool×List (α×Bool))):List Bool×List (α×Bool):=
   (s.2.1.tail,(s.1,s.2.1.headD false)::s.2.2)
 def zipBitsStepRealizer:Realizer (zipBitsStep (α:=α)):=
   (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
     ((Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).comp BinaryAdder.headBit)).pair (Realizer.snd.comp Realizer.snd) |>.comp Realizer.cons))
 theorem zipBitsStep_linear:Linear (zipBitsStepRealizer (α:=α)):=
   linear_pair (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.tailBits_linear)
     (linear_comp (linear_pair (linear_pair linear_fst (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.headBit_linear))
       (linear_comp linear_snd linear_snd)) linear_cons)
 theorem zipBitsFold_volume (L:List α) (bits:List Bool) (acc:List (α×Bool)):
     volume (L.foldl (fun s a => zipBitsStep (a,s)) (bits,acc))≤volume (bits,acc)+volume L+4*L.length:=by
   induction L generalizing bits acc with
   | nil => simp
   | cons a L ih =>
     rw [List.foldl_cons]
     have ht:volume bits.tail≤volume bits:=tailList_volume bits
     have hb:=volume_bool (bits.headD false)
     have hh:=ih bits.tail ((a,bits.headD false)::acc)
     dsimp only [zipBitsStep] at hh ⊢
     simp only [volume_pair,volume_cons,List.length_cons] at hh ⊢
     omega
 theorem zipBits_fold_polynomial:PolyBound (zipBitsStepRealizer (α:=α)).fold:=by
   apply polynomial_fold_bounded (linear_polynomial zipBitsStep_linear) 5
   intro keys ⟨bits,acc⟩ j hj
   have hh:=zipBitsFold_volume (keys.take j) bits acc
   have ht:=take_volume_le keys j
   have hlen:=length_volume keys
   simp only [List.length_take] at hh
   simp only [volume_pair]
   simp only [volume_pair] at hh
   omega
 def zipBits (L:List α) (bits:List Bool):List (α×Bool):=
   ((L.foldl (fun s a => zipBitsStep (a,s)) (bits,[])).2).reverse
 def zipBitsRealizer:Realizer (fun s:List α×List Bool => zipBits s.1 s.2):=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp zipBitsStepRealizer.fold).comp (Realizer.snd.comp Realizer.reverse))
 theorem zipBits_polynomial:PolyBound (zipBitsRealizer (α:=α)):=by
   have hn:Linear (Realizer.nil:Realizer (fun _:List α×List Bool => ([]:List (α×Bool)))):=
     linear_of _ 3 (by omega) (fun _ => by change 2≤_; omega) (fun _ => by simp; omega)
   exact polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_fst)
     (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial hn))) zipBits_fold_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial_generic)
 theorem zipBitsFold_map (L:List α) (f:α→ Bool) (acc:List (α×Bool)):
     L.foldl (fun s a => zipBitsStep (a,s)) (L.map f,acc)=([],(L.map (fun a => (a,f a))).reverse++acc):=by
   induction L generalizing acc with
   | nil => rfl
   | cons a L ih =>
     rw [List.map_cons,List.foldl_cons]
     change L.foldl (fun s a => zipBitsStep (a,s)) (L.map f,(a,f a)::acc)=_
     rw [ih,List.map_cons,List.reverse_cons]
     simp only [List.append_assoc,List.singleton_append]
 theorem zipBits_map (L:List α) (f:α→ Bool):zipBits L (L.map f)=L.map (fun a => (a,f a)):=by
   rw [zipBits,zipBitsFold_map]
   simp

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
variable {α:Type} [OAI.ThreeMachine.StackCompiler.Coding α]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem eqNat_polynomial:PolyBound Realizer.eqNat:=by
   refine ⟨10000000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht:=Realizer.time_eqNat_le a b
   have hbase:a+b+1≤volume (a,b)+1:=by simp only [volume_pair,volume_nat]; omega
   have hp:=Nat.pow_le_pow_left hbase 2
   have hv:=volume_bool (decide (a=b))
   have hz:1≤(volume (a,b)+1)^2:=one_le_pow₀ (by omega)
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 10000000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · change volume (decide (a=b))≤_
     omega
 abbrev Key:=ℕ×ℕ
 abbrev Entry:=Key×Bool
 def tableTest (s:Entry×Key):Bool:=decide (s.1.1=s.2)
 def entryKey:Realizer (fun s:Entry×Key => s.1.1):=Realizer.fst.comp Realizer.fst
 def tableTestRealizer:Realizer tableTest:=
   (((((entryKey.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp Realizer.eqNat).pair
     (((entryKey.comp Realizer.snd).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.eqNat)).comp Realizer.and).congr
     (fun s => by
       dsimp only [Function.comp_apply,tableTest]
       by_cases h:s.1.1.1=s.2.1 <;> by_cases k:s.1.1.2=s.2.2 <;> simp [Prod.ext_iff,h,k])
 theorem tableTest_polynomial:PolyBound tableTestRealizer:=by
   have hk:Linear entryKey:=linear_comp linear_fst linear_fst
   unfold tableTestRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp hk linear_fst) (linear_comp linear_snd linear_fst))) eqNat_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair (linear_comp hk linear_snd) (linear_comp linear_snd linear_snd))) eqNat_polynomial))
     (linear_polynomial linear_and)
 def tableLookup (entries:List Entry) (key:Key):Bool:=
   ((entries.filter (fun e => decide (e.1=key))).map Prod.snd).headD false
 def tableLookupRealizer:Realizer (fun s:List Entry×Key => tableLookup s.1 s.2):=
   (((filterEnvironment tableTestRealizer).comp (mapList Realizer.snd)).comp BinaryAdder.headBit)
 theorem tableLookup_polynomial:PolyBound tableLookupRealizer:=
   polynomial_comp (polynomial_comp (filterEnvironment_polynomial tableTest_polynomial)
     (polynomial_mapList (linear_polynomial linear_snd))) (linear_polynomial BinaryAdder.headBit_linear)
 theorem tableLookup_map (keys:List Key) (f:Key→ Bool) (key:Key) (hk:key∈keys):
     tableLookup (keys.map (fun k => (k,f k))) key=f key:=by
   induction keys with
   | nil => simp at hk
   | cons a keys ih =>
     by_cases h:a=key
     · subst a; simp [tableLookup]
     · have hm:key∈keys:=by rcases List.mem_cons.mp hk with he|hm; exact False.elim (h he.symm); exact hm
       have hh:=ih hm
       simpa only [tableLookup,List.map_cons,List.filter_cons,h,decide_false,Bool.false_eq_true,if_false] using hh

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 theorem tableLookup_map_missing (keys:List Key) (f:Key→ Bool) (key:Key) (hk:key∉keys):
     tableLookup (keys.map (fun k => (k,f k))) key=false:=by
   induction keys with
   | nil => rfl
   | cons a keys ih =>
     have ha:a≠key:=by intro he; subst a; simp at hk
     have ht:key∉keys:=by intro hm; exact hk (List.mem_cons_of_mem a hm)
     have hh:=ih ht
     simpa only [tableLookup,List.map_cons,List.filter_cons,ha,decide_false,Bool.false_eq_true,if_false] using hh
end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def finVertexPairs (n:ℕ):List (Fin n×Fin n):=
   (List.finRange n).flatMap (fun u => ((List.finRange n).filter (fun v => u<v)).map (fun v => (u,v)))
 theorem vertexPairs_fin (n:ℕ):vertexPairs n=(finVertexPairs n).map (fun p => (p.1.val,p.2.val)):=by
   have hr:List.range n=(List.finRange n).map Fin.val:=(finRange_val n).symm
   simp only [vertexPairs,upperRow,finVertexPairs,hr,List.flatMap_map,List.map_flatMap,List.map_map,List.filter_map,Function.comp_def,Fin.lt_def]
 theorem mem_finVertexPairs {n:ℕ} (u v:Fin n):(u,v)∈finVertexPairs n↔ u<v:=by
   simp [finVertexPairs]
 theorem mem_vertexPairs {n:ℕ} (u v:Fin n) (h:u<v):(u.val,v.val)∈vertexPairs n:=by
   rw [vertexPairs_fin]
   exact List.mem_map.mpr ⟨(u,v),(mem_finVertexPairs u v).mpr h,rfl⟩
 noncomputable def adjacencyNat {n:ℕ} (G:SimpleGraph (Fin n)) (p:Key):Bool:=
   if hu:p.1<n then if hv:p.2<n then decide (G.Adj ⟨p.1,hu⟩ ⟨p.2,hv⟩) else false else false
 theorem adjacencyNat_fin {n:ℕ} (G:SimpleGraph (Fin n)) (u v:Fin n):
     adjacencyNat G (u.val,v.val)=decide (G.Adj u v):=by simp only [adjacencyNat,dif_pos u.isLt,dif_pos v.isLt]
 theorem adjacencyBits_table {n:ℕ} (G:SimpleGraph (Fin n)):
     adjacencyBits G=(vertexPairs n).map (adjacencyNat G):=by
   rw [vertexPairs_fin,List.map_map]
   have he:(fun p:Fin n×Fin n => adjacencyNat G (p.1.val,p.2.val))=(fun p => decide (G.Adj p.1 p.2)):=by
     funext p
     exact adjacencyNat_fin G p.1 p.2
   rw [show adjacencyNat G ∘ (fun p:Fin n×Fin n => (p.1.val,p.2.val))=(fun p => decide (G.Adj p.1 p.2)) from he]
   simp only [adjacencyBits,finVertexPairs,List.map_flatMap,List.map_map,Function.comp_def]
 theorem table_original_adj {n:ℕ} (G:SimpleGraph (Fin n)) (u v:Fin n) (h:u<v):
     tableLookup (zipBits (vertexPairs n) (adjacencyBits G)) (u.val,v.val)=decide (G.Adj u v):=by
   rw [adjacencyBits_table,zipBits_map,tableLookup_map _ _ _ (mem_vertexPairs u v h),adjacencyNat_fin]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def maxNatRealizer:Realizer (fun x:ℕ×ℕ => max x.1 x.2):=
   ((Realizer.le.pair Realizer.id).comp (Realizer.snd.choose Realizer.fst)).congr (fun x => by simp [max_def])
 theorem maxNat_polynomial:PolyBound maxNatRealizer:=by
   unfold maxNatRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair nat_le_polynomial (linear_polynomial linear_id))
     (polynomial_choose (linear_polynomial linear_snd) (linear_polynomial linear_fst))
 def orderedPair (p:Key):Key:=(min p.1 p.2,max p.1 p.2)
 def orderedPairRealizer:Realizer orderedPair:=minRealizer.pair maxNatRealizer
 theorem orderedPair_polynomial:PolyBound orderedPairRealizer:=polynomial_pair min_polynomial maxNat_polynomial
 theorem vertexPairs_strict (n:ℕ) (p:Key) (h:p∈vertexPairs n):p.1<p.2:=by
   obtain ⟨u,hu,hp⟩:=List.mem_flatMap.mp h
   obtain ⟨v,hv,he⟩:=List.mem_map.mp hp
   have hlt:=(List.mem_filter.mp hv).2
   subst p
   exact of_decide_eq_true hlt
 theorem table_original_any {n:ℕ} (G:SimpleGraph (Fin n)) (u v:Fin n):
     tableLookup (zipBits (vertexPairs n) (adjacencyBits G)) (orderedPair (u.val,v.val))=decide (G.Adj u v):=by
   by_cases huv:u<v
   · have hn:u.val≤v.val:=huv.le
     simp only [orderedPair,min_eq_left hn,max_eq_right hn]
     exact table_original_adj G u v huv
   · by_cases hvu:v<u
     · have hn:v.val≤u.val:=hvu.le
       simp only [orderedPair,min_eq_right hn,max_eq_left hn]
       rw [table_original_adj G v u hvu,G.adj_comm]
     · have he:u=v:=le_antisymm (le_of_not_gt hvu) (le_of_not_gt huv)
       subst v
       simp only [orderedPair,min_self,max_self]
       have hm:(u.val,u.val)∉vertexPairs n:=by intro h; have hh:=vertexPairs_strict n _ h; exact (Nat.lt_irrefl _) hh
       rw [adjacencyBits_table,zipBits_map,tableLookup_map_missing _ _ _ hm]
       simp

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
open EdgeSublinearMWIS.Main.TernaryAdapter Lax759944.BinaryWordEncoding

 def fullRow (s:ℕ×ℕ):List Key:=(List.range s.2).map (fun v => (s.1,v))
 def fullRowRealizer:Realizer fullRow:=
   (((Realizer.snd.comp Realizer.range).pair Realizer.fst).comp (mapEnvironment (Realizer.snd.pair Realizer.fst)))
 theorem fullRow_polynomial:PolyBound fullRowRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) range_polynomial)
     (linear_polynomial linear_fst)) (polynomial_mapEnvironment (linear_polynomial (linear_pair linear_snd linear_fst)))
 def fullPairs (n:ℕ):List Key:=(List.range n).flatMap (fun u => fullRow (u,n))
 def fullPairsRealizer:Realizer fullPairs:=
   (((Realizer.range.pair Realizer.id).comp (mapEnvironment fullRowRealizer)).comp flattenList)
 theorem fullPairs_polynomial:PolyBound fullPairsRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair range_polynomial (linear_polynomial linear_id))
     (polynomial_mapEnvironment fullRow_polynomial)) flattenList_polynomial
 theorem fullPairs_fin (n:ℕ):fullPairs n=
     ((List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u.val,v.val)))):=by
   have hr:List.range n=(List.finRange n).map Fin.val:=(finRange_val n).symm
   simp only [fullPairs,fullRow,hr,List.flatMap_map,List.map_map,Function.comp_def]

 def nativeTableRealizer:Realizer (fun s:ℕ×List Bool => zipBits (vertexPairs s.1) s.2):=
   ((Realizer.fst.comp vertexPairsRealizer).pair Realizer.snd).comp zipBitsRealizer
 theorem nativeTable_polynomial:PolyBound nativeTableRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) vertexPairs_polynomial)
     (linear_polynomial linear_snd)) zipBits_polynomial
 def nativeAdjacencyQuery:Realizer (fun s:Key×List Entry => nativeBooleanWord
     (tableLookup s.2 (orderedPair s.1))):=
   ((Realizer.snd.pair (Realizer.fst.comp orderedPairRealizer)).comp tableLookupRealizer).comp nativeBooleanRealizer
 theorem nativeAdjacencyQuery_polynomial:PolyBound nativeAdjacencyQuery:=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
     (polynomial_comp (linear_polynomial linear_fst) orderedPair_polynomial)) tableLookup_polynomial)
     nativeBoolean_polynomial
 def nativeAdjacency (s:ℕ×List Bool):List Bool:=
   ((fullPairs s.1).map (fun p => nativeBooleanWord (tableLookup (zipBits (vertexPairs s.1) s.2) (orderedPair p)))).flatten
 def nativeAdjacencyRealizer:Realizer nativeAdjacency:=
   ((((Realizer.fst.comp fullPairsRealizer).pair nativeTableRealizer).comp
     (mapEnvironment nativeAdjacencyQuery)).comp flattenList)
 theorem nativeAdjacency_polynomial:PolyBound nativeAdjacencyRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial linear_fst) fullPairs_polynomial) nativeTable_polynomial)
     (polynomial_mapEnvironment nativeAdjacencyQuery_polynomial)) flattenList_polynomial
 theorem nativeAdjacency_code {n:ℕ} (G:SimpleGraph (Fin n)):
     nativeAdjacency (n,adjacencyBits G)=binarySymbols (encode
       (List.ofFn (fun u => List.ofFn (fun v => if G.Adj u v then 1 else 0))).flatten):=by
   simp only [nativeAdjacency,fullPairs_fin,List.map_flatMap,List.map_map,Function.comp_def,
     table_original_any,List.finRange,List.map_ofFn]
   simp [nativeBoolean_code,encode,binarySymbols,List.flatMap_def,List.map_flatten,
     List.flatten_flatten,List.map_map,List.map_ofFn]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext u
   simp [Function.comp_def,List.map_ofFn,List.map_flatten,List.flatten_flatten,List.map_map]

 def nativeParameters (s:ℕ×List Bool):List Bool:=
   (((readMany (s.1+1) s.2).1.map (fun a => nativeSigned (signedReduced a)))).flatten
 def nativeParametersRealizer:Realizer nativeParameters:=
   (((((Realizer.fst.comp Realizer.succ).pair Realizer.snd).comp readManyRealizer).comp Realizer.fst).comp
     (mapList nativeRationalRealizer)).comp flattenList
 theorem nativeParameters_polynomial:PolyBound nativeParametersRealizer:=
   polynomial_comp (polynomial_comp (polynomial_comp (polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) (linear_polynomial succ_linear))
       (linear_polynomial linear_snd)) readMany_polynomial) (linear_polynomial linear_fst))
       (polynomial_mapList nativeRational_polynomial)) flattenList_polynomial

 def nativeInput (L:List Bool):List Bool:=
   let s:=graphStart L
   nativeWord (natBits s.1)++nativeAdjacency (s.1,s.2.1)++nativeParameters (s.1,s.2.2)
 def nativeInputRealizer:Realizer nativeInput:=graphStartRealizer.comp
   (((((Realizer.fst.comp nativeNaturalRealizer).pair
       ((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp nativeAdjacencyRealizer)).comp appendBits).pair
     ((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp nativeParametersRealizer)).comp appendBits)
 theorem nativeInput_polynomial:PolyBound nativeInputRealizer:=
   polynomial_comp graphStart_polynomial (polynomial_comp (polynomial_pair
     (polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) nativeNatural_polynomial)
       (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_fst)))
         nativeAdjacency_polynomial)) appendBits_polynomial)
     (polynomial_comp (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_snd)))
       nativeParameters_polynomial)) appendBits_polynomial)

 theorem nativeParameters_code {n:ℕ} (w:Fin n→ RationalCode) (ε:RationalCode):
     nativeParameters (n,rationalData w ε)=binarySymbols (encode
       (Lax263307.IndependentSetEncoding.encodeParameters (fun v => (w v).value) ε.value)):=by
   let qs:=List.ofFn w++[ε]
   have hl:qs.length=n+1:=by simp [qs]
   have he:rationalData w ε=qs.flatMap RationalCode.bits:=by
     simp [qs,rationalData,List.flatMap_def,List.map_ofFn,Function.comp_def]
   simp only [nativeParameters,← hl,he]
   rw [show qs.flatMap RationalCode.bits=qs.flatMap RationalCode.bits++[] by simp,
     readMany_codes]
   simp only [List.map_map]
   have hn:∀ q:RationalCode,nativeSigned (signedReduced (codeWords q))=
       binarySymbols (encode (Lax263307.IndependentSetEncoding.encodeRational q.value)):=
     nativeRational_code
   simp only [Function.comp_def,hn]
   simp [qs,Lax263307.IndependentSetEncoding.encodeParameters,encode,binarySymbols,
     List.flatMap_def,List.map_map,List.map_flatten,List.flatten_flatten,List.map_ofFn]
   apply congrArg List.flatten
   apply congrArg List.ofFn
   funext v
   simp [Function.comp_def,List.map_flatten,List.flatten_flatten,List.map_map]

 theorem nativeInput_code {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
     (w:Fin n→ RationalCode) (ε:RationalCode):
     nativeInput (weightedInput G w ε)=binarySymbols (encode
       (Lax263307.IndependentSetEncoding.encodeInput G (fun v => (w v).value) ε.value)):=by
   unfold nativeInput
   rw [graphStart_weighted]
   simp only [nativeWord_natBits,nativeAdjacency_code,nativeParameters_code]
   simp [Lax263307.IndependentSetEncoding.encodeInput,encode,binarySymbols,
     List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_assoc]
   apply congrArg (fun rows:List (List ℕ) => List.flatMap symbolBits
     (List.flatMap Lax759944.BinaryWordEncoding.encodeNat rows.flatten))
   apply congrArg List.ofFn
   funext u
   apply congrArg List.ofFn
   funext v
   split_ifs <;> rfl

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open OAI.ThreeMachine.StackCompiler RawStack RealizerBounds TernaryAdapter
open Lax759944.BinaryWordEncoding Lax263307.IndependentSetEncoding

 theorem canonicalParameters_le_input {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ):rationalBitSize w ε≤ bitSize (encodeInput G w ε):=by
  simp only [encodeInput,Lax455465Proofs.WordSize.bitSize_append]
  change bitSize (encodeParameters w ε)≤ _
  omega

 theorem canonical_input_polynomial:∃ B p:ℕ,0<B∧ 0<p∧
    ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (w:Fin n→ RationalCode) (ε:RationalCode),
      bitSize (encodeInput G (fun v => (w v).value) ε.value)+1≤
        B*((weightedInput G w ε).length+1)^p:=by
  obtain ⟨C,q,hC,hclock⟩:=nativeInput_polynomial
  refine ⟨C*6^q+1,q+1,by positivity,by omega,?_⟩
  intro n G inst w ε
  let input:=weightedInput G w ε
  have hc:=(hclock input).2
  have hlen:=bits_length_volume (nativeInput input)
  have hvol:=BinaryAdder.volume_bits input
  have he:=nativeInput_code G w ε
  have hsize:(nativeInput input).length=2*bitSize (encodeInput G (fun v => (w v).value) ε.value):=by
    rw [he,binarySymbols_length]
    rfl
  have hbase:volume input+1≤ 6*(input.length+1):=by omega
  have hp:=hc.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
  rw [mul_pow] at hp
  have hq:(input.length+1)^q≤ (input.length+1)^(q+1):=Nat.pow_le_pow_right (by omega) (by omega)
  have ht:=hp.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (C*6^q) hq)
  have h1:1≤(input.length+1)^(q+1):=Nat.one_le_pow _ _ (by omega)
  change _≤ (C*6^q+1)*(input.length+1)^(q+1)
  nlinarith only [hlen,hsize,ht,h1]

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

set_option maxHeartbeats 500000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasRuntime

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses AlgorithmParameters WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive NativePolynomialEnvelope

def workspaceAt {C:GraphClass} (i:Fixed C) (R:ℕ):ℕ:=i.budgetCoefficient*(R+1)^i.budgetExponent

def budgetBound {C:GraphClass} (i:Fixed C) (R:ℕ):ℕ:=
  i.envelopeCoefficient+i.envelopeExponent+i.budgetCoefficient+i.budgetExponent+
    2*R+R+R+R+R+R+R+(R+1)^i.budgetExponent+workspaceAt i R+2*(workspaceAt i R+1)+100

def widthBound {C:GraphClass} (i:Fixed C) (J:ℕ):ℕ:=
  NativeRootWorkspace.hostHeight i.cfg (workspaceAt i J)+budgetBound i J+
    100*(2*J+1)^4+16*(J+1)+100

def frontendBound {C:GraphClass} (i:Fixed C) (J:ℕ):ℕ:=
  NativeBlowUp.cost J J+(16*(J*J)+14)+18+(14*(2*J+2)+28)+
    (48*J+12*i.envelopeExponent+12*i.budgetExponent+78)+(24*J+44*J+36)+20

def allowance {C:GraphClass} (i:Fixed C):ℕ:=
  Lax455465Proofs.RamTransfer.layoutAllowance
    (Lax455465Proofs.RamAutomaticLayout.layout (NativeWeightedExecution.command i))

theorem polynomial:∀ {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C),
  Lax263307Proofs.NativePolynomialEnvelope.Bounded fun (J:ℕ) =>
    Lax263307Proofs.NativeQptasRuntime.widthBound i J + Lax263307Proofs.NativeQptasRuntime.allowance i +
        10 * Lax263307Proofs.NativeQptasRuntime.frontendBound i J +
      1:=
fun {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C) =>
  id
    (Lax263307Proofs.NativePolynomialEnvelope.add
      (Lax263307Proofs.NativePolynomialEnvelope.add
        (Lax263307Proofs.NativePolynomialEnvelope.add
          (Lax263307Proofs.NativePolynomialEnvelope.add
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              Lax263307Proofs.NativePolynomialEnvelope.identity
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 36)
                                  (Lax263307Proofs.NativePolynomialEnvelope.pow 4
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 5)
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                            (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 20))))
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 10))
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                            (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1))
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 4)
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 20))))
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 20)))
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                      (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                        i.budgetCoefficient)
                                                      (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                                          Lax263307Proofs.NativePolynomialEnvelope.identity
                                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2))
                                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                          (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                            i.budgetCoefficient)
                                                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                                            (Lax263307Proofs.NativePolynomialEnvelope.add
                                                              Lax263307Proofs.NativePolynomialEnvelope.identity
                                                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                                    (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                      (Lax263307Proofs.NativeCoreMachine.frameArrays i.cfg).length))
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                    (Lax263307Proofs.NativeCoreMachine.frameScalars i.cfg).length)))
                                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                                      (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                        i.budgetCoefficient)
                                                      (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                                          Lax263307Proofs.NativePolynomialEnvelope.identity
                                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant
                                                  (Lax263307Proofs.NativeCoreMachine.frameArrays i.cfg).length)))
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant
                                              (Lax263307Proofs.NativeCoreMachine.frameScalars i.cfg).length))
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                              (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                                  Lax263307Proofs.NativePolynomialEnvelope.identity
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                                              (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                              (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                                  Lax263307Proofs.NativePolynomialEnvelope.identity
                                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))))
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                            (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))))
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                        (Lax263307Proofs.NativePolynomialEnvelope.add
                                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                            (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                        (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            Lax263307Proofs.NativePolynomialEnvelope.identity
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                        (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                          (Lax263307Proofs.NativePolynomialEnvelope.add
                                            Lax263307Proofs.NativePolynomialEnvelope.identity
                                            (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 2)))
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                    (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 80)))
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 100)))
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                  (Lax263307Proofs.NativePolynomialEnvelope.mul
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                    (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                  (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant
                                (Lax455465Proofs.RamVirtualConstants.allowance i.cfg.rounded)))
                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                  (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                                (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    Lax263307Proofs.NativePolynomialEnvelope.identity
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))))
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 8)
                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                              (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                              (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  Lax263307Proofs.NativePolynomialEnvelope.identity
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))))
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 100)))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 100))
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.add
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant
                                          (i.envelopeCoefficient + i.envelopeExponent + i.budgetCoefficient +
                                            i.budgetExponent))
                                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                                          Lax263307Proofs.NativePolynomialEnvelope.identity))
                                      Lax263307Proofs.NativePolynomialEnvelope.identity)
                                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                                Lax263307Proofs.NativePolynomialEnvelope.identity)
                              Lax263307Proofs.NativePolynomialEnvelope.identity)
                            Lax263307Proofs.NativePolynomialEnvelope.identity)
                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              Lax263307Proofs.NativePolynomialEnvelope.identity
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                          (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              Lax263307Proofs.NativePolynomialEnvelope.identity
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                            (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                Lax263307Proofs.NativePolynomialEnvelope.identity
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 100)))
                (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 100)
                  (Lax263307Proofs.NativePolynomialEnvelope.pow 4
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))))
              (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
                  (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
            (Lax263307Proofs.NativePolynomialEnvelope.constant 100))
          (Lax263307Proofs.NativePolynomialEnvelope.constant (Lax263307Proofs.NativeQptasRuntime.allowance i)))
        (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 10)
          (Lax263307Proofs.NativePolynomialEnvelope.add
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 12)
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.add
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        Lax263307Proofs.NativePolynomialEnvelope.identity
                                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                                        (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                        Lax263307Proofs.NativePolynomialEnvelope.identity))
                                    (Lax263307Proofs.NativePolynomialEnvelope.constant 3)))
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 110)
                                  Lax263307Proofs.NativePolynomialEnvelope.identity))
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 78))
                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                              (Lax263307Proofs.NativePolynomialEnvelope.add
                                (Lax263307Proofs.NativePolynomialEnvelope.mul
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 15)
                                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 19))
                              Lax263307Proofs.NativePolynomialEnvelope.identity))
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            (Lax263307Proofs.NativePolynomialEnvelope.mul
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 32)
                              Lax263307Proofs.NativePolynomialEnvelope.identity)
                            Lax263307Proofs.NativePolynomialEnvelope.identity))
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 18))
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            Lax263307Proofs.NativePolynomialEnvelope.identity
                            Lax263307Proofs.NativePolynomialEnvelope.identity))
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 14)))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 18))
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 14)
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                          Lax263307Proofs.NativePolynomialEnvelope.identity)
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 28)))
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 48)
                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                      (Lax263307Proofs.NativePolynomialEnvelope.constant (12 * i.envelopeExponent)))
                    (Lax263307Proofs.NativePolynomialEnvelope.constant (12 * i.budgetExponent)))
                  (Lax263307Proofs.NativePolynomialEnvelope.constant 78)))
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 24)
                    Lax263307Proofs.NativePolynomialEnvelope.identity)
                  (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 44)
                    Lax263307Proofs.NativePolynomialEnvelope.identity))
                (Lax263307Proofs.NativePolynomialEnvelope.constant 36)))
            (Lax263307Proofs.NativePolynomialEnvelope.constant 20))))
      (Lax263307Proofs.NativePolynomialEnvelope.constant 1))

theorem local_polynomial:∀ {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C),
  Lax263307Proofs.NativePolynomialEnvelope.Bounded fun (R:ℕ) =>
    Lax263307Proofs.NativeLocalTime.steps (Lax263307Proofs.NativeQptasRuntime.workspaceAt i R) +
        Lax263307Proofs.NativeLocalTime.branches (Lax263307Proofs.NativeQptasRuntime.workspaceAt i R) +
      Lax263307Proofs.NativeLocalTime.time i.cfg (Lax263307Proofs.NativeQptasRuntime.workspaceAt i R)
        (2 * (Lax263307Proofs.NativeQptasRuntime.workspaceAt i R + 1)):=
fun {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C) =>
  Exists.casesOn (Lax263307Proofs.NativeLocalTime.polynomial i.cfg)
    fun (P:Polynomial ℕ)
      (hP:
        ∀ (R:ℕ),
          (fun (W:ℕ) =>
                Lax263307Proofs.NativeLocalTime.steps W + Lax263307Proofs.NativeLocalTime.branches W +
                  Lax263307Proofs.NativeLocalTime.time i.cfg W (2 * (W + 1)))
              R≤
            Polynomial.eval R P) =>
    Lax263307Proofs.NativePolynomialEnvelope.of_le
      (Lax263307Proofs.NativePolynomialEnvelope.eval P
        (have this:
          Lax263307Proofs.NativePolynomialEnvelope.Bounded (Lax263307Proofs.NativeQptasRuntime.workspaceAt i):=
          id
            (id
              (Lax263307Proofs.NativePolynomialEnvelope.mul
                (Lax263307Proofs.NativePolynomialEnvelope.constant i.budgetCoefficient)
                (Lax263307Proofs.NativePolynomialEnvelope.pow i.budgetExponent
                  (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
                    (Lax263307Proofs.NativePolynomialEnvelope.constant 1)))));
        this))
      fun (R:ℕ) => hP (Lax263307Proofs.NativeQptasRuntime.workspaceAt i R)

theorem host_mono (cfg:NativeCoreMachine.Config) {W V:ℕ} (h:W≤ V):
    NativeRootWorkspace.hostHeight cfg W≤ NativeRootWorkspace.hostHeight cfg V:=by
  dsimp only [NativeRootWorkspace.hostHeight,NativeNearResources.wordHeight,NativeRootWorkspace.frameLength,
    NativeRootWorkspace.stride,NativeRoundedResources.wordHeight]
  gcongr

theorem parameters {C:GraphClass} (i:Fixed C) (N:ℕ) (ε:ℚ) (hε:0<ε):
    let D:=denominator N ε
    let X:=D*logarithm N
    let R:=resource i N ε
    0< D∧ 1≤ X∧ N≤ R∧ D≤ R∧ logarithm N≤ R∧ X≤ R∧
      X^i.envelopeExponent≤ R∧ i.envelopeCoefficient*X^i.envelopeExponent≤ R:=by
  dsimp only
  let D:=denominator N ε
  let X:=D*logarithm N
  let R:=resource i N ε
  have hD:0< D:=lt_of_lt_of_le (by decide:0<4)
    (Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have hL:1≤ logarithm N:=by dsimp only [logarithm]; omega
  have hX:1≤ X:=Nat.mul_pos hD hL
  have hH:i.envelopeCoefficient*X^i.envelopeExponent≤ R:=Nat.lt_two_pow_self.le
  have hP:X^i.envelopeExponent≤ R:=
    (Nat.le_mul_of_pos_left _ i.envelopeCoefficientPositive).trans hH
  have hXR:X≤ R:=(le_self_pow hX (Nat.ne_of_gt i.envelopeExponentPositive)).trans hP
  have hNR:N≤ R:=by
    by_cases hn:0< N
    · have h:=i.uniform N D N hD hn (Nat.le_refl N)
      change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D≤ R at h
      dsimp only [ParameterResources.resource] at h
      omega
    · omega
  have hDR:D≤ R:=(Nat.le_mul_of_pos_right _ hL).trans hXR
  have hLR:logarithm N≤ R:=(Nat.le_mul_of_pos_left _ hD).trans hXR
  exact ⟨hD,hX,hNR,hDR,hLR,hXR,hP,hH⟩

theorem budget_guard {C:GraphClass} (i:Fixed C) (N:ℕ) (ε:ℚ) (hε:0<ε):
    NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent
      N (denominator N ε)≤ budgetBound i (resource i N ε):=by
  have hp:=parameters i N ε hε
  dsimp only [NativeRootBudget.guard,NativeRootResource.budget,budgetBound,workspaceAt]
  gcongr
  all_goals first | exact Nat.le_refl _ | exact hp.2.2.1 | exact hp.2.2.2.1 | exact hp.2.2.2.2.1 |
    exact hp.2.2.2.2.2.1 | exact hp.2.2.2.2.2.2.1 | exact hp.2.2.2.2.2.2.2

theorem frontend_bound {C:GraphClass} (i:Fixed C) {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ) (hε:0<ε):
    NativeWeightedExecution.cost i weights ε≤ NativeUnweightedExecution.cost i.cfg (order weights ε) (workspace i (order weights ε) ε)+
      frontendBound i (max (resource i (order weights ε) ε) (rationalBitSize weights ε)):=by
  let N:=order weights ε
  let R:=resource i N ε
  let J:=max R (rationalBitSize weights ε)
  have hp:=parameters i N ε hε
  have hR:R≤ J:=Nat.le_max_left _ _
  have hn:n≤ J:=(NativeInputBounds.order_le_bits weights ε).trans (Nat.le_max_right _ _)
  have hN:N≤ J:=hp.2.2.1.trans hR
  have hblowup:NativeBlowUp.cost n N≤ NativeBlowUp.cost J J:=by
    dsimp only [NativeBlowUp.cost]; gcongr
  have hbudget:budgetCost i N ε≤ 48*J+12*i.envelopeExponent+12*i.budgetExponent+78:=by
    have hs:N.size≤ N:=Nat.size_le.mpr Nat.lt_two_pow_self
    have ht:(2*N).size≤ 2*N:=Nat.size_le.mpr Nat.lt_two_pow_self
    have hexp:i.envelopeCoefficient*(denominator N ε*logarithm N)^i.envelopeExponent≤ J:=hp.2.2.2.2.2.2.2.trans hR
    dsimp only [budgetCost]
    omega
  have hdepth:RecursionDepth.depth N≤ 2*J+2:=by
    have h:=Lax263307Proofs.RecursionDepth.logarithmic_bound N
    have hl:=Nat.log2_le_self N
    omega
  have hNN:N*N≤ J*J:=Nat.mul_self_le_mul_self hN
  change NativeQptasPositive.cost i n N ε≤ NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+frontendBound i J
  dsimp only [NativeQptasPositive.cost,frontendBound]
  omega

end Lax263307Proofs.NativeQptasRuntime

end

section

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000

namespace Lax263307Proofs.NativeQptasComplexity

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses AlgorithmParameters WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive NativeQptasRuntime

theorem exponent_mono (A d e n D:ℕ) (hD:0< D) (hde:d≤ e):
    NativeRootResource.envelope A d n D≤ NativeRootResource.envelope A e n D:=by
  have hX:1≤ D*logarithm n:=Nat.mul_pos hD (by dsimp only [logarithm]; omega)
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX hde))

theorem scale (A d n D q:ℕ) (hD:0< D):
    q*NativeRootResource.envelope A d n D≤ NativeRootResource.envelope (A+q) d n D:=by
  let T:=(D*logarithm n)^d
  have hT:1≤ T:=Nat.one_le_pow _ _ (Nat.mul_pos hD (by dsimp only [logarithm]; omega))
  calc
    _≤ 2^q*2^(A*T):=Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
    _=2^(q+A*T):=(pow_add _ _ _).symm
    _≤ 2^((A+q)*T):=Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left q hT])

theorem add (A B d n D:ℕ) (hD:0< D):
    NativeRootResource.envelope A d n D+NativeRootResource.envelope B d n D≤
      NativeRootResource.envelope (A+B+1) d n D:=by
  let T:=(D*logarithm n)^d
  have hT:1≤ T:=Nat.one_le_pow _ _ (Nat.mul_pos hD (by dsimp only [logarithm]; omega))
  have hA:2^(A*T)≤ 2^((A+B)*T):=Nat.pow_le_pow_right (by decide) (by nlinarith only [])
  have hB:2^(B*T)≤ 2^((A+B)*T):=Nat.pow_le_pow_right (by decide) (by nlinarith only [])
  calc
    _≤ 2^((A+B)*T)+2^((A+B)*T):=Nat.add_le_add hA hB
    _=2^((A+B)*T+1):=by rw [pow_succ]; omega
    _≤ 2^((A+B+1)*T):=Nat.pow_le_pow_right (by decide) (by nlinarith only [hT])

theorem core_bound {C:GraphClass} (i:Fixed C):
    ∃ K:ℕ,∀ N ε,0<ε→ NativeUnweightedExecution.cost i.cfg N (workspace i N ε)≤
      NativeRootResource.envelope K (i.envelopeExponent+1) N (denominator N ε):=by
  obtain ⟨B,f,hB,hf,hbound⟩:=NativePolynomialEnvelope.monomial (local_polynomial i)
  let A:=3*(B+f*(i.envelopeCoefficient+1)+1)
  refine ⟨A+i.envelopeCoefficient+9,?_⟩
  intro N ε hε
  let D:=denominator N ε
  let X:=D*logarithm N
  let R:=resource i N ε
  let W:=workspace i N ε
  let U:=NativeRootResource.envelope A (i.envelopeExponent+1) N D
  have hp:=parameters i N ε hε
  have hD:0< D:=hp.1
  have hR:1≤ R:=Nat.one_le_two_pow
  have hU:1≤ U:=Nat.one_le_two_pow
  have caps:=hbound R
  change NativeLocalTime.steps W+NativeLocalTime.branches W+NativeLocalTime.time i.cfg W (2*(W+1))≤ B*(R+1)^f at caps
  let NS:=NativeRecursionBudget.work (NativeLocalTime.steps W) (NativeLocalTime.branches W) (RecursionDepth.depth N)
  let NT:=NativeRecursionBudget.work (NativeLocalTime.time i.cfg W (2*(W+1))) (NativeLocalTime.branches W) (RecursionDepth.depth N)
  have hs:NS≤ U:=NativeRootResource.recursive_bound B f i.envelopeCoefficient i.envelopeExponent N D
    (NativeLocalTime.steps W) (NativeLocalTime.branches W) hD (by exact (by omega:NativeLocalTime.steps W≤ B*(R+1)^f))
    (by exact (by omega:NativeLocalTime.branches W≤ B*(R+1)^f))
  have ht:NT≤ U:=NativeRootResource.recursive_bound B f i.envelopeCoefficient i.envelopeExponent N D
    (NativeLocalTime.time i.cfg W (2*(W+1))) (NativeLocalTime.branches W) hD
    (by exact (by omega:NativeLocalTime.time i.cfg W (2*(W+1))≤ B*(R+1)^f))
    (by exact (by omega:NativeLocalTime.branches W≤ B*(R+1)^f))
  have hlocal:NativeUnweightedExecution.cost i.cfg N W≤ 397*U*R:=by
    change (NT+26+68*(NS+3))*N+98≤ _
    have hnR:N≤ R:=hp.2.2.1
    have htimes:(NT+26+68*(NS+3))*N≤ 299*U*R:=
      Nat.mul_le_mul (by nlinarith only [hs,ht,hU]) hnR
    have hUR:1≤ U*R:=Nat.mul_pos hU hR
    nlinarith only [htimes,Nat.mul_le_mul_left 98 hUR]
  have hRR:R≤ NativeRootResource.envelope i.envelopeCoefficient (i.envelopeExponent+1) N D:=
    exponent_mono _ _ _ _ _ hD (by omega)
  have hT:1≤ X^(i.envelopeExponent+1):=Nat.one_le_pow _ _ hp.2.1
  calc
    NativeUnweightedExecution.cost i.cfg N W≤ 397*U*R:=hlocal
    _≤ 2^9*2^(A*X^(i.envelopeExponent+1))*2^(i.envelopeCoefficient*X^(i.envelopeExponent+1)):=
      Nat.mul_le_mul (Nat.mul_le_mul_right _ (by decide:397≤ 2^9)) hRR
    _=2^(9+A*X^(i.envelopeExponent+1)+i.envelopeCoefficient*X^(i.envelopeExponent+1)):=by rw [←pow_add,←pow_add]
    _≤ 2^((A+i.envelopeCoefficient+9)*X^(i.envelopeExponent+1)):=
      Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left 9 hT])

theorem copy_bound {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ) (hε:0<ε):
    order weights ε≤ 2*n^2*⌈ε⁻¹⌉₊:=by
  by_cases hz:order weights ε=0
  · omega
  · have hp:=positive_parameters weights ε (by omega)
    exact NativeFinalBounds.copy_order (PositiveWeights.positiveWeights weights) ε
      (fun v => le_max_right _ _) hp.1 hε hp.2

end Lax263307Proofs.NativeQptasComplexity

end

section

set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax263307 GraphClasses
open Lax263307.IndependentSetEncoding
open Lax263307Proofs NativeQptasImplementation NativeQptasPositive NativeQptasRuntime

def frontendUniversal (J:ℕ):ℕ:=
  NativeBlowUp.cost J J+(16*(J*J)+14)+18+(14*(2*J+2)+28)+
    (48*J+78)+(24*J+44*J+36)+20

def rationalOverhead (ℓ:ℕ):ℕ:=100*(2*ℓ+1)^4+16*(ℓ+1)+10*frontendUniversal ℓ

 theorem rationalOverhead_polynomial:Lax263307Proofs.NativePolynomialEnvelope.Bounded EdgeSublinearMWIS.Main.RamBridge.rationalOverhead:=
id
  (id
    (Lax263307Proofs.NativePolynomialEnvelope.add
      (Lax263307Proofs.NativePolynomialEnvelope.add
        (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 100)
          (Lax263307Proofs.NativePolynomialEnvelope.pow 4
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                Lax263307Proofs.NativePolynomialEnvelope.identity)
              (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
        (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
          (Lax263307Proofs.NativePolynomialEnvelope.add Lax263307Proofs.NativePolynomialEnvelope.identity
            (Lax263307Proofs.NativePolynomialEnvelope.constant 1))))
      (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 10)
        (Lax263307Proofs.NativePolynomialEnvelope.add
          (Lax263307Proofs.NativePolynomialEnvelope.add
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.add
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.add
                        (Lax263307Proofs.NativePolynomialEnvelope.add
                          (Lax263307Proofs.NativePolynomialEnvelope.add
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 12)
                                (Lax263307Proofs.NativePolynomialEnvelope.add
                                  (Lax263307Proofs.NativePolynomialEnvelope.add
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      Lax263307Proofs.NativePolynomialEnvelope.identity
                                      Lax263307Proofs.NativePolynomialEnvelope.identity)
                                    (Lax263307Proofs.NativePolynomialEnvelope.mul
                                      (Lax263307Proofs.NativePolynomialEnvelope.constant 3)
                                      Lax263307Proofs.NativePolynomialEnvelope.identity))
                                  (Lax263307Proofs.NativePolynomialEnvelope.constant 3)))
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 110)
                                Lax263307Proofs.NativePolynomialEnvelope.identity))
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 78))
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            (Lax263307Proofs.NativePolynomialEnvelope.add
                              (Lax263307Proofs.NativePolynomialEnvelope.mul
                                (Lax263307Proofs.NativePolynomialEnvelope.constant 15)
                                Lax263307Proofs.NativePolynomialEnvelope.identity)
                              (Lax263307Proofs.NativePolynomialEnvelope.constant 19))
                            Lax263307Proofs.NativePolynomialEnvelope.identity))
                        (Lax263307Proofs.NativePolynomialEnvelope.mul
                          (Lax263307Proofs.NativePolynomialEnvelope.mul
                            (Lax263307Proofs.NativePolynomialEnvelope.constant 32)
                            Lax263307Proofs.NativePolynomialEnvelope.identity)
                          Lax263307Proofs.NativePolynomialEnvelope.identity))
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 18))
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 16)
                        (Lax263307Proofs.NativePolynomialEnvelope.mul Lax263307Proofs.NativePolynomialEnvelope.identity
                          Lax263307Proofs.NativePolynomialEnvelope.identity))
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 14)))
                  (Lax263307Proofs.NativePolynomialEnvelope.constant 18))
                (Lax263307Proofs.NativePolynomialEnvelope.add
                  (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 14)
                    (Lax263307Proofs.NativePolynomialEnvelope.add
                      (Lax263307Proofs.NativePolynomialEnvelope.mul
                        (Lax263307Proofs.NativePolynomialEnvelope.constant 2)
                        Lax263307Proofs.NativePolynomialEnvelope.identity)
                      (Lax263307Proofs.NativePolynomialEnvelope.constant 2)))
                  (Lax263307Proofs.NativePolynomialEnvelope.constant 28)))
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 48)
                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                (Lax263307Proofs.NativePolynomialEnvelope.constant 78)))
            (Lax263307Proofs.NativePolynomialEnvelope.add
              (Lax263307Proofs.NativePolynomialEnvelope.add
                (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 24)
                  Lax263307Proofs.NativePolynomialEnvelope.identity)
                (Lax263307Proofs.NativePolynomialEnvelope.mul (Lax263307Proofs.NativePolynomialEnvelope.constant 44)
                  Lax263307Proofs.NativePolynomialEnvelope.identity))
              (Lax263307Proofs.NativePolynomialEnvelope.constant 36)))
          (Lax263307Proofs.NativePolynomialEnvelope.constant 20)))))

 theorem frontend_split {C:GraphClass} (i:Fixed C) (R ℓ:ℕ):
    frontendBound i (max R ℓ)≤ frontendBound i R+frontendUniversal ℓ:=by
  by_cases h:ℓ≤ R
  · rw [max_eq_left h]; omega
  · rw [max_eq_right (by omega:R≤ ℓ)]
    simp only [frontendBound,frontendUniversal]
    omega

 theorem width_split {C:GraphClass} (i:Fixed C) {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ)
    (hε:0<ε):
    NativeQptasWordBounds.width i weights ε≤
      widthBound i (resource i (order weights ε) ε)+
        100*(2*rationalBitSize weights ε+1)^4+16*(rationalBitSize weights ε+1):=by
  let N:=order weights ε
  let R:=resource i N ε
  let ℓ:=rationalBitSize weights ε
  have hp:=parameters i N ε hε
  have hn:=NativeInputBounds.order_le_bits weights ε
  have hN:N≤ R:=hp.2.2.1
  have hh:=host_mono i.cfg (show workspace i N ε≤ workspaceAt i R from le_refl _)
  have hb:=budget_guard i N ε hε
  change NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)≤ budgetBound i R at hb
  have hs:100*(n+N+1)^4≤ 100*(2*R+1)^4+100*(2*ℓ+1)^4:=by
    by_cases h:ℓ≤ R
    · have hbase:n+N+1≤ 2*R+1:=by omega
      have ht:=Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hbase 4)
      omega
    · have hbase:n+N+1≤ 2*ℓ+1:=by omega
      have ht:=Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hbase 4)
      omega
  change NativeRootWorkspace.hostHeight i.cfg (workspace i N ε)+
    NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)+
      100*(n+N+1)^4+16*(ℓ+1)+100≤ _
  change _≤ NativeRootWorkspace.hostHeight i.cfg (workspaceAt i R)+budgetBound i R+
    100*(2*R+1)^4+16*(R+1)+100+100*(2*ℓ+1)^4+16*(ℓ+1)
  omega

 theorem universal_rational_overhead:∃ q Q:ℕ,0<q∧ 0<Q∧ ∀ {C:GraphClass} (i:Fixed C),
    ∃ K:ℕ,∀ n (weights:Fin n→ ℚ) ε,0<ε→
      NativeQptasWordBounds.width i weights ε+allowance i+10*NativeWeightedExecution.cost i weights ε+1≤
        NativeRootResource.envelope K (i.envelopeExponent+1) (order weights ε) (denominator (order weights ε) ε)+
          Q*(rationalBitSize weights ε+1)^q:=by
  obtain ⟨Q,q,hQ,hq,hbit⟩:=NativePolynomialEnvelope.monomial rationalOverhead_polynomial
  refine ⟨q,Q,hq,hQ,?_⟩
  intro C i
  obtain ⟨B,f,hB,hf,hbound⟩:=NativePolynomialEnvelope.monomial (polynomial i)
  obtain ⟨A,hcore⟩:=NativeQptasComplexity.core_bound i
  let K₀:=B+f*(i.envelopeCoefficient+1)
  refine ⟨A+10+K₀+1,?_⟩
  intro n weights ε hε
  let N:=order weights ε
  let D:=denominator N ε
  let R:=resource i N ε
  let ℓ:=rationalBitSize weights ε
  have hD:0<D:=(parameters i N ε hε).1
  have hw:=width_split i weights ε hε
  have ht:=frontend_bound i weights ε hε
  change NativeQptasWordBounds.width i weights ε≤ widthBound i R+100*(2*ℓ+1)^4+16*(ℓ+1) at hw
  change NativeWeightedExecution.cost i weights ε≤ NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+frontendBound i (max R ℓ) at ht
  have hf:=frontend_split i R ℓ
  have hb:=hbound R
  have hbits:=hbit ℓ
  have hsplit:NativeQptasWordBounds.width i weights ε+allowance i+10*NativeWeightedExecution.cost i weights ε+1≤
      10*NativeUnweightedExecution.cost i.cfg N (workspace i N ε)+B*(R+1)^f+Q*(ℓ+1)^q:=by
    dsimp only [rationalOverhead] at hbits
    omega
  have hcoreScaled:=(Nat.mul_le_mul_left 10 (hcore N ε hε)).trans
    (NativeQptasComplexity.scale A (i.envelopeExponent+1) N D 10 hD)
  have hbudget:B*(R+1)^f≤ NativeRootResource.envelope K₀ i.envelopeExponent N D:=
    NativeRootResource.budget_bound B f i.envelopeCoefficient i.envelopeExponent N D hD
  have hbudget':=hbudget.trans (NativeQptasComplexity.exponent_mono K₀ i.envelopeExponent
    (i.envelopeExponent+1) N D hD (by omega))
  have hsum:=(Nat.add_le_add hcoreScaled hbudget').trans
    (NativeQptasComplexity.add (A+10) K₀ (i.envelopeExponent+1) N D hD)
  exact hsplit.trans (Nat.add_le_add_right hsum _)

end EdgeSublinearMWIS.Main.RamBridge

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]

 def Expanded {f:α→ β} (R:Realizer f) (N:α→ ℕ):Prop:=
   ∃ C q:ℕ,0<C∧ ∀x,R.time x≤C*(volume x+N x+1)^q∧ volume (f x)≤C*(volume x+N x+1)^q
 theorem polynomial_expanded {f:α→ β} {R:Realizer f} (hR:PolyBound R) (N:α→ ℕ):Expanded R N:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   refine ⟨C,q,hC,?_⟩
   intro x
   have hp:=Nat.pow_le_pow_left (show volume x+1≤volume x+N x+1 by omega) q
   exact ⟨(hR x).1.trans (Nat.mul_le_mul_left C hp),(hR x).2.trans (Nat.mul_le_mul_left C hp)⟩
 theorem expanded_comp {f:α→ β} {g:β→ γ} {R:Realizer f} {S:Realizer g} {N:α→ ℕ}
     (hR:Expanded R N) (hS:PolyBound S):Expanded (R.comp S) N:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   refine ⟨C+D*(C+1)^r+10*(C+1),q+q*r,by positivity,?_⟩
   intro x
   let z:=volume x+N x+1
   have hz:1≤z:=by dsimp [z]; omega
   have hp:1≤z^q:=one_le_pow₀ hz
   have h1:=hR x
   change R.time x≤C*z^q∧ volume (f x)≤C*z^q at h1
   have h2:=hS (f x)
   have hv:volume (f x)+1≤(C+1)*z^q:=by nlinarith
   have hVp:=Nat.pow_le_pow_left hv r
   rw [mul_pow,← pow_mul] at hVp
   have hq:=Nat.pow_le_pow_right hz (show q≤q+q*r by omega)
   have hr:=Nat.pow_le_pow_right hz (show q*r≤q+q*r by omega)
   have ht1:=h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hVp)
   have ht2:=ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hr)
   have hc:=(Nat.mul_le_mul_left 10 hv).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hq)
   have ho:=h2.2.trans (Nat.mul_le_mul_left D hVp)
   have ho:=ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hr)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     have hcoef:D*(C+1)^r≤C+D*(C+1)^r+10*(C+1):=by omega
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^(q+q*r)) hcoef)
 theorem polynomial_comp_expanded {f:α→ β} {g:β→ γ} {R:Realizer f} {S:Realizer g} {N:β→ ℕ}
     (hR:PolyBound R) (hS:Expanded S N):Expanded (R.comp S) (N ∘ f):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   let e:=q+(q+1)*r+1
   refine ⟨C+D*(C+2)^r+10*(C+1),e,by positivity,?_⟩
   intro x
   let z:=volume x+N (f x)+1
   have hz:1≤z:=by dsimp [z]; omega
   have hN:N (f x)≤z:=by dsimp [z]; omega
   have hp:=Nat.pow_le_pow_left (show volume x+1≤z by dsimp [z]; omega) q
   have h1:=hR x
   have ht:R.time x≤C*z^q:=h1.1.trans (Nat.mul_le_mul_left C hp)
   have hv:volume (f x)≤C*z^q:=h1.2.trans (Nat.mul_le_mul_left C hp)
   have hq:z^q≤z^(q+1):=Nat.pow_le_pow_right hz (by omega)
   have hze:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   have hv':=hv.trans (Nat.mul_le_mul_left C hq)
   have hbase:volume (f x)+N (f x)+1≤(C+2)*z^(q+1):=by nlinarith
   have h2:=hS (f x)
   have hbp:=Nat.pow_le_pow_left hbase r
   rw [mul_pow,← pow_mul] at hbp
   have hqe:z^q≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hre:z^((q+1)*r)≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have ht1:=ht.trans (Nat.mul_le_mul_left C hqe)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hbp)
   have ht2:=ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have ho:=h2.2.trans (Nat.mul_le_mul_left D hbp)
   have ho:=ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have hv1:volume (f x)+1≤(C+1)*z^q:=by have hh:=one_le_pow₀ hz (n:=q); nlinarith
   have hc:=(Nat.mul_le_mul_left 10 hv1).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqe)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+2)^r+10*(C+1))*z^e
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+2)^r+10*(C+1))*z^e
     have hcoef:D*(C+2)^r≤C+D*(C+2)^r+10*(C+1):=by omega
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^e) hcoef)

end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]
 theorem expanded_pair {f:α→ β} {g:α→ γ} {R:Realizer f} {S:Realizer g} {N:α→ ℕ}
     (hR:Expanded R N) (hS:Expanded S N):Expanded (R.pair S) N:=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   refine ⟨21*C+21*D+40,q+r+1,by positivity,?_⟩
   intro x
   let z:=volume x+N x+1
   have hz:1≤z:=by dsimp [z]; omega
   have hq:z^q≤z^(q+r+1):=Nat.pow_le_pow_right hz (by omega)
   have hr:z^r≤z^(q+r+1):=Nat.pow_le_pow_right hz (by omega)
   have hv:volume x+1≤z^(q+r+1):=(show volume x+1≤z by dsimp [z]; omega).trans
     (by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+r+1))
   have h1:=hR x
   have h2:=hS x
   change R.time x≤C*z^q∧ volume (f x)≤C*z^q at h1
   change S.time x≤D*z^r∧ volume (g x)≤D*z^r at h2
   have ht1:=h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hr)
   have ho1:=h1.2.trans (Nat.mul_le_mul_left C hq)
   have ho2:=h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · rw [Realizer.time_pair]
     change _≤(21*C+21*D+40)*z^(q+r+1)
     nlinarith only [ht1,ht2,ho1,ho2,hv]
   · change volume (f x,g x)≤(21*C+21*D+40)*z^(q+r+1)
     rw [volume_pair]
     nlinarith only [ho1,ho2,hv]
end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ:Type} [Coding α] [Coding β] [Coding γ]
 theorem expanded_comp_expanded {f:α→ β} {g:β→ γ} {R:Realizer f} {S:Realizer g}
     {N:α→ ℕ} {M:β→ ℕ} (hR:Expanded R N) (hS:Expanded S M):
     Expanded (R.comp S) (fun x => N x+M (f x)):=by
   obtain ⟨C,q,hC,hR⟩:=hR
   obtain ⟨D,r,hD,hS⟩:=hS
   let e:=q+(q+1)*r+1
   refine ⟨C+D*(C+2)^r+10*(C+1),e,by positivity,?_⟩
   intro x
   let z:=volume x+(N x+M (f x))+1
   have hz:1≤z:=by dsimp [z]; omega
   have hM:M (f x)≤z:=by dsimp [z]; omega
   have hp:=Nat.pow_le_pow_left (show volume x+N x+1≤z by dsimp [z]; omega) q
   have h1:=hR x
   have ht:R.time x≤C*z^q:=h1.1.trans (Nat.mul_le_mul_left C hp)
   have hv:volume (f x)≤C*z^q:=h1.2.trans (Nat.mul_le_mul_left C hp)
   have hq:z^q≤z^(q+1):=Nat.pow_le_pow_right hz (by omega)
   have hze:z≤z^(q+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1)
   have hv':=hv.trans (Nat.mul_le_mul_left C hq)
   have hbase:volume (f x)+M (f x)+1≤(C+2)*z^(q+1):=by nlinarith
   have h2:=hS (f x)
   have hbp:=Nat.pow_le_pow_left hbase r
   rw [mul_pow,← pow_mul] at hbp
   have hqe:z^q≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hre:z^((q+1)*r)≤z^e:=Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have ht1:=ht.trans (Nat.mul_le_mul_left C hqe)
   have ht2:=h2.1.trans (Nat.mul_le_mul_left D hbp)
   have ht2:=ht2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have ho:=h2.2.trans (Nat.mul_le_mul_left D hbp)
   have ho:=ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+2)^r) hre)
   have hv1:volume (f x)+1≤(C+1)*z^q:=by have hh:=one_le_pow₀ hz (n:=q); nlinarith
   have hc:=(Nat.mul_le_mul_left 10 hv1).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqe)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+2)^r+10*(C+1))*z^e
     nlinarith only [ht1,ht2,hc]
   · change volume (g (f x))≤(C+D*(C+2)^r+10*(C+1))*z^e
     exact ho.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^e) (show D*(C+2)^r≤C+D*(C+2)^r+10*(C+1) by omega))
end EdgeSublinearMWIS.Main.RealizerBounds

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem value_expanded:Expanded valueRealizer value:=by
   obtain ⟨C,q,hC,hT⟩:=value_time
   refine ⟨C+3,q+1,by omega,?_⟩
   intro A
   let z:=volume A+value A+1
   have hz:1≤z:=by dsimp [z]; omega
   have hl:=bits_length_volume A
   have hbase:value A+A.length+1≤z:=by dsimp [z]; omega
   have hp:z^q≤z^(q+1):=Nat.pow_le_pow_right hz (by omega)
   have ht:=(hT A).trans ((Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)).trans (Nat.mul_le_mul_left C hp))
   have hv:value A+1≤z^(q+1):=(show value A+1≤z by dsimp [z]; omega).trans
     (by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤q+1))
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (value A)≤(C+3)*z^(q+1)
     rw [volume_nat]
     nlinarith
 def readUnboundedNatural (L:List Bool):ℕ×List Bool:=(value (readWord L).1,(readWord L).2)
 def readUnboundedNaturalRealizer:Realizer readUnboundedNatural:=
   readWordRealizer.comp ((Realizer.fst.comp valueRealizer).pair Realizer.snd)
 theorem readUnboundedNatural_expanded:Expanded readUnboundedNaturalRealizer (fun L => value (readWord L).1):=
   polynomial_comp_expanded readWord_polynomial (expanded_pair
     (polynomial_comp_expanded (linear_polynomial linear_fst) value_expanded)
     (polynomial_expanded (linear_polynomial linear_snd) (fun s:List Bool×List Bool => value s.1)))
 theorem readUnboundedNatural_encoded (n:ℕ) (rest:List Bool):readUnboundedNatural (encodeNat n++rest)=(n,rest):=by
   simp only [readUnboundedNatural,readWord_encoded,value_natBits]
end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β:Type} [Coding α] [Coding β]

 theorem expanded_polynomial_measure {f:α→ β} {R:Realizer f} {N:α→ ℕ}
    (hR:Expanded R N) (A p:ℕ) (hN:∀x,N x≤A*(volume x+1)^p):PolyBound R:=by
  obtain ⟨C,q,hC,hR⟩:=hR
  refine ⟨C*(A+1)^q,(p+1)*q,by positivity,?_⟩
  intro x
  have hz:1≤volume x+1:=by omega
  have hp:(volume x+1)^p≤ (volume x+1)^(p+1):=Nat.pow_le_pow_right hz (by omega)
  have hlinear:volume x+1≤ (volume x+1)^(p+1):=le_self_pow hz (by omega)
  have hbase:volume x+N x+1≤ (A+1)*(volume x+1)^(p+1):=by
    have hn:=(hN x).trans (Nat.mul_le_mul_left A hp)
    nlinarith only [hn,hlinear]
  have hpow:=Nat.pow_le_pow_left hbase q
  rw [mul_pow,← pow_mul] at hpow
  have hclock:=Nat.mul_le_mul_left C hpow
  rw [← mul_assoc] at hclock
  exact ⟨(hR x).1.trans hclock,(hR x).2.trans hclock⟩
end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def naturalProductWords (s:ℕ×ℕ):List Bool:=multiply (natBits s.1) (natBits s.2)
 def naturalProductWordsRealizer:Realizer naturalProductWords:=
   ((Realizer.fst.comp naturalWordRealizer).pair (Realizer.snd.comp naturalWordRealizer)).comp multiplyRealizer
 theorem naturalProductWords_polynomial:PolyBound naturalProductWordsRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) naturalWord_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) naturalWord_polynomial)) multiply_polynomial
 theorem naturalProductWords_value (s:ℕ×ℕ):value (naturalProductWords s)=s.1*s.2:=by
   simp only [naturalProductWords,multiply_value,value_natBits]
 def naturalProductRealizer:Realizer (fun s:ℕ×ℕ => s.1*s.2):=
   (naturalProductWordsRealizer.comp valueRealizer).congr naturalProductWords_value
 theorem naturalProduct_polynomial:PolyBound naturalProductRealizer:=by
   have he:=polynomial_comp_expanded naturalProductWords_polynomial value_expanded
   apply polynomial_congr
   apply expanded_polynomial_measure he 1 2
   rintro ⟨a,b⟩
   simp only [Function.comp_apply,naturalProductWords_value]
   simp only [volume_pair,volume_nat,one_mul]
   nlinarith [Nat.zero_le ((a-b)^2)]

 def naturalPowerRealizer:(d:ℕ)→ Realizer (fun n:ℕ => n^d)
   | 0 => (Realizer.constant 1).congr (fun _ => by simp)
   | d+1 => (((naturalPowerRealizer d).pair Realizer.id).comp naturalProductRealizer).congr
       (fun n => by simp [pow_succ])
 theorem naturalPower_polynomial (d:ℕ):PolyBound (naturalPowerRealizer d):=by
   induction d with
   | zero =>
     dsimp only [naturalPowerRealizer]
     apply polynomial_congr
     exact linear_polynomial (linear_constant 1)
   | succ d ih =>
     dsimp only [naturalPowerRealizer]
     apply polynomial_congr
     exact polynomial_comp (polynomial_pair ih (linear_polynomial linear_id)) naturalProduct_polynomial

 def naturalLogInput (n:ℕ):ℕ:=(n+2).size
 def naturalLogInputRealizer:Realizer naturalLogInput:=
   (((Realizer.succ.comp Realizer.succ).comp naturalWordRealizer).comp listLength).congr
     (fun n => by change (natBits (n+1+1)).length=(n+2).size; rw [natBits_eq_bits,Nat.size_eq_bits_len])
 theorem naturalLogInput_polynomial:PolyBound naturalLogInputRealizer:=
   by
   unfold naturalLogInputRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp (linear_polynomial (linear_comp succ_linear succ_linear))
     naturalWord_polynomial) listLength_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def powerTwoWord (k:ℕ):List Bool:=List.replicate k false++[true]
 def powerTwoWordRealizer:Realizer powerTwoWord:=
   (((Realizer.id.pair (Realizer.constant false)).comp replicateList).pair (Realizer.constant [true])).comp appendBits
 theorem powerTwoWord_polynomial:PolyBound powerTwoWordRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial
     (linear_pair linear_id (linear_constant false))) replicateList_polynomial)
       (linear_polynomial (linear_constant [true]))) appendBits_polynomial
 theorem powerTwoWord_value (k:ℕ):value (powerTwoWord k)=2^k:=by
   induction k with
   | zero => simp [powerTwoWord,value]
   | succ k ih =>
     have he:powerTwoWord (k+1)=false::powerTwoWord k:=by simp only [powerTwoWord,List.replicate_succ,List.cons_append]
     rw [he,value,Bool.toNat_false,zero_add,ih,pow_succ]
     omega

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def paddingExponent (K d:ℕ) (s:ℕ×ℕ):ℕ:=K*(s.2*naturalLogInput s.1)^d
 def paddingExponentRealizer (K d:ℕ):Realizer (paddingExponent K d):=
   ((Realizer.constant K).pair
     (((Realizer.snd.pair (Realizer.fst.comp naturalLogInputRealizer)).comp naturalProductRealizer).comp
       (naturalPowerRealizer d))).comp naturalProductRealizer
 theorem paddingExponent_polynomial (K d:ℕ):PolyBound (paddingExponentRealizer K d):=
   polynomial_comp (polynomial_pair (linear_polynomial (linear_constant K))
     (polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_comp (linear_polynomial linear_fst) naturalLogInput_polynomial)) naturalProduct_polynomial)
       (naturalPower_polynomial d))) naturalProduct_polynomial

 def paddingMagnitude (K d:ℕ) (s:ℕ×ℕ):ℕ:=2^paddingExponent K d s
 def paddingMagnitudeRealizer (K d:ℕ):Realizer (paddingMagnitude K d):=
   (((paddingExponentRealizer K d).comp powerTwoWordRealizer).comp valueRealizer).congr
     (fun _ => powerTwoWord_value _)
 theorem paddingMagnitude_expanded (K d:ℕ):
     Expanded (paddingMagnitudeRealizer K d) (paddingMagnitude K d):=by
   unfold paddingMagnitudeRealizer
   obtain ⟨C,q,hC,hclock⟩:=polynomial_comp_expanded
     (polynomial_comp (paddingExponent_polynomial K d) powerTwoWord_polynomial) value_expanded
   refine ⟨C,q,hC,?_⟩
   intro s
   constructor
   · erw [Realizer.time_congr]
     simpa only [Function.comp_apply,powerTwoWord_value,paddingMagnitude] using (hclock s).1
   · simpa only [Function.comp_apply,powerTwoWord_value,paddingMagnitude] using (hclock s).2

 theorem paddingMagnitude_bounds {K d n E:ℕ} (hK:0<K) (hd:0<d) (hE:0<E):
     n≤paddingMagnitude K d (n,E)∧ E≤paddingMagnitude K d (n,E)∧ 1≤paddingMagnitude K d (n,E):=by
   let L:=naturalLogInput n
   have hL:1≤L:=Nat.size_pos.mpr (by omega:0<n+2)
   have hP:E*L≤ K*(E*L)^d:=
     (le_self_pow (Nat.mul_pos hE hL) hd.ne').trans (Nat.le_mul_of_pos_left _ hK)
   have hEL:E≤ E*L:=Nat.le_mul_of_pos_right _ hL
   have hLE:L≤ E*L:=Nat.le_mul_of_pos_left _ hE
   have hn:n<2^L:=(by omega:n≤n+2).trans_lt (Nat.lt_size_self (n+2))
   have hpL:=Nat.pow_le_pow_right (by decide:1≤2) (hLE.trans hP)
   have hpE:=Nat.lt_two_pow_self.trans_le
     (Nat.pow_le_pow_right (by decide:1≤2) (hEL.trans hP))
   exact ⟨hn.le.trans hpL,hpE.le,Nat.one_le_two_pow⟩

 def paddingZeroBitsRealizer:Realizer (fun T:ℕ => List.replicate (2*T) false):=
   ((((Realizer.id.pair Realizer.id).comp Realizer.add).pair (Realizer.constant false)).comp replicateList).congr
     (fun T => by simp [two_mul])
 theorem paddingZeroBits_polynomial:PolyBound paddingZeroBitsRealizer:=by
   unfold paddingZeroBitsRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair
     (polynomial_comp (linear_polynomial (linear_pair linear_id linear_id)) BinaryGcd.nat_add_polynomial)
     (linear_polynomial (linear_constant false))) replicateList_polynomial
 def paddingBitsRealizer (K d:ℕ):Realizer (fun s:ℕ×ℕ => List.replicate (2*paddingMagnitude K d s) false):=
   (paddingMagnitudeRealizer K d).comp paddingZeroBitsRealizer
 theorem paddingBits_expanded (K d:ℕ):
     Expanded (paddingBitsRealizer K d) (paddingMagnitude K d):=
   expanded_comp (paddingMagnitude_expanded K d) paddingZeroBits_polynomial

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem natCeil_ratio (n d:ℕ) (hd:0<d):⌈(n:ℚ)/(d:ℚ)⌉₊=(n+d-1)/d:=by
   rw [← Nat.ceilDiv_eq_add_pred_div]
   have hdQ:(0:ℚ)<d:=by exact_mod_cast hd
   apply le_antisymm
   · apply Nat.ceil_le.mpr
     rw [div_le_iff₀ hdQ]
     have hh:n≤(n⌈/⌉d)*d:=by
       simpa only [Nat.mul_comm] using (ceilDiv_le_iff_le_mul hd).mp (le_refl (n⌈/⌉d))
     exact_mod_cast hh
   · apply (ceilDiv_le_iff_le_mul hd).mpr
     have hh:=Nat.le_ceil ((n:ℚ)/(d:ℚ))
     rw [div_le_iff₀ hdQ] at hh
     have hhNat:n≤⌈(n:ℚ)/(d:ℚ)⌉₊*d:=by exact_mod_cast hh
     simpa only [Nat.mul_comm] using hhNat
 def ceilFraction (s:FractionWords):List Bool:=
   (divide (sumWords s.1 (BinarySubtract.difference s.2 [true])) s.2).1
 def ceilFractionRealizer:Realizer ceilFraction:=
   ((((Realizer.fst.pair ((Realizer.snd.pair (Realizer.constant [true])).comp BinarySubtract.differenceRealizer)).comp sumWordsRealizer).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 theorem ceilFraction_polynomial:PolyBound ceilFractionRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_pair (linear_polynomial linear_fst) (polynomial_comp
       (linear_polynomial (linear_pair linear_snd (linear_constant _))) BinarySubtract.difference_polynomial)) sumWords_polynomial)
     (linear_polynomial linear_snd)) divide_polynomial) (linear_polynomial linear_fst)
 theorem ceilFraction_value (s:FractionWords) (hs:0<value s.2):value (ceilFraction s)=⌈fractionValue s⌉₊:=by
   rw [ceilFraction,(divide_value _ _ hs).1,sumWords_value,BinarySubtract.difference_value]
   simp only [value,Bool.toNat_true,Nat.mul_zero,Nat.add_zero]
   rw [fractionValue,natCeil_ratio _ _ hs]
   congr 1
   omega
end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem fold_reverse_head {α:Type} (L:List α) (a:α):
     L.reverse.foldl (fun _ b => b) a=L.headD a:=by
   cases L with
   | nil => rfl
   | cons b L => rw [List.reverse_cons,List.foldl_append]; rfl
 def headList {α:Type} [Coding α] (a:α):Realizer (fun L:List α => L.headD a):=
   ((Realizer.reverse.pair (Realizer.constant a)).comp Realizer.fst.fold).congr (fun L => fold_reverse_head L a)
 theorem headList_polynomial {α:Type} [Coding α] (a:α):PolyBound (headList a):=by
   unfold headList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair reverse_polynomial_generic (linear_polynomial (linear_constant a)))
     (polynomial_fold_select (linear_polynomial linear_fst) (fun _ _ => Or.inl rfl))

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def lookupList {α:Type} [Coding α] (a:α):Realizer (fun s:List α×ℕ => (s.1.drop s.2).headD a):=
   dropList.comp (headList a)
 theorem lookupList_polynomial {α:Type} [Coding α] (a:α):PolyBound (lookupList a):=
   polynomial_comp dropList_polynomial (headList_polynomial a)

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Extra where | raw | context | count | consume | temp deriving Fintype,DecidableEq
 inductive CallPhase where | count | context | out | into | emitContext | prefix deriving Fintype,DecidableEq
 abbrev CallK (U:Program):=U.machine.tm.K⊕Extra
 abbrev CallΓ (U:Program):CallK U→ Type:=StackSum U.machine.tm.Γ (fun _:Extra => Bool)
 abbrev CallΛ (U:Program):=U.machine.tm.Λ⊕CallPhase
 abbrev Callσ (U:Program):=U.machine.tm.σ×Option Bool
 def callCarry {U:Program} (v:Callσ U) (a:Option Bool):Callσ U:=(v.1,a)
 def callNext {U:Program} (p:CallPhase):Stmt (CallΓ U) (CallΛ U) (Callσ U):=
   .load (fun v => callCarry v none) (.goto (fun _ => .inr p))
 def callCode (U:Program):CallΛ U→ Stmt (CallΓ U) (CallΛ U) (Callσ U)
   | .inl l => extendStmt .emitContext (U.machine.tm.m l)
   | .inr .count =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.getD false)
         (.push (.inr .count) (fun _ => true) (.push (.inr .consume) (fun _ => true) (callNext .count)))
         (callNext .context))
   | .inr .context =>
     .pop (.inr .consume) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.pop (.inr .raw) (fun v a => callCarry v a)
           (.push (.inr .context) (fun v => v.2.getD false) (callNext .context)))
         (callNext .out))
   | .inr .out =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (callNext .out))
         (callNext .into))
   | .inr .into =>
     .pop (.inr .temp) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₀) (fun v => U.machine.inputAlphabet.symm (v.2.getD false)) (callNext .into))
         (.load (fun _ => (U.machine.tm.initialState,none)) (.goto (fun _ => .inl U.machine.tm.main))))
   | .inr .emitContext =>
     .pop (.inr .context) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun v => U.machine.outputAlphabet.symm (v.2.getD false)) (callNext .emitContext))
         (.push (.inl U.machine.tm.k₁) (fun _ => U.machine.outputAlphabet.symm false) (callNext .prefix)))
   | .inr .prefix =>
     .pop (.inr .count) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun _ => U.machine.outputAlphabet.symm true) (callNext .prefix))
         (.load (fun _ => (U.machine.tm.initialState,none)) .halt))

 def callTM (U:Program):Turing.FinTM2 where
   K:=CallK U
   Γ:=CallΓ U
   Λ:=CallΛ U
   σ:=Callσ U
   k₀:=.inr .raw
   k₁:=.inl U.machine.tm.k₁
   initialState:=(U.machine.tm.initialState,none)
   main:=.inr .count
   m:=callCode U
 def callWithContext (U:Program):Program where
   machine:= ⟨callTM U,(by change Bool ≃ Bool; exact Equiv.refl _),
     (by change U.machine.tm.Γ U.machine.tm.k₁ ≃ Bool; exact U.machine.outputAlphabet)⟩
   finiteAlphabet k:=by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def extraStore (R C N D T:List Bool):Extra→ List Bool
   | .raw => R
   | .context => C
   | .count => N
   | .consume => D
   | .temp => T
 def callCfg (U:Program) (p:CallPhase) (S:∀k,List (U.machine.tm.Γ k)) (R C N D T:List Bool):(callTM U).Cfg:=
   cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (extraStore R C N D T))
 theorem update_extend_right {κ μ:Type} [DecidableEq κ] [DecidableEq μ] {Γ:κ→ Type} {Δ:μ→ Type}
     (S:∀k,List (Γ k)) (E:∀k,List (Δ k)) (e:μ) (L:List (Δ e)):
     Function.update (extendStore S E) (.inr e) L=extendStore S (Function.update E e L):=by
   funext k
   cases k with
   | inl k => simp [Function.update,extendStore]
   | inr j =>
     by_cases h:j=e
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]

 theorem count_step_true (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C N D T:List Bool):
     step (callCode U) (callCfg U .count S (true::R) C N D T)=
       some (callCfg U .count S R C (true::N) (true::D) T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   simp only [update_extend_right,Function.update_of_ne (by decide:Extra.count≠Extra.raw),
     Function.update_of_ne (by decide:Extra.consume≠Extra.raw),Function.update_of_ne (by decide:Extra.consume≠Extra.count)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

 theorem count_step_false (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C N D T:List Bool):
     step (callCode U) (callCfg U .count S (false::R) C N D T)=some (callCfg U .context S R C N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem context_step_cons (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (b d:Bool) (R C N D T:List Bool):
     step (callCode U) (callCfg U .context S (b::R) C N (d::D) T)=
       some (callCfg U .context S R (b::C) N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide:Extra.raw≠Extra.consume),
     Function.update_of_ne (by decide:Extra.context≠Extra.consume),Function.update_of_ne (by decide:Extra.context≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem context_step_nil (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C N T:List Bool):
     step (callCode U) (callCfg U .context S R C N [] T)=some (callCfg U .out S R C N [] T):=by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]
 theorem call_out_cons (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (b:Bool) (R C N D T:List Bool):
     step (callCode U) (callCfg U .out S (b::R) C N D T)=some (callCfg U .out S R C N D (b::T)):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide:Extra.temp≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem call_out_nil (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (C N D T:List Bool):
     step (callCode U) (callCfg U .out S [] C N D T)=some (callCfg U .into S [] C N D T):=by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]

 theorem call_into_cons (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (b:Bool) (R C N D T:List Bool):
     step (callCode U) (callCfg U .into S R C N D (b::T))=some (callCfg U .into
       (Function.update S U.machine.tm.k₀ (U.machine.inputAlphabet.symm b::S U.machine.tm.k₀)) R C N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem call_into_nil (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C N D:List Bool):
     step (callCode U) (callCfg U .into S R C N D [])=
       some (extendCfg .emitContext (none:Option Bool) (extraStore R C N D [])
         (cfg (some U.machine.tm.main) U.machine.tm.initialState S)):=by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update,extendCfg]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem emit_context_cons (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (b:Bool) (R C N D T:List Bool):
     step (callCode U) (callCfg U .emitContext S R (b::C) N D T)=some (callCfg U .emitContext
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm b::S U.machine.tm.k₁)) R C N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem emit_context_nil (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R N D T:List Bool):
     step (callCode U) (callCfg U .emitContext S R [] N D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm false::S U.machine.tm.k₁)) R [] N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem prefix_step_cons (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (b:Bool) (R C N D T:List Bool):
     step (callCode U) (callCfg U .prefix S R C (b::N) D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm true::S U.machine.tm.k₁)) R C N D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true]
   rw [update_extend_right]
   simp only [extendStore_inl]
   rw [update_extend]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 def callHaltCfg (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C D T:List Bool):(callTM U).Cfg:=
   cfg none (U.machine.tm.initialState,none) (extendStore S (extraStore R C [] D T))
 theorem prefix_step_nil (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (R C D T:List Bool):
     step (callCode U) (callCfg U .prefix S R C [] D T)=some (callHaltCfg U S R C D T):=by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false,callHaltCfg]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

 theorem callHalt_only (U:Program) (output:List Bool):
     callHaltCfg U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []=
       Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm):=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (onlyStack U.machine.tm.k₁ _) (extraStore [] [] [] [] [])=(Turing.haltList (callTM U) _).stk
   rw [haltList_store]
   funext k
   cases k with
   | inl k =>
     by_cases h:k=U.machine.tm.k₁
     · subst k; simp [onlyStack,Function.update,extendStore,callTM]
     · simp [onlyStack,Function.update,extendStore,callTM,h]
   | inr e => cases e <;> simp [onlyStack,Function.update,extendStore,callTM,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem count_loop (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (n:ℕ) (rest C N D T:List Bool):
     run (callCode U) (callCfg U .count S (List.replicate n true++false::rest) C N D T) (n+1)=
       some (callCfg U .context S rest C (List.replicate n true++N) (List.replicate n true++D) T):=by
   induction n generalizing N D with
   | zero => exact count_step_false U S rest C N D T
   | succ n ih =>
     simp only [List.replicate_succ,List.cons_append]
     rw [run_first,count_step_true,Option.bind_some]
     have hh:=ih (true::N) (true::D)
     have hn:∀L:List Bool,List.replicate n true++true::L=true::(List.replicate n true++L):=by
       intro L
       calc
         _=(List.replicate n true++[true])++L:=by simp
         _=List.replicate (n+1) true++L:=by rw [List.replicate_succ']
         _=_:=rfl
     simpa only [hn] using hh
 theorem context_loop (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (L rest C N T:List Bool):
     run (callCode U) (callCfg U .context S (L++rest) C N (List.replicate L.length true) T) (L.length+1)=
       some (callCfg U .out S rest (L.reverse++C) N [] T):=by
   induction L generalizing C with
   | nil => exact context_step_nil U S rest C N T
   | cons b L ih =>
     simp only [List.length_cons,List.replicate_succ,List.cons_append]
     rw [run_first,context_step_cons,Option.bind_some]
     have hh:=ih (b::C)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem call_out_loop (U:Program) (S:∀k,List (U.machine.tm.Γ k)) (L C N D T:List Bool):
     run (callCode U) (callCfg U .out S L C N D T) (L.length+1)=
       some (callCfg U .into S [] C N D (L.reverse++T)):=by
   induction L generalizing T with
   | nil => exact call_out_nil U S C N D T
   | cons b L ih =>
     rw [List.length_cons,run_first,call_out_cons,Option.bind_some]
     have hh:=ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem inputCfg_only (U:Program) (input:List Bool):
     cfg (some U.machine.tm.main) U.machine.tm.initialState
       (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm))=
       Turing.initList U.machine.tm (input.map U.machine.inputAlphabet.symm):=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   exact (initList_store _ _).symm
 theorem call_into_loop (U:Program) (L acc R C N D:List Bool):
     run (callCode U) (callCfg U .into (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D L) (L.length+1)=
       some (extendCfg .emitContext (none:Option Bool) (extraStore R C N D [])
         (Turing.initList U.machine.tm ((L.reverse++acc).map U.machine.inputAlphabet.symm))):=by
   induction L generalizing acc with
   | nil =>
     have hh:=call_into_nil U (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D
     rw [inputCfg_only] at hh
     exact hh
   | cons b L ih =>
     rw [List.length_cons,run_first,call_into_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh:=ih (b::acc)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem emit_context_loop (U:Program) (C output R N D T:List Bool):
     run (callCode U) (callCfg U .emitContext
       (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R C N D T) (C.length+1)=
       some (callCfg U .prefix (onlyStack U.machine.tm.k₁
         ((false::(C.reverse++output)).map U.machine.outputAlphabet.symm)) R [] N D T):=by
   induction C generalizing output with
   | nil =>
     have hh:=emit_context_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R N D T
     rw [onlyStack_self,onlyStack_update] at hh
     exact hh
   | cons b C ih =>
     rw [List.length_cons,run_first,emit_context_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh:=ih (b::output)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem prefix_loop (U:Program) (n:ℕ) (output:List Bool):
     run (callCode U) (callCfg U .prefix (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
       [] [] (List.replicate n true) [] []) (n+1)=
       some (Turing.haltList (callTM U) ((List.replicate n true++output).map U.machine.outputAlphabet.symm)):=by
   induction n generalizing output with
   | zero =>
     have hh:=prefix_step_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []
     rw [callHalt_only] at hh
     exact hh
   | succ n ih =>
     rw [List.replicate_succ,run_first,prefix_step_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh:=ih (true::output)
     have he:List.replicate n true++true::output=List.replicate (n+1) true++output:=by
       rw [List.replicate_succ',List.append_assoc,List.singleton_append]
     simpa only [List.map_cons,he,List.replicate_succ,List.cons_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem call_start (U:Program) (ctx input:List Bool):
     Turing.initList (callTM U) (prefixBits ctx++input)=
       callCfg U .count (fun _ => []) (List.replicate ctx.length true++false::(ctx++input)) [] [] [] []:=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore,extraStore,prefixBits,List.append_assoc]
 theorem call_after_halt (U:Program) (ctx output:List Bool):
     extendCfg .emitContext (none:Option Bool) (extraStore [] ctx.reverse (List.replicate ctx.length true) [] [])
       (Turing.haltList U.machine.tm (output.map U.machine.outputAlphabet.symm))=
         callCfg U .emitContext (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
           [] ctx.reverse (List.replicate ctx.length true) [] []:=by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList U.machine.tm _).stk _=extendStore (onlyStack U.machine.tm.k₁ _) _
   rw [haltList_store]

 theorem call_context_runs (U:Program) (ctx input output:List Bool) (T:ℕ) (hU:Runs U input output T):
     Runs (callWithContext U) (prefixBits ctx++input) (prefixBits ctx++output)
       (T+4*ctx.length+2*input.length+6):=by
   change Nonempty (Turing.TM2OutputsInTime (callTM U) ((prefixBits ctx++input).map id)
     (some ((prefixBits ctx++output).map U.machine.outputAlphabet.symm)) (T+4*ctx.length+2*input.length+6))
   rw [List.map_id]
   obtain ⟨t,ht,hu⟩:=outputs_run U input output T hU
   let S:∀k,List (U.machine.tm.Γ k):=fun _ => []
   let N:=List.replicate ctx.length true
   have h1:=count_loop U S ctx.length (ctx++input) [] [] [] []
   simp only [List.append_nil] at h1
   rw [← call_start] at h1
   have h2:=context_loop U S ctx input [] N []
   simp only [List.append_nil] at h2
   have h3:=call_out_loop U S input ctx.reverse N [] []
   simp only [List.append_nil] at h3
   have h4:=call_into_loop U input.reverse [] [] ctx.reverse N []
   simp only [List.map_nil,onlyStack_nil,List.reverse_reverse,List.append_nil,List.length_reverse] at h4
   have h5:=run_extend .emitContext U.machine.tm.m (callCode U) (fun _ => rfl) _ _ (none:Option Bool)
     (extraStore [] ctx.reverse N [] []) t hu
   rw [call_after_halt] at h5
   have h6:=emit_context_loop U ctx.reverse output [] N [] []
   simp only [List.reverse_reverse,List.length_reverse] at h6
   have h7:=prefix_loop U ctx.length (false::(ctx++output))
   have hr:=run_trans _ _ _ _ _ _ h1 h2
   have hr:=run_trans _ _ _ _ _ _ hr h3
   have hr:=run_trans _ _ _ _ _ _ hr h4
   have hr:=run_trans _ _ _ _ _ _ hr h5
   have hr:=run_trans _ _ _ _ _ _ hr h6
   have hr:=run_trans _ _ _ _ _ _ hr h7
   have he:List.replicate ctx.length true++false::(ctx++output)=prefixBits ctx++output:=by
     simp only [prefixBits,List.append_assoc,List.cons_append]
   rw [he] at hr
   obtain ⟨hrun⟩:=RawStack.outputs (tm:=callTM U) (prefixBits ctx++input)
     ((prefixBits ctx++output).map U.machine.outputAlphabet.symm) _ hr
   refine ⟨{hrun with steps_le_m:=hrun.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nativeDefaultRational:SignedWords:=(false,([],[true]))

 def rawAccuracy (s:ℕ×List Bool):SignedWords:=
   ((readMany (s.1+1) s.2).1.drop s.1).headD nativeDefaultRational
 def rawAccuracyRealizer:Realizer rawAccuracy:=
   (((((Realizer.fst.comp Realizer.succ).pair Realizer.snd).comp readManyRealizer).comp Realizer.fst).pair
     Realizer.fst).comp (lookupList nativeDefaultRational)
 theorem rawAccuracy_polynomial:PolyBound rawAccuracyRealizer:=
   polynomial_comp (polynomial_pair (polynomial_comp (polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) (linear_polynomial succ_linear))
       (linear_polynomial linear_snd)) readMany_polynomial) (linear_polynomial linear_fst))
     (linear_polynomial linear_fst)) (lookupList_polynomial nativeDefaultRational)

 def inverseCeilingWords (s:SignedWords):List Bool:=ceilFraction (s.2.2,s.2.1)
 def inverseCeilingWordsRealizer:Realizer inverseCeilingWords:=
   ((Realizer.snd.comp Realizer.snd).pair (Realizer.snd.comp Realizer.fst)).comp ceilFractionRealizer
 theorem inverseCeilingWords_polynomial:PolyBound inverseCeilingWordsRealizer:=
   polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_snd linear_snd)
     (linear_comp linear_snd linear_fst))) ceilFraction_polynomial

 def paddingMetadata (L:List Bool):List Bool:=
   let s:=graphStart L
   encodeNat s.1++prefixBits (inverseCeilingWords (rawAccuracy (s.1,s.2.2)))
 abbrev MetadataFields:=ℕ×(List Bool×List Bool)
 def metadataAccuracyEnvironment:Realizer (fun s:MetadataFields => (s.1,s.2.2)):=
   Realizer.fst.pair (Realizer.snd.comp Realizer.snd)
 def metadataCeilingCode:Realizer (fun s:MetadataFields =>
     prefixBits (inverseCeilingWords (rawAccuracy (s.1,s.2.2)))):=
   (((metadataAccuracyEnvironment.comp rawAccuracyRealizer).comp inverseCeilingWordsRealizer).comp prefixRealizer).congr (fun _ => rfl)
 def metadataFieldsRealizer:Realizer (fun s:MetadataFields =>
     encodeNat s.1++prefixBits (inverseCeilingWords (rawAccuracy (s.1,s.2.2)))):=
   (((Realizer.fst.comp naturalCodeRealizer).pair metadataCeilingCode).comp appendBits).congr (fun _ => rfl)
 def paddingMetadataRealizer:Realizer paddingMetadata:=
   (graphStartRealizer.comp metadataFieldsRealizer).congr (fun _ => rfl)
 theorem paddingMetadata_polynomial:PolyBound paddingMetadataRealizer:=by
   unfold paddingMetadataRealizer
   apply polynomial_congr
   apply polynomial_comp graphStart_polynomial
   unfold metadataFieldsRealizer
   apply polynomial_congr
   apply polynomial_comp _ appendBits_polynomial
   apply polynomial_pair
   · exact polynomial_comp (linear_polynomial linear_fst) naturalCode_polynomial
   · unfold metadataCeilingCode
     apply polynomial_congr
     exact polynomial_comp (polynomial_comp (polynomial_comp
       (linear_polynomial (linear_pair linear_fst (linear_comp linear_snd linear_snd))) rawAccuracy_polynomial)
       inverseCeilingWords_polynomial) prefix_polynomial

 theorem rawAccuracy_code {n:ℕ} (w:Fin n→ RationalCode) (ε:RationalCode):
     rawAccuracy (n,rationalData w ε)=codeWords ε:=by
   let qs:=List.ofFn w++[ε]
   have hl:qs.length=n+1:=by simp [qs]
   have he:rationalData w ε=qs.flatMap RationalCode.bits:=by
     simp [qs,rationalData,List.flatMap_def,List.map_ofFn,Function.comp_def]
   simp only [rawAccuracy,← hl,he]
   rw [show qs.flatMap RationalCode.bits=qs.flatMap RationalCode.bits++[] by simp,readMany_codes]
   simp [qs,List.map_ofFn]

 theorem nativeCeiling_canonical (s:FractionWords):trim (ceilFraction s)=ceilFraction s:=by
   unfold ceilFraction divide
   exact trim_idem _
 theorem nativeCeiling_natBits (s:FractionWords) (hs:0<value s.2):
     ceilFraction s=natBits ⌈fractionValue s⌉₊:=by
   exact (canonical_eq_natBits _ (nativeCeiling_canonical s)).trans
     (congrArg natBits (ceilFraction_value s hs))

 theorem inverseCeilingWords_code (ε:RationalCode) (hε:0<ε.value):
     inverseCeilingWords (codeWords ε)=natBits ⌈ε.value⁻¹⌉₊:=by
   have hd:(0:ℚ)<ε.denominator:=by exact_mod_cast ε.positive
   have hn:(0:ℚ)<ε.numerator:=(div_pos_iff_of_pos_right hd).mp hε
   have hni:0<ε.numerator:=by exact_mod_cast hn
   have hna:(ε.numerator.natAbs:ℚ)=(ε.numerator:ℚ):=by
     calc
       _=((ε.numerator.natAbs:ℤ):ℚ):=(Int.cast_natCast _).symm
       _=_:=congrArg (fun z:ℤ => (z:ℚ)) (Int.natAbs_of_nonneg hni.le)
   have hnv:0<value (codeWords ε).2.1:=by
     simp only [codeWords,value_natBits]
     exact Int.natAbs_pos.mpr hni.ne'
   have hh:=ceilFraction_value ((codeWords ε).2.2,(codeWords ε).2.1) hnv
   have hv:fractionValue ((codeWords ε).2.2,(codeWords ε).2.1)=ε.value⁻¹:=by
     simp [fractionValue,codeWords,value_natBits,RationalCode.value,hna]
   exact (nativeCeiling_natBits ((codeWords ε).2.2,(codeWords ε).2.1) hnv).trans
     (congrArg (fun x:ℚ => natBits ⌈x⌉₊) hv)

 theorem paddingMetadata_code {n:ℕ} (G:SimpleGraph (Fin n))
     (w:Fin n→ RationalCode) (ε:RationalCode) (hε:0<ε.value):
     paddingMetadata (weightedInput G w ε)=encodeNat n++encodeNat ⌈ε.value⁻¹⌉₊:=by
   simp only [paddingMetadata,graphStart_weighted,rawAccuracy_code,inverseCeilingWords_code ε hε,prefix_natBits]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β:Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def parsePaddingMetadata (L:List Bool):ℕ×ℕ:=
   let s:=readUnboundedNatural L
   (s.1,(readUnboundedNatural s.2).1)
 def parsePaddingTail:Realizer (fun s:ℕ×List Bool => (s.1,(readUnboundedNatural s.2).1)):=
   Realizer.fst.pair ((Realizer.snd.comp readUnboundedNaturalRealizer).comp Realizer.fst)
 def parsePaddingMetadataRealizer:Realizer parsePaddingMetadata:=
   readUnboundedNaturalRealizer.comp parsePaddingTail
 theorem parsePaddingTail_expanded:Expanded parsePaddingTail (fun s => value (readWord s.2).1):=by
   exact expanded_pair (polynomial_expanded (linear_polynomial linear_fst) _)
     (expanded_comp (polynomial_comp_expanded (linear_polynomial linear_snd) readUnboundedNatural_expanded)
       (linear_polynomial linear_fst))
 theorem parsePaddingMetadata_expanded:
     Expanded parsePaddingMetadataRealizer (fun L => (parsePaddingMetadata L).1+(parsePaddingMetadata L).2):=by
   have hh:=expanded_comp_expanded readUnboundedNatural_expanded parsePaddingTail_expanded
   exact hh
 theorem parsePaddingMetadata_code (n E:ℕ):
     parsePaddingMetadata (encodeNat n++encodeNat E)=(n,E):=by
   rw [parsePaddingMetadata,readUnboundedNatural_encoded]
   rw [show encodeNat E=encodeNat E++[] by simp,readUnboundedNatural_encoded]

 def classPaddingBits (K d:ℕ) (L:List Bool):List Bool:=
   List.replicate (2*paddingMagnitude K d (parsePaddingMetadata L)) false
 def classPaddingRealizer (K d:ℕ):Realizer (classPaddingBits K d):=
   parsePaddingMetadataRealizer.comp (paddingBitsRealizer K d)
 theorem classPadding_expanded (K d:ℕ):
     Expanded (classPaddingRealizer K d) (fun L => (parsePaddingMetadata L).1+
       (parsePaddingMetadata L).2+paddingMagnitude K d (parsePaddingMetadata L)):=by
   exact expanded_comp_expanded parsePaddingMetadata_expanded (paddingBits_expanded K d)

 theorem class_padding_program (K d:ℕ) (hK:0<K) (hd:0<d):
     ∃ (U:Program) (A r:ℕ),0<A∧ 0<r∧ ∀ n E:ℕ,0<E→
       Runs U (encodeNat n++encodeNat E)
         (List.replicate (2*paddingMagnitude K d (n,E)) false)
         (A*(paddingMagnitude K d (n,E))^r):=by
   obtain ⟨U,B,hB,hU⟩:=realizer_native_program _ (classPaddingRealizer K d)
   obtain ⟨C,q,hC,hclock⟩:=classPadding_expanded K d
   refine ⟨U,B*(C*40^q+9),q+1,by positivity,by omega,?_⟩
   intro n E hE
   let T:=paddingMagnitude K d (n,E)
   let input:=encodeNat n++encodeNat E
   have hbounds:=paddingMagnitude_bounds (n:=n) hK hd hE
   have hn:n≤T:=hbounds.1
   have hEt:E≤T:=hbounds.2.1
   have hT:1≤T:=hbounds.2.2
   have hlen:input.length≤6*T:=by
     have h1:=EncodingBounds.encodeNat_length n
     have h2:=EncodingBounds.encodeNat_length E
     dsimp [input]
     simp only [List.length_append]
     omega
   have hvol:=BinaryAdder.volume_bits input
   have hparse:parsePaddingMetadata input=(n,E):=parsePaddingMetadata_code n E
   have hc:=hclock input
   dsimp only at hc
   rw [hparse] at hc
   change (classPaddingRealizer K d).time input≤C*(volume input+(n+E+T)+1)^q∧ _ at hc
   have hbase:volume input+(n+E+T)+1≤40*T:=by omega
   have ht:=hc.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
   rw [mul_pow] at ht
   have hq:T^q≤T^(q+1):=Nat.pow_le_pow_right hT (by omega)
   have htl:T≤T^(q+1):=le_self_pow hT (by omega)
   have ht':(classPaddingRealizer K d).time input≤ (C*40^q)*T^(q+1):=
     ht.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (C*40^q) hq)
   have hother:input.length+2*T+1≤ 9*T^(q+1):=by omega
   have htime:(classPaddingRealizer K d).time input+input.length+2*T+1≤
       (C*40^q+9)*T^(q+1):=by nlinarith only [ht',hother]
   have hr:=hU input
   have hout:classPaddingBits K d input=List.replicate (2*T) false:=by
     simp only [classPaddingBits,hparse,T]
   rw [hout] at hr
   apply NativeCompiler.runs_mono U _ _ hr
   simp only [List.length_replicate]
   simpa only [T,mul_assoc] using Nat.mul_le_mul_left B htime

end EdgeSublinearMWIS.Main.RawStack

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nativePaddingPre (L:List Bool):List Bool:=prefixBits L++paddingMetadata L
 def nativePaddingPreRealizer:Realizer nativePaddingPre:=
   (prefixRealizer.pair paddingMetadataRealizer).comp appendBits
 theorem nativePaddingPre_polynomial:PolyBound nativePaddingPreRealizer:=
   polynomial_comp (polynomial_pair prefix_polynomial paddingMetadata_polynomial) appendBits_polynomial
 theorem nativePaddingPre_code {n:ℕ} (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode)
    (ε:RationalCode) (hε:0<ε.value):
    nativePaddingPre (weightedInput G w ε)=prefixBits (weightedInput G w ε)++
      (encodeNat n++encodeNat ⌈ε.value⁻¹⌉₊):=by
   rw [nativePaddingPre,paddingMetadata_code G w ε hε]

 def nativePaddingPenalty (Q q:ℕ) (L:List Bool):List Bool:=
   List.replicate (2*(Q*(L.length+1)^q)) false
 def nativePaddingPenaltyRealizer (Q q:ℕ):Realizer (nativePaddingPenalty Q q):=
   (((Realizer.constant Q).pair ((listLength.comp Realizer.succ).comp (naturalPowerRealizer q))).comp
     naturalProductRealizer).comp paddingZeroBitsRealizer
 theorem nativePaddingPenalty_polynomial (Q q:ℕ):PolyBound (nativePaddingPenaltyRealizer Q q):=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial (linear_constant Q))
     (polynomial_comp (polynomial_comp listLength_polynomial (linear_polynomial succ_linear))
       (naturalPower_polynomial q))) naturalProduct_polynomial) paddingZeroBits_polynomial

 def nativePaddingPostFields (Q q:ℕ) (s:List Bool×List Bool):List Bool:=
   nativeInput s.1++s.2++s.2++nativePaddingPenalty Q q s.1
 def nativePaddingPostFieldsRealizer (Q q:ℕ):Realizer (nativePaddingPostFields Q q):=
   ((((((Realizer.fst.comp nativeInputRealizer).pair Realizer.snd).comp appendBits).pair Realizer.snd).comp
     appendBits).pair (Realizer.fst.comp (nativePaddingPenaltyRealizer Q q))).comp appendBits
 theorem nativePaddingPostFields_polynomial (Q q:ℕ):PolyBound (nativePaddingPostFieldsRealizer Q q):=
   polynomial_comp (polynomial_pair (polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) nativeInput_polynomial)
       (linear_polynomial linear_snd)) appendBits_polynomial) (linear_polynomial linear_snd)) appendBits_polynomial)
     (polynomial_comp (linear_polynomial linear_fst) (nativePaddingPenalty_polynomial Q q))) appendBits_polynomial
 def nativePaddingPost (Q q:ℕ) (L:List Bool):List Bool:=nativePaddingPostFields Q q (readWord L)
 def nativePaddingPostRealizer (Q q:ℕ):Realizer (nativePaddingPost Q q):=
   readWordRealizer.comp (nativePaddingPostFieldsRealizer Q q)
 theorem nativePaddingPost_polynomial (Q q:ℕ):PolyBound (nativePaddingPostRealizer Q q):=
   polynomial_comp readWord_polynomial (nativePaddingPostFields_polynomial Q q)
 theorem nativePaddingPost_code (Q q:ℕ) (L:List Bool) (T:ℕ):
     nativePaddingPost Q q (prefixBits L++List.replicate (2*T) false)=
       nativeInput L++List.replicate (2*(2*T+Q*(L.length+1)^q)) false:=by
   simp only [nativePaddingPost,readWord_prefix,nativePaddingPostFields,nativePaddingPenalty]
   rw [List.append_assoc,List.append_assoc,← List.replicate_add,← List.replicate_add]
   congr 2
   ring
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RamBridge
open TernaryAdapter Lax759944.BinaryWordEncoding
 theorem wordBits_append (xs ys:List ℕ):wordBits (xs++ys)=wordBits xs++wordBits ys:=by
   simp [wordBits,encode,binarySymbols]
 theorem wordBits_zeroPadding (T:ℕ):wordBits (List.replicate T 0)=List.replicate (2*T) false:=by
   induction T with
   | zero => rfl
   | succ T ih =>
     rw [List.replicate_succ,show 0::List.replicate T 0=[0]++List.replicate T 0 from rfl,wordBits_append,ih]
     change [false,false]++List.replicate (2*T) false=List.replicate (2*(T+1)) false
     rw [show 2*(T+1)=2+2*T by omega,List.replicate_add]
     rfl
end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open Lax263307Proofs NativeQptasImplementation NativeQptasPositive
open Lax263307.IndependentSetEncoding Lax759944.BinaryWordEncoding RawStack

 theorem naturalLogInput_eq (n:ℕ):naturalLogInput n=NativeFinalBounds.inputLog n:=by
   change (n+2).size=(n+2).log2+1
   apply Nat.le_antisymm
   · exact Nat.size_le.mpr Nat.lt_log2_self
   · have h:=Nat.lt_size.mpr (Nat.log2_self_le (by omega:n+2≠0))
     omega

 theorem uniform_padding_threshold:∃ Q q:ℕ,0<Q∧ 0<q∧
    ∀ {C:Lax263307.GraphClasses.GraphClass} (i:Fixed C),∃ A d:ℕ,0<A∧ 0<d∧
      ∀ (n:ℕ) (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
        (w:Fin n→ RationalCode) (ε:RationalCode),0<ε.value→
        let T:=paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊)
        let padding:=2*T+Q*((weightedInput G w ε).length+1)^q
        bitSize (encodeInput G (fun v => (w v).value) ε.value)+1≤padding∧
        NativeQptasWordBounds.width i (fun v => (w v).value) ε.value+
          Lax455465Proofs.RamTransfer.layoutAllowance
            (Lax455465Proofs.RamAutomaticLayout.layout (paddedCommand (NativeWeightedExecution.command i)))≤padding∧
        NativeWeightedExecution.cost i (fun v => (w v).value) ε.value≤padding:=by
   obtain ⟨q₀,Q₀,hq₀,hQ₀,hsource⟩:=universal_rational_overhead
   obtain ⟨B,p,hB,hp,hinput⟩:=canonical_input_polynomial
   let q:=p*q₀+p+1
   let Q:=Q₀*(B+1)^q₀+B+1
   refine ⟨Q,q,by dsimp [Q]; positivity,by dsimp [q]; omega,?_⟩
   intro C i
   obtain ⟨K,hK⟩:=hsource i
   let e:=i.envelopeExponent+1
   let layout:=Lax455465Proofs.RamTransfer.layoutAllowance
     (Lax455465Proofs.RamAutomaticLayout.layout (paddedCommand (NativeWeightedExecution.command i)))
   let A:=K*864^e+layout+1
   refine ⟨A,3*e,by dsimp [A]; positivity,by dsimp [e]; omega,?_⟩
   intro n G inst w ε hε
   let weights:=fun v => (w v).value
   let E:= ⌈ε.value⁻¹⌉₊
   let X:=E*naturalLogInput n
   let T:=paddingMagnitude A (3*e) (n,E)
   let z:=(weightedInput G w ε).length+1
   let penalty:=Q*z^q
   have hz:1≤z:=by dsimp [z]; omega
   have hE:0<E:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
   have hL:0<naturalLogInput n:=Nat.size_pos.mpr (by omega:0<n+2)
   have hX:1≤X:=Nat.mul_pos hE hL
   have hpoly:=hinput n G w ε
   change bitSize (encodeInput G weights ε.value)+1≤B*z^p at hpoly
   have hparams:=canonicalParameters_le_input G weights ε.value
   have hpenalty:Q₀*(rationalBitSize weights ε.value+1)^q₀+
       (bitSize (encodeInput G weights ε.value)+1)≤penalty:=by
     have hparam:rationalBitSize weights ε.value+1≤B*z^p:=by omega
     have ht:=Nat.mul_le_mul_left Q₀ (Nat.pow_le_pow_left hparam q₀)
     rw [mul_pow,← pow_mul] at ht
     have hexp:p*q₀≤q:=by dsimp [q]; omega
     have hbig:=Nat.mul_le_mul_left (Q₀*B^q₀) (Nat.pow_le_pow_right hz hexp)
     have hcoef:Q₀*B^q₀≤Q₀*(B+1)^q₀:=Nat.mul_le_mul_left Q₀ (Nat.pow_le_pow_left (by omega) _)
     have hfirst:Q₀*(rationalBitSize weights ε.value+1)^q₀≤(Q₀*(B+1)^q₀)*z^q:=by
       exact ht.trans (by simpa only [mul_assoc] using hbig.trans (Nat.mul_le_mul_right _ hcoef))
     have hsecond:bitSize (encodeInput G weights ε.value)+1≤B*z^q:=
       hpoly.trans (Nat.mul_le_mul_left B (Nat.pow_le_pow_right hz (by dsimp [q]; omega)))
     change _≤ (Q₀*(B+1)^q₀+B+1)*z^q
     nlinarith only [hfirst,hsecond]
   have hcore:=hK n weights ε.value hε
   have hcopy:=NativeQptasComplexity.copy_bound weights ε.value hε
   have henv:=NativeFinalBounds.weighted_envelope K e n (order weights ε.value) ε.value hε hcopy
   have hA:K*864^e≤A:=by dsimp [A]; omega
   have hquasi:NativeRootResource.envelope K e (order weights ε.value)
       (denominator (order weights ε.value) ε.value)≤T:=by
     apply henv.trans
     change 2^((K*864^e)*(E*NativeFinalBounds.inputLog n)^(3*e))≤ 2^(A*X^(3*e))
     rw [← naturalLogInput_eq]
     exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hA)
   have hstatic:layout≤T:=by
     have ha:layout≤A:=by dsimp [A]; omega
     have he:A≤A*X^(3*e):=Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hX)
     exact ha.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) he))
   change bitSize (encodeInput G weights ε.value)+1≤2*T+penalty∧
     NativeQptasWordBounds.width i weights ε.value+layout≤2*T+penalty∧
     NativeWeightedExecution.cost i weights ε.value≤2*T+penalty
   change NativeQptasWordBounds.width i weights ε.value+NativeQptasRuntime.allowance i+
     10*NativeWeightedExecution.cost i weights ε.value+1≤
       NativeRootResource.envelope K e (order weights ε.value) (denominator (order weights ε.value) ε.value)+
         Q₀*(rationalBitSize weights ε.value+1)^q₀ at hcore
   omega

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem pipeline_time_bound (A C K₁ K₂ B D p r:ℕ) (hA:0<A) (hC:0<C) (hK₁:0<K₁) (hK₂:0<K₂) (hp:0<p):
     ∃ K:ℕ,0<K∧ ∀ (L N T payload middle tcall tab post:ℕ),
       payload≤L+B*(A*(L+N+1)^p)→ tcall≤T+6*payload+7→
       tab=K₁*(A*(L+N+1)^p+tcall+L+1)→ middle≤L+D*tab→
       post=C*(middle+1)^r→
       K₂*(tab+post+L+1)≤K*(T+L+N+1)^(p+p*r+1):=by
   let F:=K₁*(A*(1+6*B)+15)
   refine ⟨K₂*(F+C*(2+D*F)^r+2),by dsimp [F]; positivity,?_⟩
   intro L N T payload middle tcall tab post hpay hcall hab hmid hpost
   let z:=T+L+N+1
   have hz:1≤z:=by dsimp [z]; omega
   have hpre:(L+N+1)^p≤z^p:=Nat.pow_le_pow_left (by dsimp [z]; omega) p
   have hzp:z≤z^p:=by simpa only [pow_one] using Nat.pow_le_pow_right hz hp
   have hin:T+7*L+8≤15*z:=by dsimp [z]; omega
   have hpay':payload≤L+B*(A*z^p):=hpay.trans (Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.mul_le_mul_left A hpre)) L)
   have habound:tab≤F*z^p:=by
     rw [hab]
     have hinner:A*(L+N+1)^p+tcall+L+1≤(A*(1+6*B)+15)*z^p:=by
       have hh:=Nat.mul_le_mul_left A hpre
       nlinarith only [hh,hcall,hpay',hin,hzp]
     exact (Nat.mul_le_mul_left K₁ hinner).trans_eq (by dsimp [F]; ring)
   have hL:L+1≤z^p:=(show L+1≤z by dsimp [z]; omega).trans hzp
   have hinput:middle+1≤(2+D*F)*z^p:=by
     have hmul:=Nat.mul_le_mul_left D habound
     have hone:1≤z^p:=one_le_pow₀ hz
     nlinarith only [hmid,hmul,hL,hone]
   have hpostbound:post≤C*(2+D*F)^r*z^(p*r):=by
     rw [hpost]
     have hh:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput r)
     simpa only [mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hp1:z^p≤z^(p+p*r+1):=Nat.pow_le_pow_right hz (by omega)
   have hr1:z^(p*r)≤z^(p+p*r+1):=Nat.pow_le_pow_right hz (by omega)
   have h1:z≤z^(p+p*r+1):=by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega:1≤p+p*r+1)
   have htab:=habound.trans (Nat.mul_le_mul_left F hp1)
   have hpost':=hpostbound.trans (Nat.mul_le_mul_left (C*(2+D*F)^r) hr1)
   have hL':L+1≤z^(p+p*r+1):=(show L+1≤z by dsimp [z]; omega).trans h1
   have hs:tab+post+L+1≤(F+C*(2+D*F)^r+2)*z^(p+p*r+1):=by
     nlinarith only [htab,hpost',hL']
   change _≤(K₂*(F+C*(2+D*F)^r+2))*z^(p+p*r+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K₂ hs

end EdgeSublinearMWIS.Main.RawStack

end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.ProgramComposition
open RawStack OAI.ThreeMachine.StackCompiler RealizerBounds

 theorem uniform_context_pipeline {f g:List Bool→ List Bool} (R:Realizer f) (S:Realizer g)
     (hR:PolyBound R) (hS:PolyBound S):
     ∃ q:ℕ,0<q∧ ∀ U:Program,∃ (P:Program) (K:ℕ),0<K∧
       ∀ (input ctx middle output:List Bool) (T:ℕ),f input=prefixBits ctx++middle→ Runs U middle output T→
         ∃ s,Runs P input (g (prefixBits ctx++output)) s∧ s≤K*(T+input.length+1)^q:=by
   obtain ⟨Pre,A,p,hA,hp,hPre⟩:=TreeToTM2.realizer_poly_program R hR
   obtain ⟨Post,C,r,hC,hr,hPost⟩:=TreeToTM2.realizer_poly_program S hS
   refine ⟨p+p*r+1,by omega,?_⟩
   intro U
   let AB:=sequence Pre (callWithContext U)
   let P:=sequence AB Post
   obtain ⟨K₁,hK₁,hSeq₁⟩:=sequence_runs_linear Pre (callWithContext U)
   obtain ⟨K₂,hK₂,hSeq₂⟩:=sequence_runs_linear AB Post
   let B:=StackSpace.bound Pre.machine.tm
   obtain ⟨K,hK,hBound⟩:=pipeline_time_bound A C K₁ K₂ B (StackSpace.bound AB.machine.tm) p r hA hC hK₁ hK₂ hp
   refine ⟨P,K,hK,?_⟩
   intro input ctx middle output T hf hU
   let ret:=prefixBits ctx++output
   let preTime:=A*(input.length+1)^p
   let callTime:=T+4*ctx.length+2*middle.length+6
   let abTime:=K₁*(preTime+callTime+input.length+1)
   let postTime:=C*(ret.length+1)^r
   have hpre:=hPre input
   have hcall:=call_context_runs U ctx middle output T hU
   rw [← hf] at hcall
   have hab:Runs AB input ret abTime:=hSeq₁ input (f input) ret preTime callTime hpre hcall
   have hpost:=hPost ret
   have hfinal:=hSeq₂ input ret (g ret) abTime postTime hab hpost
   refine ⟨K₂*(abTime+postTime+input.length+1),hfinal,?_⟩
   have hcallBound:callTime≤ T+6*(f input).length+7:=by
     rw [hf]
     simp only [List.length_append,prefixBits,List.length_replicate,List.length_cons]
     dsimp only [callTime]
     omega
   have hb:=hBound input.length 0 T (f input).length ret.length callTime abTime postTime
     (by simpa only [Nat.add_zero] using output_length Pre input (f input) preTime hpre) hcallBound
     (by simp only [Nat.add_zero]; rfl) (output_length AB input ret abTime hab) rfl
   simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Nat.add_zero] using hb
end EdgeSublinearMWIS.Main.ProgramComposition

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
open EdgeSublinearMWIS.Main.TernaryAdapter

 def dropTwoBitsRealizer:Realizer (fun L:List Bool => L.drop 2):=
   ((tailList (α:=Bool)).comp tailList).congr (fun L => by
     cases L with
     | nil => rfl
     | cons a L => cases L <;> rfl)
 theorem dropTwoBits_polynomial:PolyBound dropTwoBitsRealizer:=by
   unfold dropTwoBitsRealizer
   apply polynomial_congr
   exact linear_polynomial (linear_comp tailList_linear tailList_linear)
 def dropFourBitsRealizer:Realizer (fun L:List Bool => L.drop 4):=
   (dropTwoBitsRealizer.comp dropTwoBitsRealizer).congr (fun L => by simp only [Function.comp_apply,List.drop_drop])
 theorem dropFourBits_polynomial:PolyBound dropFourBitsRealizer:=by
   unfold dropFourBitsRealizer
   apply polynomial_congr
   exact polynomial_comp dropTwoBits_polynomial dropTwoBits_polynomial

 abbrev NativeMaskState:=List Bool×List Bool
 def nativeMaskTrue:Realizer (fun s:NativeMaskState => (s.1.drop 4,true::s.2)):=
   (Realizer.fst.comp dropFourBitsRealizer).pair
     (((Realizer.constant true).pair Realizer.snd).comp Realizer.cons)
 def nativeMaskFalse:Realizer (fun s:NativeMaskState => (s.1.drop 2,false::s.2)):=
   (Realizer.fst.comp dropTwoBitsRealizer).pair
     (((Realizer.constant false).pair Realizer.snd).comp Realizer.cons)
 theorem nativeMaskTrue_polynomial:PolyBound nativeMaskTrue:=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) dropFourBits_polynomial)
     (linear_polynomial (linear_comp (linear_pair (linear_constant true) linear_snd) linear_cons))
 theorem nativeMaskFalse_polynomial:PolyBound nativeMaskFalse:=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) dropTwoBits_polynomial)
     (linear_polynomial (linear_comp (linear_pair (linear_constant false) linear_snd) linear_cons))
 def nativeMaskActive (s:NativeMaskState):NativeMaskState:=
   if (s.1.drop 2).headD false then (s.1.drop 4,true::s.2) else (s.1.drop 2,false::s.2)
 def nativeMaskActiveRealizer:Realizer nativeMaskActive:=
   ((((Realizer.fst.comp dropTwoBitsRealizer).comp BinaryAdder.headBit).pair Realizer.id).comp
     (nativeMaskTrue.choose nativeMaskFalse)).congr (fun _ => rfl)
 theorem nativeMaskActive_polynomial:PolyBound nativeMaskActiveRealizer:=by
   unfold nativeMaskActiveRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp
     (polynomial_comp (linear_polynomial linear_fst) dropTwoBits_polynomial)
     (linear_polynomial BinaryAdder.headBit_linear)) (linear_polynomial linear_id))
     (polynomial_choose nativeMaskTrue_polynomial nativeMaskFalse_polynomial)
 def nativeMaskStep (s:NativeMaskState):NativeMaskState:=if !s.1.isEmpty then nativeMaskActive s else s
 def nativeMaskStepRealizer:Realizer nativeMaskStep:=
   (((Realizer.fst.comp nonemptyBits).pair Realizer.id).comp (nativeMaskActiveRealizer.choose Realizer.id)).congr
     (fun _ => rfl)
 theorem nativeMaskStep_polynomial:PolyBound nativeMaskStepRealizer:=by
   unfold nativeMaskStepRealizer
   apply polynomial_congr
   exact polynomial_comp (linear_polynomial (linear_pair (linear_comp linear_fst nonempty_linear) linear_id))
     (polynomial_choose nativeMaskActive_polynomial (linear_polynomial linear_id))
 theorem nativeMaskStep_volume (s:NativeMaskState):volume (nativeMaskStep s)≤ volume s+4:=by
   rcases s with ⟨L,R⟩
   have h2:=volume_drop_le L 2
   have h4:=volume_drop_le L 4
   have ht:=volume_bool true
   have hf:=volume_bool false
   simp only [nativeMaskStep,nativeMaskActive]
   split_ifs <;> simp only [volume_pair,volume_cons] <;> omega
 def nativeMaskDecode (L:List Bool):List Bool:=(nativeMaskStep^[L.length] (L,[])).2.reverse
 def nativeMaskDecodeRealizer:Realizer nativeMaskDecode:=
   (((listLength.pair (Realizer.id.pair (Realizer.constant ([]:List Bool)))).comp nativeMaskStepRealizer.iterate).comp
     (Realizer.snd.comp Realizer.reverse))
 theorem nativeMaskDecode_polynomial:PolyBound nativeMaskDecodeRealizer:=
   polynomial_comp (polynomial_comp (polynomial_pair listLength_polynomial
     (linear_polynomial (linear_pair linear_id (linear_constant ([]:List Bool)))))
       (polynomial_iterate nativeMaskStep_polynomial 4 nativeMaskStep_volume))
     (polynomial_comp (linear_polynomial linear_snd) reverse_polynomial)

 def nativeMaskEncoding (bs:List Bool):List Bool:=bs.flatMap nativeBooleanWord

 theorem nativeMaskStep_true (bs acc:List Bool):
     nativeMaskStep (nativeMaskEncoding (true::bs),acc)=(nativeMaskEncoding bs,true::acc):=rfl
 theorem nativeMaskStep_false (bs acc:List Bool):
     nativeMaskStep (nativeMaskEncoding (false::bs),acc)=(nativeMaskEncoding bs,false::acc):=by
   cases bs with
   | nil => rfl
   | cons b bs => cases b <;> rfl
 theorem nativeMaskSteps (bs acc:List Bool) (m:ℕ) (hm:bs.length≤ m):
     nativeMaskStep^[m] (nativeMaskEncoding bs,acc)=([],bs.reverse++acc):=by
   induction bs generalizing m acc with
   | nil =>
     induction m with
     | zero => rfl
     | succ m ih => rw [Function.iterate_succ_apply]; exact ih (by simp)
   | cons b bs ih =>
     cases m with
     | zero => simp at hm
     | succ m =>
       rw [Function.iterate_succ_apply]
       cases b
       · rw [nativeMaskStep_false,ih (false::acc) m (by simpa using hm)]
         simp
       · rw [nativeMaskStep_true,ih (true::acc) m (by simpa using hm)]
         simp
 theorem nativeMaskEncoding_length (bs:List Bool):bs.length≤(nativeMaskEncoding bs).length:=by
   induction bs with
   | nil => rfl
   | cons b bs ih => cases b <;> simp [nativeMaskEncoding,nativeBooleanWord,List.flatMap_cons] at * <;> omega
 theorem nativeMaskDecode_encoding (bs:List Bool):nativeMaskDecode (nativeMaskEncoding bs)=bs:=by
   rw [nativeMaskDecode,nativeMaskSteps bs [] _ (nativeMaskEncoding_length bs)]
   simp
 theorem nativeMaskWordEncoding (bs:List Bool):
     RamBridge.wordBits (bs.map (fun b => if b then 1 else 0))=nativeMaskEncoding bs:=by
   calc
     _=bs.flatMap (fun b => binarySymbols (Lax759944.BinaryWordEncoding.encodeNat (if b then 1 else 0))):=by
       simp only [RamBridge.wordBits,Lax759944.BinaryWordEncoding.encode,List.flatMap_map,
         binarySymbols,List.flatMap_assoc]
     _=bs.flatMap nativeBooleanWord:=by
       apply congrArg (fun f => bs.flatMap f)
       funext b
       exact (nativeBoolean_code b).symm
 theorem nativeMaskOutput_code {n:ℕ} (I:Finset (Fin n)):
     RamBridge.wordBits (Lax263307.IndependentSetEncoding.encodeOutput I)=nativeMaskEncoding (mask I):=by
   have he:Lax263307.IndependentSetEncoding.encodeOutput I=(mask I).map (fun b => if b then 1 else 0):=by
     simp [Lax263307.IndependentSetEncoding.encodeOutput,mask,List.map_ofFn]
     funext v
     simp [Function.comp_def]
   rw [he]
   exact nativeMaskWordEncoding _
 theorem nativeMaskDecode_output {n:ℕ} (I:Finset (Fin n)):
     nativeMaskDecode (RamBridge.wordBits (Lax263307.IndependentSetEncoding.encodeOutput I))=mask I:=by
   rw [nativeMaskOutput_code,nativeMaskDecode_encoding]

end EdgeSublinearMWIS.Main.RawStack

end
end

section

namespace EdgeSublinearMWIS.Main.RuntimeEnvelope

 theorem pow_add_bound (x y q:ℕ):(x+y)^q≤2^q*(x^q+y^q):=by
   by_cases h:x≤ y
   · calc
       _≤ (2*y)^q:=Nat.pow_le_pow_left (by omega) q
       _=2^q*y^q:=mul_pow _ _ _
       _≤ _:=Nat.mul_le_mul_left _ (by omega)
   · calc
       _≤ (2*x)^q:=Nat.pow_le_pow_left (by omega) q
       _=2^q*x^q:=mul_pow _ _ _
       _≤ _:=Nat.mul_le_mul_left _ (by omega)

 theorem two_monomial_power (C D T z a b q:ℕ):
     (C*T^a+D*z^b)^q≤2^q*(C^q+D^q)*(T^(a*q)+z^(b*q)):=by
   have hh:=pow_add_bound (C*T^a) (D*z^b) q
   rw [mul_pow,mul_pow,← pow_mul,← pow_mul] at hh
   have hm:C^q*T^(a*q)+D^q*z^(b*q)≤(C^q+D^q)*(T^(a*q)+z^(b*q)):=by nlinarith only [Nat.zero_le (C^q*z^(b*q)),Nat.zero_le (D^q*T^(a*q))]
   exact hh.trans ((Nat.mul_le_mul_left _ hm).trans_eq (by ring))

 theorem two_monomial_clock {C D T z a b q r p:ℕ} (hT:1≤ T) (hz:1≤ z)
     (hr:a*q≤ r) (hp:b*q≤ p):
     (C*T^a+D*z^b)^q≤(2^q*(C^q+D^q))*(T^r+z^p):=by
   exact (two_monomial_power C D T z a b q).trans
     (Nat.mul_le_mul_left _ (Nat.add_le_add (Nat.pow_le_pow_right hT hr) (Nat.pow_le_pow_right hz hp)))

 theorem sequence_clock {a b c K₁ K₂ T₁ T₂ T₃ z H:ℕ}
     (h₁:T₁≤ a*H) (h₂:T₂≤ b*H) (h₃:T₃≤ c*H) (hz:z≤ H):
     K₂*(K₁*(T₁+T₂+z)+T₃+z)≤(K₂*(K₁*(a+b+1)+c+1))*H:=by
   have hsum:T₁+T₂+z≤(a+b+1)*H:=by nlinarith
   have hs:=Nat.mul_le_mul_left K₁ hsum
   have hsum₂:K₁*(T₁+T₂+z)+T₃+z≤(K₁*(a+b+1)+c+1)*H:=by nlinarith only [hs,h₃,hz]
   exact (Nat.mul_le_mul_left K₂ hsum₂).trans_eq (by ring)

end EdgeSublinearMWIS.Main.RuntimeEnvelope

end

section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open RawStack RealizerBounds ProgramComposition RuntimeEnvelope
open OAI.ThreeMachine.StackCompiler
open Lax263307Proofs NativeQptasImplementation
open Lax263307.IndependentSetEncoding Lax759944.BinaryWordEncoding

 theorem nativeMaskEncoding_length_upper (bs:List Bool):(nativeMaskEncoding bs).length≤4*bs.length:=by
   induction bs with
   | nil => rfl
   | cons b bs ih => cases b <;> simp [nativeMaskEncoding,nativeBooleanWord,List.flatMap_cons] at * <;> omega

 theorem weighted_bit_program_mixed_bound:∃ q:ℕ,0< q∧
    ∀ C:GraphClass,StronglyEdgeSublinear C→
      ∃ (P:Program) (A d r K:ℕ),0< A∧ 0< d∧ 0< r∧ 0< K∧
        ∀ (n:ℕ) (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode) (ε:RationalCode),
          C n G→ 0<ε.value→ ε.value<1→
          ∃ I:Finset (Fin n),G.IsIndepSet (I:Set (Fin n))∧
            (1-(ε.value:ℝ))*weightedAlpha G (fun v => (w v).value)≤∑ v∈I,((w v).value:ℝ)∧
            Runs P (weightedInput G w ε) (mask I)
              (K*((paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊))^r+((weightedInput G w ε).length+1)^q)):=by
   obtain ⟨qSim,hqSim,hSolver⟩:=native_weighted_binary_program
   obtain ⟨Q,qPad,hQ,hqPad,hThreshold⟩:=uniform_padding_threshold
   obtain ⟨qCtx,hqCtx,hContext⟩:=uniform_context_pipeline nativePaddingPreRealizer
     (nativePaddingPostRealizer Q qPad) nativePaddingPre_polynomial (nativePaddingPost_polynomial Q qPad)
   obtain ⟨Dec,Cdec,pdec,hCdec,hpdec,hDec⟩:=TreeToTM2.realizer_poly_program nativeMaskDecodeRealizer nativeMaskDecode_polynomial
   let q:=max qCtx (max (qPad*qSim) pdec)+1
   refine ⟨q,by dsimp [q]; omega,?_⟩
   intro C hC
   obtain ⟨i,Sol,Ksol,hKsol,hSol⟩:=hSolver C hC
   obtain ⟨A,d,hA,hd,hThreshold⟩:=hThreshold i
   obtain ⟨U,At,rClass,hAt,hrClass,hU⟩:=class_padding_program A d hA hd
   obtain ⟨Pad,Kctx,hKctx,hPad⟩:=hContext U
   let Stage₁:=sequence Pad Sol
   let P:=sequence Stage₁ Dec
   obtain ⟨K₁,hK₁,hSeq₁⟩:=sequence_runs_linear Pad Sol
   obtain ⟨K₂,hK₂,hSeq₂⟩:=sequence_runs_linear Stage₁ Dec
   let r:=max (rClass*qCtx) qSim+1
   let a:=Kctx*(2^qCtx*(At^qCtx+1))
   let b:=(Ksol*3^qSim)*(2^qSim*(2^qSim+Q^qSim))
   let c:=Cdec*5^pdec
   let K:=K₂*(K₁*(a+b+1)+c+1)
   refine ⟨P,A,d,r,K,hA,hd,by dsimp [r]; omega,by dsimp [K]; positivity,?_⟩
   intro n G w ε hG hε hε1
   let input:=weightedInput G w ε
   let weights:=fun v => (w v).value
   let xs:=encodeInput G weights ε.value
   let T:=paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊)
   let z:=input.length+1
   let W:=2*T+Q*z^qPad
   let H:=T^r+z^q
   have hz:1≤ z:=by dsimp [z]; omega
   have hE:0<⌈ε.value⁻¹⌉₊:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
   have hT:1≤ T:=(paddingMagnitude_bounds (n:=n) hA hd hE).2.2
   have hthreshold:=hThreshold n G w ε hε
   change bitSize xs+1≤ W∧ _∧ NativeWeightedExecution.cost i weights ε.value≤ W at hthreshold
   have hjob:=hU n ⌈ε.value⁻¹⌉₊ hE
   obtain ⟨tPad,hPadRun,hPadTime⟩:=hPad input input (encodeNat n++encodeNat ⌈ε.value⁻¹⌉₊)
     (List.replicate (2*T) false) (At*T^rClass) (nativePaddingPre_code G w ε hε) hjob
   have hPadOutput:nativePaddingPost Q qPad (prefixBits input++List.replicate (2*T) false)=
       wordBits (xs++List.replicate W 0):=by
     rw [nativePaddingPost_code]
     change nativeInput input++List.replicate (2*W) false=wordBits (xs++List.replicate W 0)
     have hx:nativeInput input=wordBits xs:=nativeInput_code G w ε
     rw [hx,wordBits_append,wordBits_zeroPadding]
   rw [hPadOutput] at hPadRun
   obtain ⟨I,hInd,hApprox,hSolRun⟩:=hSol n G weights ε.value hG hε hε1 W hthreshold.2.1
   let tSol:=Ksol*(bitSize xs+W+NativeWeightedExecution.cost i weights ε.value+1)^qSim
   change Runs Sol (wordBits (xs++List.replicate W 0)) (wordBits (encodeOutput I)) tSol at hSolRun
   let out:=wordBits (encodeOutput I)
   let tDec:=Cdec*(out.length+1)^pdec
   have hDecRun:=hDec out
   rw [nativeMaskDecode_output] at hDecRun
   change Runs Dec out (mask I) tDec at hDecRun
   have hPadClock:tPad≤ a*H:=by
     have hh:=two_monomial_clock (C:=At) (D:=1) (T:=T) (z:=z) (a:=rClass) (b:=1)
       (q:=qCtx) (r:=r) (p:=q) hT hz (by dsimp [r]; omega) (by dsimp [q]; omega)
     simp only [one_pow,one_mul,pow_one] at hh
     have ht:tPad≤ Kctx*(At*T^rClass+z)^qCtx:=by simpa only [z,Nat.add_assoc] using hPadTime
     exact (ht.trans (Nat.mul_le_mul_left Kctx hh)).trans_eq (by dsimp [a,H]; ring)
   have hSolClock:tSol≤ b*H:=by
     have hbase:bitSize xs+W+NativeWeightedExecution.cost i weights ε.value+1≤3*W:=by omega
     have ht:=Nat.mul_le_mul_left Ksol (Nat.pow_le_pow_left hbase qSim)
     rw [mul_pow] at ht
     have hh:=two_monomial_clock (C:=2) (D:=Q) (T:=T) (z:=z) (a:=1) (b:=qPad)
       (q:=qSim) (r:=r) (p:=q) hT hz (by dsimp [r]; omega) (by dsimp [q]; omega)
     simp only [pow_one,one_mul] at hh
     exact (ht.trans (by simpa only [mul_assoc] using Nat.mul_le_mul_left (Ksol*3^qSim) hh)).trans_eq
       (by dsimp [b,H]; ring)
   have hn:n≤ input.length:=by
     have h:=EncodingBounds.order_le_data w ε
     simp only [input,weightedInput,List.length_append]
     omega
   have hout:out.length≤4*n:=by
     have h:=nativeMaskEncoding_length_upper (mask I)
     rw [← nativeMaskOutput_code] at h
     simpa only [mask,List.length_ofFn] using h
   have hDecClock:tDec≤ c*H:=by
     have hbase:out.length+1≤5*z:=by omega
     have ht:=Nat.mul_le_mul_left Cdec (Nat.pow_le_pow_left hbase pdec)
     rw [mul_pow] at ht
     have hp:z^pdec≤ z^q:=Nat.pow_le_pow_right hz (by dsimp [q]; omega)
     have hs:z^q≤ H:=by dsimp [H]; omega
     exact ht.trans (by dsimp [c]; simpa only [mul_assoc] using Nat.mul_le_mul_left (Cdec*5^pdec) (hp.trans hs))
   have hzq:z≤z^q:=le_self_pow hz (by dsimp [q]; omega)
   have hzH:z≤ H:=hzq.trans (by dsimp [H]; omega)
   have hStage₁:=hSeq₁ input (wordBits (xs++List.replicate W 0)) out tPad tSol hPadRun hSolRun
   have hFinal:=hSeq₂ input out (mask I) (K₁*(tPad+tSol+input.length+1)) tDec hStage₁ hDecRun
   refine ⟨I,hInd,hApprox,?_⟩
   apply NativeCompiler.runs_mono P _ _ hFinal
   simpa only [K,H,z,Nat.add_assoc] using sequence_clock (K₁:=K₁) (K₂:=K₂) hPadClock hSolClock hDecClock hzH

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open RawStack RuntimeEnvelope

 theorem weighted_bit_machine_mixed_bound:∃ q:ℕ,0<q∧
    ∀ C:GraphClass,StronglyEdgeSublinear C→
      ∃ (M:CatalyticMatching.General.Machine) (A d r K:ℕ),0<A∧ 0<d∧ 0<r∧ 0<K∧
        ∀ (n:ℕ) (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode) (ε:RationalCode),
          C n G→ 0<ε.value→ ε.value<1→
          ∃ (I:Finset (Fin n)) (s:ℕ),BitHalts M (weightedInput G w ε) (mask I) s∧
            G.IsIndepSet (I:Set (Fin n))∧
            (1-(ε.value:ℝ))*weightedAlpha G (fun v => (w v).value)≤∑ v∈I,((w v).value:ℝ)∧
            s≤K*((paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊))^r+((weightedInput G w ε).length+1)^q):=by
   obtain ⟨q,hq,hProg⟩:=weighted_bit_program_mixed_bound
   obtain ⟨u,hu,hSim⟩:=stack_simulation
   refine ⟨q*u,Nat.mul_pos hq hu,?_⟩
   intro C hC
   obtain ⟨P,A,d,r,K,hA,hd,hr,hK,hP⟩:=hProg C hC
   obtain ⟨M,J,hJ,hM⟩:=hSim P
   refine ⟨M,A,d,r*u,J*(K+1)^u*2^u,hA,hd,Nat.mul_pos hr hu,by positivity,?_⟩
   intro n G w ε hG hε hε1
   obtain ⟨I,hInd,hApprox,hRun⟩:=hP n G w ε hG hε hε1
   let T:=paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊)
   let z:=(weightedInput G w ε).length+1
   let H:=T^r+z^q
   obtain ⟨s,hHalt,hs⟩:=hM (weightedInput G w ε) (mask I) (K*H) hRun
   have hz:1≤z:=by dsimp [z]; omega
   have hzq:z≤z^q:=le_self_pow hz hq.ne'
   have hzH:z≤H:=hzq.trans (by dsimp [H]; omega)
   have hbase:K*H+(weightedInput G w ε).length+1≤(K+1)*H:=by
     calc
       _=K*H+z:=by dsimp [z]; omega
       _≤ K*H+H:=Nat.add_le_add_left hzH _
       _=_:=by ring
   have hp:=Nat.mul_le_mul_left J (Nat.pow_le_pow_left hbase u)
   rw [mul_pow] at hp
   have hsum:=Nat.mul_le_mul_left (J*(K+1)^u) (pow_add_bound (T^r) (z^q) u)
   rw [← pow_mul,← pow_mul] at hsum
   refine ⟨I,s,hHalt,hInd,hApprox,?_⟩
   exact (hs.trans hp).trans (by simpa only [H,T,z,mul_assoc] using hsum)

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace EdgeSublinearMWIS.Main.RamBridge
open RawStack

 theorem logTwo_max_ge_one (n:ℕ):1≤logTwo (max 2 (n:ℝ)):=by
   have h2:0<Real.log 2:=Real.log_pos (by norm_num)
   have hlog:=Real.log_le_log (by norm_num:(0:ℝ)<2) (le_max_left 2 (n:ℝ))
   exact (le_div_iff₀ h2).mpr (by simpa only [one_mul] using hlog)

 theorem naturalLogInput_real_bound (n:ℕ):
     (naturalLogInput n:ℝ)≤3*logTwo (max 2 (n:ℝ)):=by
   let L:=naturalLogInput n
   let M:ℝ:=max 2 (n:ℝ)
   have hL:0<L:=Nat.size_pos.mpr (by omega:0<n+2)
   have hp:2^(L-1)≤n+2:=by
     apply Nat.lt_size.mp
     change L-1<L
     omega
   have hM:2≤M:=le_max_left _ _
   have hn:(n:ℝ)≤M:=le_max_right _ _
   have hn2:(n:ℝ)+2≤M^2:=by nlinarith [sq_nonneg (M-2)]
   have hpow:(2:ℝ)^(L-1)≤M^2:=by
     have hc:(2:ℝ)^(L-1)≤(n:ℝ)+2:=by exact_mod_cast hp
     exact hc.trans hn2
   have hlog:=Real.log_le_log (by positivity:0<(2:ℝ)^(L-1)) hpow
   rw [Real.log_pow,Real.log_pow,Nat.cast_sub (by omega:1≤L),Nat.cast_one] at hlog
   norm_num only [Nat.cast_ofNat] at hlog
   have hlogM:=Real.log_le_log (by norm_num:(0:ℝ)<2) hM
   have h2:0<Real.log 2:=Real.log_pos (by norm_num)
   change (L:ℝ)≤3*(Real.log M/Real.log 2)
   rw [← mul_div_assoc]
   apply (le_div_iff₀ h2).mpr
   nlinarith

 theorem ceil_inverse_real_bound (ε:ℚ) (hε:0<ε) (hε1:ε<1):
     (⌈ε⁻¹⌉₊:ℝ)≤2*(ε:ℝ)⁻¹:=by
   have hc:=Nat.ceil_lt_add_one (inv_nonneg.mpr hε.le)
   have hi:(1:ℚ)<ε⁻¹:=(one_lt_inv₀ hε).mpr hε1
   have hc':(⌈ε⁻¹⌉₊:ℝ)<(ε:ℝ)⁻¹+1:=by exact_mod_cast hc
   have hi':(1:ℝ)<(ε:ℝ)⁻¹:=by exact_mod_cast hi
   linarith

 theorem paddingMagnitude_exp_bound (A d r n:ℕ) (ε:ℚ) (hε:0<ε) (hε1:ε<1):
     ((paddingMagnitude A d (n,⌈ε⁻¹⌉₊))^r:ℝ)≤
       Real.exp ((A:ℝ)*r*Real.log 2*6^d*((ε:ℝ)⁻¹*logTwo (max 2 (n:ℝ)))^d):=by
   let E:= ⌈ε⁻¹⌉₊
   let L:=naturalLogInput n
   let Z:=(ε:ℝ)⁻¹*logTwo (max 2 (n:ℝ))
   have hE:=ceil_inverse_real_bound ε hε hε1
   have hL:=naturalLogInput_real_bound n
   have hlog:0≤logTwo (max 2 (n:ℝ)):=(by norm_num:(0:ℝ)≤1).trans (logTwo_max_ge_one n)
   have hinv:0≤(ε:ℝ)⁻¹:=inv_nonneg.mpr (by exact_mod_cast hε.le)
   have hX:(E:ℝ)*(L:ℝ)≤6*Z:=by
     have hh:=mul_le_mul hE hL (by positivity:(0:ℝ)≤(L:ℝ)) (by positivity:(0:ℝ)≤2*(ε:ℝ)⁻¹)
     dsimp [E,L,Z] at *
     nlinarith only [hh]
   have hpow:=pow_le_pow_left₀ (by positivity:(0:ℝ)≤(E:ℝ)*(L:ℝ)) hX d
   have h2:0≤Real.log 2:=(Real.log_pos (by norm_num:(1:ℝ)<2)).le
   have hco:0≤(A:ℝ)*r*Real.log 2:=by positivity
   have hexp:(A:ℝ)*((E:ℝ)*(L:ℝ))^d*r*Real.log 2≤
       (A:ℝ)*r*Real.log 2*6^d*Z^d:=by
     calc
       _=((A:ℝ)*r*Real.log 2)*((E:ℝ)*(L:ℝ))^d:=by ring
       _≤ ((A:ℝ)*r*Real.log 2)*(6*Z)^d:=mul_le_mul_of_nonneg_left hpow hco
       _=_:=by rw [mul_pow]; ring
   have heq2 (k:ℕ):(2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2):=by
     rw [Real.exp_nat_mul,Real.exp_log (by norm_num:(0:ℝ)<2)]
   have heq:((paddingMagnitude A d (n,E))^r:ℝ)=
       Real.exp ((A:ℝ)*((E:ℝ)*(L:ℝ))^d*r*Real.log 2):=by
     unfold paddingMagnitude paddingExponent
     push_cast
     rw [← pow_mul,heq2]
     congr 1
     push_cast
     dsimp [L]
   rw [heq]
   exact Real.exp_le_exp.mpr hexp

end EdgeSublinearMWIS.Main.RamBridge

end
end

section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace EdgeSublinearMWIS.Main
theorem theorem_2_local:
    ∃ q:ℕ,0 < q∧ ∀ C:GraphClass,StronglyEdgeSublinear C→
      ∃ (M:CatalyticMatching.General.Machine) (K:ℝ) (d:ℕ),0 < K∧ 0 < d∧
        ∀ (n:ℕ) (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode)
          (ε:RationalCode),C n G→ 0 < ε.value→ ε.value < 1→
          ∃ (I:Finset (Fin n)) (s:ℕ),
            BitHalts M (weightedInput G w ε) (mask I) s∧
            G.IsIndepSet (I:Set (Fin n))∧
            (1 - (ε.value:ℝ)) * weightedAlpha G (fun v => (w v).value)≤
              ∑ v∈ I, ((w v).value:ℝ)∧
            (s:ℝ)≤ K * Real.exp
              (K * (((ε.value:ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1:ℝ) ^ q:=by
  obtain ⟨q,hq,hMachine⟩:=RamBridge.weighted_bit_machine_mixed_bound
  refine ⟨2*q,by omega,?_⟩
  intro C hC
  obtain ⟨M,A,d,r,N,hA,hd,hr,hN,hM⟩:=hMachine C hC
  let coef:ℝ:=(A:ℝ)*r*Real.log 2*6^d
  let K:ℝ:=(N:ℝ)*3^q+coef+1
  have hcoef:0≤coef:=by dsimp [coef]; positivity
  have hNreal:(0:ℝ)<N:=by exact_mod_cast hN
  have hK:0<K:=by dsimp [K]; positivity
  have hpoly:(N:ℝ)*3^q≤K:=by dsimp [K]; linarith
  have hexpcoef:coef≤K:=by
    have hn3:(0:ℝ)≤(N:ℝ)*3^q:=by positivity
    dsimp [K]
    linarith
  have hthree:(1:ℝ)≤3^q:=one_le_pow₀ (by norm_num)
  have hNK:(N:ℝ)≤K:=by
    have hh:=mul_le_mul_of_nonneg_left hthree hNreal.le
    simp only [mul_one] at hh
    exact hh.trans hpoly
  refine ⟨M,K,d,hK,hd,?_⟩
  intro n G w ε hG hε hε1
  obtain ⟨I,s,hHalt,hInd,hApprox,hs⟩:=hM n G w ε hG hε hε1
  refine ⟨I,s,hHalt,hInd,hApprox,?_⟩
  let T:=RawStack.paddingMagnitude A d (n,⌈ε.value⁻¹⌉₊)
  let Z:=(ε.value:ℝ)⁻¹*logTwo (max 2 (n:ℝ))
  let L:ℝ:=(rationalData w ε).length+1
  have hZ:0≤Z:=mul_nonneg (inv_nonneg.mpr (by exact_mod_cast hε.le))
    ((by norm_num:(0:ℝ)≤1).trans (RamBridge.logTwo_max_ge_one n))
  have hTp:((T^r:ℕ):ℝ)≤Real.exp (coef*Z^d):=
    by simpa only [T,Nat.cast_pow,coef,Z] using RamBridge.paddingMagnitude_exp_bound A d r n ε.value hε hε1
  have hLength:=EncodingBounds.input_length G w ε
  have hLengthPow:=Nat.pow_le_pow_left hLength q
  rw [mul_pow,← pow_mul] at hLengthPow
  have hLengthReal:(((weightedInput G w ε).length+1:ℕ):ℝ)^q≤3^q*L^(2*q):=by
    dsimp only [L]
    exact_mod_cast hLengthPow
  have hsReal:(s:ℝ)≤(N:ℝ)*(((T^r:ℕ):ℝ)+(((weightedInput G w ε).length+1:ℕ):ℝ)^q):=by
    exact_mod_cast hs
  have hExp:Real.exp (coef*Z^d)≤Real.exp (K*Z^d):=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexpcoef (pow_nonneg hZ _))
  have hExpMul:(N:ℝ)*Real.exp (coef*Z^d)≤K*Real.exp (K*Z^d):=
    (mul_le_mul_of_nonneg_left hExp hNreal.le).trans
      (mul_le_mul_of_nonneg_right hNK (Real.exp_pos _).le)
  change (s:ℝ)≤K*Real.exp (K*Z^d)+K*L^(2*q)
  calc
    _≤ (N:ℝ)*(((T^r:ℕ):ℝ)+(((weightedInput G w ε).length+1:ℕ):ℝ)^q):=hsReal
    _≤ (N:ℝ)*(Real.exp (coef*Z^d)+3^q*L^(2*q)):=
      mul_le_mul_of_nonneg_left (add_le_add hTp hLengthReal) hNreal.le
    _=(N:ℝ)*Real.exp (coef*Z^d)+((N:ℝ)*3^q)*L^(2*q):=by ring
    _≤ K*Real.exp (K*Z^d)+K*L^(2*q):=
      add_le_add hExpMul (mul_le_mul_of_nonneg_right hpoly (by dsimp [L]; positivity))

end EdgeSublinearMWIS.Main

open EdgeSublinearMWIS.Main
theorem solution:
    ∃ q:ℕ,0 < q∧ ∀ C:GraphClass,StronglyEdgeSublinear C→
      ∃ (M:CatalyticMatching.General.Machine) (K:ℝ) (d:ℕ),0 < K∧ 0 < d∧
        ∀ (n:ℕ) (G:SimpleGraph (Fin n)) (w:Fin n→ RationalCode)
          (ε:RationalCode),C n G→ 0 < ε.value→ ε.value < 1→
          ∃ (I:Finset (Fin n)) (s:ℕ),
            BitHalts M (weightedInput G w ε) (mask I) s∧
            G.IsIndepSet (I:Set (Fin n))∧
            (1 - (ε.value:ℝ)) * weightedAlpha G (fun v => (w v).value)≤
              ∑ v∈ I, ((w v).value:ℝ)∧
            (s:ℝ)≤ K * Real.exp
              (K * (((ε.value:ℝ))⁻¹ * logTwo (max 2 n)) ^ d) +
                K * ((rationalData w ε).length + 1:ℝ) ^ q:=by
  exact theorem_2_local

end
end
