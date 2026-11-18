-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.bounded_native_iteration
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:43:20.638197+00:00
-- url     : https://prove2.me/submissions/35c37ac8-5807-4664-9f49-af710659b0ab

import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

-- Solutions.RawStackTrace
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kDecidableEq
open Turing.TM2
variable {κ Λ σ : Type} [DecidableEq κ] {Γ : κ → Type}

 def cfg (l : Option Λ) (v : σ) (S : ∀i,List (Γ i)) : Cfg Γ Λ σ := ⟨l,v,S⟩
 def run (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : ℕ → Option (Cfg Γ Λ σ)
   | 0 => some c
   | t+1 => (run code c t).bind (step code)

 theorem run_iter (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c t=(fun o : Option (Cfg Γ Λ σ) => o.bind (step code))^[t] (some c) := by
  induction t with
  | zero => rfl
  | succ t ih => rw [run,ih,Function.iterate_succ_apply']

 theorem run_add (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (s t : ℕ) :
    run code c (s+t)=(run code c s).bind (fun d => run code d t) := by
  induction t with
  | zero => simp only [Nat.add_zero,run]; cases run code c s <;> rfl
  | succ t ih => rw [Nat.add_succ,run,ih]; simp only [Option.bind_assoc,run]

 theorem run_trans (code : Λ → Stmt Γ Λ σ) (c d e : Cfg Γ Λ σ) (s t : ℕ)
    (hs : run code c s=some d) (ht : run code d t=some e) : run code c (s+t)=some e := by
  rw [run_add,hs,Option.bind_some,ht]

 theorem run_one (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) : run code c 1=step code c := rfl

 theorem run_first (code : Λ → Stmt Γ Λ σ) (c : Cfg Γ Λ σ) (t : ℕ) :
    run code c (t+1)=(step code c).bind (fun d => run code d t) := by
  rw [show t+1=1+t by omega,run_add,run_one]

 theorem outputs {tm : Turing.FinTM2} (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (t : ℕ) (h : run tm.m (Turing.initList tm input) t=some (Turing.haltList tm output)) :
    Nonempty (Turing.TM2OutputsInTime tm input (some output) t) := by
  refine ⟨⟨⟨t,?_⟩,le_rfl⟩⟩
  have h' := run_iter tm.m (Turing.initList tm input) t
  rw [h'] at h
  exact h

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProgramEmbedding
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ : Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ : κ → Type} {Δ : μ → Type}

 abbrev StackSum (A : κ → Type) (B : μ → Type) : κ⊕μ → Type
   | .inl k => A k
   | .inr k => B k

 def extendStore (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) : ∀k : κ⊕μ,List (StackSum Γ Δ k) := fun k => match k with | .inl k => S k | .inr k => T k
 @[simp] theorem extendStore_inl (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) : extendStore S T (.inl k)=S k := rfl
 @[simp] theorem extendStore_inr (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : μ) : extendStore S T (.inr k)=T k := rfl

 def extendCfg (ret : Ω) (v : τ) (T : ∀k,List (Δ k)) (c : Cfg Γ Λ σ) :
     Cfg (StackSum Γ Δ) (Λ⊕Ω) (σ×τ) :=
   ⟨some (match c.l with | none => .inr ret | some l => .inl l),(c.var,v),extendStore c.stk T⟩
 def extendStmt (ret : Ω) : Stmt Γ Λ σ → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ)
   | .push k f q => .push (.inl k) (fun v => f v.1) (extendStmt ret q)
   | .pop k f q => .pop (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .peek k f q => .peek (.inl k) (fun v a => (f v.1 a,v.2)) (extendStmt ret q)
   | .load f q => .load (fun v => (f v.1,v.2)) (extendStmt ret q)
   | .branch f q r => .branch (fun v => f v.1) (extendStmt ret q) (extendStmt ret r)
   | .goto f => .goto (fun v => .inl (f v.1))
   | .halt => .goto (fun _ => .inr ret)

 theorem update_extend (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) (x : List (Γ k)) :
     Function.update (extendStore S T) (.inl k) x=extendStore (Function.update S k x) T := by
   funext j
   cases j with
   | inl j =>
     by_cases h : j=k
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
   | inr j => simp [Function.update,extendStore]

 theorem stepAux_extend (ret : Ω) (q : Stmt Γ Λ σ) (v : σ) (w : τ)
     (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) :
     stepAux (extendStmt ret q) (v,w) (extendStore S T)=extendCfg ret w T (stepAux q v S) := by
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
     cases hf : f v <;> simp only [extendStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_extend (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Λ⊕Ω → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode : ∀l,target (.inl l)=extendStmt ret (code l))
     (c : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (l : Λ) (hc : c.l=some l) :
     step target (extendCfg ret w T c)=(step code c).map (extendCfg ret w T) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [extendCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_extend ret (code l) v w S T)

 theorem run_extend (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Λ⊕Ω → Stmt (StackSum Γ Δ) (Λ⊕Ω) (σ×τ))
     (hcode : ∀l,target (.inl l)=extendStmt ret (code l))
     (c d : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (t : ℕ)
     (hr : RawStack.run code c t=some d) :
     RawStack.run target (extendCfg ret w T c) t=some (extendCfg ret w T d) := by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step code c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step code c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [step_extend ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramPrefix
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ μ Λ Ω σ τ : Type} [DecidableEq κ] [DecidableEq μ]
variable {Γ : κ → Type} {Δ : μ → Type}

 def prefixStore (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) : ∀k : μ⊕κ,List (StackSum Δ Γ k) := fun k => match k with | .inl k => T k | .inr k => S k
 @[simp] theorem prefixStore_source (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) : prefixStore S T (.inr k)=S k := rfl
 @[simp] theorem prefixStore_extra (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : μ) : prefixStore S T (.inl k)=T k := rfl

 def prefixCfg (ret : Ω) (v : τ) (T : ∀k,List (Δ k)) (c : Cfg Γ Λ σ) :
     Cfg (StackSum Δ Γ) (Ω⊕Λ) (τ×σ) :=
   ⟨some (match c.l with | none => .inl ret | some l => .inr l),(v,c.var),prefixStore c.stk T⟩
 def prefixStmt (ret : Ω) : Stmt Γ Λ σ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ)
   | .push k f q => .push (.inr k) (fun v => f v.2) (prefixStmt ret q)
   | .pop k f q => .pop (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .peek k f q => .peek (.inr k) (fun v a => (v.1,f v.2 a)) (prefixStmt ret q)
   | .load f q => .load (fun v => (v.1,f v.2)) (prefixStmt ret q)
   | .branch f q r => .branch (fun v => f v.2) (prefixStmt ret q) (prefixStmt ret r)
   | .goto f => .goto (fun v => .inr (f v.2))
   | .halt => .goto (fun _ => .inl ret)

 theorem update_prefix (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) (k : κ) (x : List (Γ k)) :
     Function.update (prefixStore S T) (.inr k) x=prefixStore (Function.update S k x) T := by
   funext j
   cases j with
   | inr j =>
     by_cases h : j=k
     · subst j; simp [Function.update,prefixStore]
     · simp [Function.update,prefixStore,h]
   | inl j => simp [Function.update,prefixStore]

 theorem stepAux_prefix (ret : Ω) (q : Stmt Γ Λ σ) (v : σ) (w : τ)
     (S : ∀k,List (Γ k)) (T : ∀k,List (Δ k)) :
     stepAux (prefixStmt ret q) (w,v) (prefixStore S T)=prefixCfg ret w T (stepAux q v S) := by
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
     cases hf : f v <;> simp only [prefixStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl

 theorem step_prefix (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Ω⊕Λ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ))
     (hcode : ∀l,target (.inr l)=prefixStmt ret (code l))
     (c : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (l : Λ) (hc : c.l=some l) :
     step target (prefixCfg ret w T c)=(step code c).map (prefixCfg ret w T) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [prefixCfg,step,hcode,Option.map_some]
   exact congrArg some (stepAux_prefix ret (code l) v w S T)

 theorem run_prefix (ret : Ω) (code : Λ → Stmt Γ Λ σ)
     (target : Ω⊕Λ → Stmt (StackSum Δ Γ) (Ω⊕Λ) (τ×σ))
     (hcode : ∀l,target (.inr l)=prefixStmt ret (code l))
     (c d : Cfg Γ Λ σ) (w : τ) (T : ∀k,List (Δ k)) (t : ℕ)
     (hr : RawStack.run code c t=some d) :
     RawStack.run target (prefixCfg ret w T c) t=some (prefixCfg ret w T d) := by
   induction t generalizing c with
   | zero => simp only [RawStack.run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [RawStack.run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step code c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step code c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [step_prefix ret code target hcode c w T l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.StackTape
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackTape

variable {K : Type} {Γ : K → Type} {b : ℕ}

/-- One-hot symbol slots in a fixed-width block; unused blocks are all false. -/
noncomputable def tapeBit (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (p : ℕ) : Bool :=
  if hr : p % (b + 1) < b then
    let x := e.symm ⟨p % (b + 1), hr⟩
    decide ((S x.1)[p / (b + 1)]? = some x.2)
  else false

 theorem read_cell (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (j : ℕ) (x : Sigma Γ) :
    tapeBit e S (j * (b + 1) + (e x).val) = decide ((S x.1)[j]? = some x.2) := by
  have hslot : (e x).val < b + 1 := (e x).isLt.trans (Nat.lt_succ_self _)
  have hmod : (j * (b + 1) + (e x).val) % (b + 1) = (e x).val := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hslot]
  have hdiv : (j * (b + 1) + (e x).val) / (b + 1) = j := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_succ b), Nat.div_eq_of_lt hslot, Nat.zero_add]
  have hr : (j * (b + 1) + (e x).val) % (b + 1) < b := by rw [hmod]; exact (e x).isLt
  have he : e.symm ⟨(j * (b + 1) + (e x).val) % (b + 1), hr⟩ = x := by
    calc
      _ = e.symm (e x) := congrArg e.symm (Fin.ext hmod)
      _ = x := e.symm_apply_apply x
  unfold tapeBit
  rw [dif_pos hr]
  simp only [hdiv]
  exact congrArg (fun z : Sigma Γ => decide ((S z.1)[j]? = some z.2)) he

 theorem tape_injective (e : (Sigma Γ) ≃ Fin b) : Function.Injective (tapeBit e) := by
  intro S T h
  funext k
  apply List.ext_getElem?
  intro j
  apply Option.ext
  intro γ
  have hh := congrFun h (j * (b + 1) + (e ⟨k,γ⟩).val)
  simp only [read_cell] at hh
  simpa only [Option.mem_def, eq_comm] using (decide_eq_decide.mp hh)

 theorem beyond_false (e : (Sigma Γ) ≃ Fin b) (S : ∀ k, List (Γ k)) (bound p : ℕ)
    (hbound : ∀ k, (S k).length ≤ bound) (hp : bound ≤ p / (b + 1)) : tapeBit e S p = false := by
  unfold tapeBit
  split_ifs with hr
  · dsimp
    have hlen := (hbound (e.symm ⟨p % (b + 1), hr⟩).1).trans hp
    simp [List.getElem?_eq_none hlen]
  · rfl

 theorem empty_tape (e : (Sigma Γ) ≃ Fin b) : tapeBit e (fun _ => []) = fun _ => false := by
  funext p
  exact beyond_false e (fun _ => []) 0 p (fun _ => Nat.le_refl _) (Nat.zero_le _)

end EdgeSublinearMWIS.Main.StackTape
end

-- Solutions.StackSpace
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackSpace

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

variable {K : Type} {Γ : K → Type} {Λ σ : Type}

 def cost : Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => cost q + 1
  | .peek _ _ q => cost q + 1
  | .pop _ _ q => cost q + 1
  | .load _ q => cost q + 1
  | .branch _ q r => max (cost q) (cost r) + 1
  | .goto _ => 1
  | .halt => 1

 theorem cost_pos (q : Turing.TM2.Stmt Γ Λ σ) : 0 < cost q := by cases q <;> simp [cost]

 def space [Fintype K] (S : ∀ k, List (Γ k)) : ℕ := ∑ k, (S k).length

 theorem space_update [Fintype K] [DecidableEq K] (S : ∀ k, List (Γ k)) (k : K) (L : List (Γ k)) :
    space (Function.update S k L) + (S k).length = space S + L.length := by
  have heq : (fun j => (Function.update S k L j).length) = Function.update (fun j => (S j).length) k L.length := by
    funext j
    by_cases h : j = k
    · subst j; simp
    · simp [Function.update, h]
  unfold space
  rw [heq, Finset.sum_update_of_mem (Finset.mem_univ k), Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add (s := Finset.univ) (fun j => (S j).length) (Finset.mem_univ k)
  omega

 theorem stepAux_space [Fintype K] [DecidableEq K] (q : Turing.TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ k, List (Γ k)) :
    space (Turing.TM2.stepAux q v S).stk ≤ space S + cost q := by
  induction q generalizing v S with
  | push k f q ih =>
    have hh := ih v (Function.update S k (f v :: S k))
    have hu := space_update S k (f v :: S k)
    simp only [List.length_cons] at hu
    change space (Turing.TM2.stepAux q v (Function.update S k (f v :: S k))).stk ≤ space S + (cost q + 1)
    omega
  | peek k f q ih =>
    have hh := ih (f v (S k).head?) S
    change space (Turing.TM2.stepAux q (f v (S k).head?) S).stk ≤ space S + (cost q + 1)
    omega
  | pop k f q ih =>
    have hh := ih (f v (S k).head?) (Function.update S k (S k).tail)
    have hu := space_update S k (S k).tail
    have hl : (S k).tail.length ≤ (S k).length := by simp only [List.length_tail]; omega
    change space (Turing.TM2.stepAux q (f v (S k).head?) (Function.update S k (S k).tail)).stk ≤ space S + (cost q + 1)
    omega
  | load f q ih =>
    have hh := ih (f v) S
    change space (Turing.TM2.stepAux q (f v) S).stk ≤ space S + (cost q + 1)
    omega
  | branch f q r ihq ihr =>
    change space (cond (f v) (Turing.TM2.stepAux q v S) (Turing.TM2.stepAux r v S)).stk ≤ space S + (max (cost q) (cost r) + 1)
    cases hv : f v with
    | false => simp only [cond_false]; have hh := ihr v S; have hm := le_max_right (cost q) (cost r); omega
    | true => simp only [cond_true]; have hh := ihq v S; have hm := le_max_left (cost q) (cost r); omega
  | goto f => simp [Turing.TM2.stepAux, cost]
  | halt => simp [Turing.TM2.stepAux, cost]

 def bound (tm : Turing.FinTM2) : ℕ := Finset.univ.sup (fun l => cost (tm.m l))

 theorem cost_le_bound (tm : Turing.FinTM2) (l : tm.Λ) : cost (tm.m l) ≤ bound tm := by
  unfold bound
  exact Finset.le_sup (f := fun l => cost (tm.m l)) (Finset.mem_univ l)

 theorem bound_pos (tm : Turing.FinTM2) : 0 < bound tm :=
  (cost_pos (tm.m tm.main)).trans_le (cost_le_bound tm tm.main)

 theorem initial_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    space (Turing.initList tm input).stk = input.length := by
  have hlen (k : tm.K) : ((Turing.initList tm input).stk k).length = if k = tm.k₀ then input.length else 0 := by
    by_cases h : k = tm.k₀
    · subst k; simp [Turing.initList]
    · simp [Turing.initList, h]
  unfold space
  simp only [hlen]
  simp

 set_option backward.isDefEq.respectTransparency.types false in
 theorem step_space (tm : Turing.FinTM2) (c c' : tm.Cfg) (h : tm.step c = some c') :
    space c'.stk ≤ space c.stk + bound tm := by
  letI : DecidableEq tm.K := tm.decidableEqK
  change Turing.TM2.step tm.m c = some c' at h
  rcases c with ⟨l,v,S⟩
  cases l with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some l =>
    change some (Turing.TM2.stepAux (tm.m l) v S) = some c' at h
    have heq := Option.some.inj h
    rw [← heq]
    exact (stepAux_space (tm.m l) v S).trans (Nat.add_le_add_left (cost_le_bound tm l) _)

 def run (tm : Turing.FinTM2) (start : tm.Cfg) : ℕ → Option tm.Cfg
  | 0 => some start
  | t + 1 => (run tm start t).bind tm.step

 theorem run_space (tm : Turing.FinTM2) (start : tm.Cfg) (t : ℕ) (c : tm.Cfg)
    (h : run tm start t = some c) : space c.stk ≤ space start.stk + bound tm * t := by
  induction t generalizing c with
  | zero => simp only [run, Option.some.injEq] at h; subst c; simp
  | succ t ih =>
    cases he : run tm start t with
    | none => simp only [run, he, Option.bind_none, reduceCtorEq] at h
    | some prev =>
      have hstep : tm.step prev = some c := by simpa only [run, he, Option.bind_some] using h
      have hi := ih prev he
      have hs := step_space tm prev c hstep
      rw [Nat.mul_succ]
      omega

 theorem input_run_space (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (t : ℕ) (c : tm.Cfg)
    (h : run tm (Turing.initList tm input) t = some c) : space c.stk ≤ input.length + bound tm * t := by
  simpa only [initial_space] using run_space tm (Turing.initList tm input) t c h

 theorem stack_length_le_space [Fintype K] (S : ∀ k, List (Γ k)) (k : K) : (S k).length ≤ space S := by
  unfold space
  exact Finset.single_le_sum (f := fun j => (S j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)

end EdgeSublinearMWIS.Main.StackSpace
end

-- Solutions.StackCompilerTypes
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.StackCompiler

attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

noncomputable instance alphabetFintype (P : EdgeSublinearMWIS.Main.Program) (k : P.machine.tm.K) :
    Fintype (P.machine.tm.Γ k) := @Fintype.ofFinite _ (P.finiteAlphabet k)

noncomputable def allStatements (P : EdgeSublinearMWIS.Main.Program) : Finset P.machine.tm.Stmt :=
  Finset.univ.biUnion (fun l => Turing.TM2.stmts₁ (P.machine.tm.m l))

abbrev Statement (P : EdgeSublinearMWIS.Main.Program) := {q // q ∈ allStatements P}

abbrev Resume (P : EdgeSublinearMWIS.Main.Program) := Statement P × P.machine.tm.σ

noncomputable def alphabetCode (P : EdgeSublinearMWIS.Main.Program) :
    (Sigma P.machine.tm.Γ) ≃ Fin (Fintype.card (Sigma P.machine.tm.Γ)) := Fintype.equivFin _

noncomputable def blockSize (P : EdgeSublinearMWIS.Main.Program) : ℕ := Fintype.card (Sigma P.machine.tm.Γ) + 1

 theorem blockSize_pos (P : EdgeSublinearMWIS.Main.Program) : 0 < blockSize P := Nat.zero_lt_succ _

 theorem main_mem (P : EdgeSublinearMWIS.Main.Program) (l : P.machine.tm.Λ) :
    P.machine.tm.m l ∈ allStatements P := by
  exact Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ _, Turing.TM2.stmts₁_self⟩

noncomputable instance resumeFintype (P : EdgeSublinearMWIS.Main.Program) : Fintype (Resume P) := inferInstance

end EdgeSublinearMWIS.Main.StackCompiler
end

-- Solutions.ProgramSequence
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Phase where | out | into | finish deriving Fintype,DecidableEq
 abbrev SeqK (P Q : Program) := P.machine.tm.K⊕(Q.machine.tm.K⊕Unit)
 abbrev SeqΓ (P Q : Program) : SeqK P Q → Type := StackSum P.machine.tm.Γ (StackSum Q.machine.tm.Γ (fun _ : Unit => Bool))
 noncomputable instance seqAlphabet (P Q : Program) (k : SeqK P Q) : Fintype (SeqΓ P Q k) :=
   @Fintype.ofFinite _ (by
     cases k with
     | inl k => exact P.finiteAlphabet k
     | inr k => cases k with
       | inl k => exact Q.finiteAlphabet k
       | inr u => change Finite Bool; infer_instance)
 abbrev SeqΛ (P Q : Program) := P.machine.tm.Λ⊕(Q.machine.tm.Λ⊕Phase)
 abbrev Seqσ (P Q : Program) := P.machine.tm.σ×(Q.machine.tm.σ×Option Bool)
 def seqInitial (P Q : Program) : Seqσ P Q := (P.machine.tm.initialState,(Q.machine.tm.initialState,none))
 def setCarry {P Q : Program} (v : Seqσ P Q) (b : Option Bool) : Seqσ P Q := (v.1,(v.2.1,b))
 def outLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .out)
 def intoLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .into)
 def finishLabel {P Q : Program} : SeqΛ P Q := .inr (.inr .finish)
 def tempStack {P Q : Program} : SeqK P Q := .inr (.inr ())

 def seqCode (P Q : Program) : SeqΛ P Q → Stmt (SeqΓ P Q) (SeqΛ P Q) (Seqσ P Q)
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

 def seqTM (P Q : Program) : Turing.FinTM2 where
   K := SeqK P Q
   Γ := SeqΓ P Q
   Λ := SeqΛ P Q
   σ := Seqσ P Q
   k₀ := .inl P.machine.tm.k₀
   k₁ := .inr (.inl Q.machine.tm.k₁)
   initialState := seqInitial P Q
   main := .inl P.machine.tm.main
   m := seqCode P Q
 def sequence (P Q : Program) : Program where
   machine := ⟨seqTM P Q,(by change P.machine.tm.Γ P.machine.tm.k₀ ≃ Bool; exact P.machine.inputAlphabet),
     (by change Q.machine.tm.Γ Q.machine.tm.k₁ ≃ Bool; exact Q.machine.outputAlphabet)⟩
   finiteAlphabet k := by
     cases k with
     | inl k => exact P.finiteAlphabet k
     | inr k => cases k with
       | inl k => exact Q.finiteAlphabet k
       | inr u => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramTransfer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def onlyStack {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L : List (Γ k)) : ∀j,List (Γ j) :=
   Function.update (fun _ => []) k L
 @[simp] theorem onlyStack_self {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L : List (Γ k)) : onlyStack k L k=L := by simp [onlyStack]
 theorem onlyStack_nil {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) : onlyStack k ([] : List (Γ k))=(fun _ => []) := by simp [onlyStack,Function.update_eq_self]
 theorem onlyStack_update {κ : Type} [DecidableEq κ] {Γ : κ → Type} (k : κ) (L R : List (Γ k)) :
     Function.update (onlyStack k L) k R=onlyStack k R := by simp [onlyStack,Function.update_idem]

 def outStore (P Q : Program) (L acc : List Bool) : ∀k,List (SeqΓ P Q k) :=
   extendStore (onlyStack P.machine.tm.k₁ (L.map P.machine.outputAlphabet.symm))
     (extendStore (fun _ => []) (fun _ : Unit => acc))
 def intoStore (P Q : Program) (L acc : List Bool) : ∀k,List (SeqΓ P Q k) :=
   extendStore (fun _ => [])
     (extendStore (onlyStack Q.machine.tm.k₀ (acc.map Q.machine.inputAlphabet.symm)) (fun _ : Unit => L))
 def outCfg (P Q : Program) (L acc : List Bool) : (seqTM P Q).Cfg :=
   cfg (some outLabel) (seqInitial P Q) (outStore P Q L acc)
 def intoCfg (P Q : Program) (L acc : List Bool) : (seqTM P Q).Cfg :=
   cfg (some intoLabel) (seqInitial P Q) (intoStore P Q L acc)

 theorem out_step_cons (P Q : Program) (b : Bool) (L acc : List Bool) :
     step (seqCode P Q) (outCfg P Q (b::L) acc)=some (outCfg P Q L (b::acc)) := by
   change step (seqCode P Q) (cfg (some outLabel) (seqInitial P Q) (outStore P Q (b::L) acc))=
     some (cfg (some outLabel) (seqInitial P Q) (outStore P Q L (b::acc)))
   simp only [cfg,step,seqCode,outLabel,stepAux,outStore,seqInitial,setCarry,extendStore_inl,
     List.map_cons,onlyStack_self,List.head?_cons,Option.map_some,Equiv.apply_symm_apply,Option.isSome_some,
     cond_true,Option.getD_some,List.tail_cons,tempStack,extendStore_inr,Function.update_of_ne (by simp :
       (Sum.inl P.machine.tm.k₁ : SeqK P Q)≠Sum.inr (Sum.inr ()))]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k =>
     by_cases hk : k=P.machine.tm.k₁
     · subst k
       simp [Function.update,onlyStack,extendStore]
     · simp [Function.update,onlyStack,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [Function.update,onlyStack,extendStore]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramSequenceRun
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 def qCfg (P Q : Program) (c : Q.machine.tm.Cfg) : (seqTM P Q).Cfg :=
   prefixCfg P.machine.tm.main P.machine.tm.initialState (fun _ => [])
     (extendCfg .finish (none : Option Bool) (fun _ : Unit => []) c)
 theorem q_stepAux (P Q : Program) (q : Q.machine.tm.Stmt) (v : Q.machine.tm.σ)
     (S : ∀k,List (Q.machine.tm.Γ k)) :
     stepAux (prefixStmt P.machine.tm.main (extendStmt .finish q))
       (P.machine.tm.initialState,(v,(none : Option Bool)))
       (prefixStore (extendStore S (fun _ : Unit => [])) (fun _ => []))=
         qCfg P Q (stepAux q v S) := by
   rw [stepAux_prefix,stepAux_extend]
   rfl
 theorem q_step (P Q : Program) (c : Q.machine.tm.Cfg) (l : Q.machine.tm.Λ) (hc : c.l=some l) :
     step (seqCode P Q) (qCfg P Q c)=(step Q.machine.tm.m c).map (qCfg P Q) := by
   rcases c with ⟨cl,v,S⟩
   dsimp only at hc
   subst cl
   simp only [qCfg,prefixCfg,extendCfg,step,seqCode,Option.map_some]
   exact congrArg some (q_stepAux P Q (Q.machine.tm.m l) v S)
 theorem q_run (P Q : Program) (c d : Q.machine.tm.Cfg) (t : ℕ)
     (hr : run Q.machine.tm.m c t=some d) :
     run (seqCode P Q) (qCfg P Q c) t=some (qCfg P Q d) := by
   induction t generalizing c with
   | zero => simp only [run,Option.some.injEq] at hr; subst d; rfl
   | succ t ih =>
     rw [run_first] at hr ⊢
     cases hc : c.l with
     | none =>
       have hn : step Q.machine.tm.m c=none := by cases c; simp_all [step]
       rw [hn,Option.bind_none] at hr
       contradiction
     | some l =>
       have hs : ∃ e,step Q.machine.tm.m c=some e := by cases c; simp_all [step]
       obtain ⟨e,he⟩ := hs
       rw [q_step P Q c l hc,he,Option.map_some,Option.bind_some]
       rw [he,Option.bind_some] at hr
       exact ih e hr

 theorem outputs_run (P : Program) (input output : List Bool) (T : ℕ) (h : Runs P input output T) :
     ∃ t,t≤T ∧ run P.machine.tm.m (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
       some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)) := by
   obtain ⟨h⟩ := h
   refine ⟨h.steps,h.steps_le_m,?_⟩
   rw [RawStack.run_iter]
   exact h.evals_in_steps

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramTransferEnd
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem out_step_nil (P Q : Program) (acc : List Bool) :
     step (seqCode P Q) (outCfg P Q [] acc)=some (intoCfg P Q acc []) := by
   simp [outCfg,intoCfg,cfg,step,seqCode,outLabel,intoLabel,stepAux,outStore,intoStore,seqInitial,setCarry,
     onlyStack_nil,tempStack,extendStore]
 theorem into_step_cons (P Q : Program) (b : Bool) (L acc : List Bool) :
     step (seqCode P Q) (intoCfg P Q (b::L) acc)=some (intoCfg P Q L (b::acc)) := by
   simp only [intoCfg,cfg,step,seqCode,intoLabel,stepAux,intoStore,seqInitial,setCarry,tempStack,
     extendStore_inr,extendStore_inl,List.head?_cons,Option.isSome_some,cond_true,Option.getD_some,List.tail_cons]
   congr 1
   congr 1
   funext k
   cases k with
   | inl k => simp [Function.update,onlyStack,extendStore]
   | inr k => cases k with
     | inl k =>
       by_cases hk : k=Q.machine.tm.k₀
       · subst k; simp [Function.update,onlyStack,extendStore]
       · simp [Function.update,onlyStack,extendStore,hk]
     | inr u => cases u; simp [Function.update,onlyStack,extendStore]

 theorem initList_store (tm : Turing.FinTM2) (L : List (tm.Γ tm.k₀)) :
     (Turing.initList tm L).stk=onlyStack tm.k₀ L := by
   funext k
   by_cases h : k=tm.k₀
   · subst k; simp [Turing.initList,onlyStack]
   · simp [Turing.initList,onlyStack,Function.update,h]
 theorem haltList_store (tm : Turing.FinTM2) (L : List (tm.Γ tm.k₁)) :
     (Turing.haltList tm L).stk=onlyStack tm.k₁ L := by
   funext k
   by_cases h : k=tm.k₁
   · subst k; simp [Turing.haltList,onlyStack]
   · simp [Turing.haltList,onlyStack,Function.update,h]

 theorem into_step_nil (P Q : Program) (acc : List Bool) :
     step (seqCode P Q) (intoCfg P Q [] acc)=some (qCfg P Q
       (Turing.initList Q.machine.tm (acc.map Q.machine.inputAlphabet.symm))) := by
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
       by_cases hk : k=Q.machine.tm.k₀
       · subst k; simp [prefixStore,extendStore,Function.update,onlyStack]
       · simp [prefixStore,extendStore,Function.update,onlyStack,hk]
     | inr u => cases u; simp [prefixStore,extendStore,Function.update,onlyStack]

 theorem out_loop (P Q : Program) (L acc : List Bool) :
     run (seqCode P Q) (outCfg P Q L acc) (L.length+1)=some (intoCfg P Q (L.reverse++acc) []) := by
   induction L generalizing acc with
   | nil => exact out_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,out_step_cons,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem into_loop (P Q : Program) (L acc : List Bool) :
     run (seqCode P Q) (intoCfg P Q L acc) (L.length+1)=some (qCfg P Q
       (Turing.initList Q.machine.tm ((L.reverse++acc).map Q.machine.inputAlphabet.symm))) := by
   induction L generalizing acc with
   | nil => exact into_step_nil P Q acc
   | cons b L ih =>
     rw [List.length_cons,run_first,into_step_cons,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ProgramCompositionRuns
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2 EdgeSublinearMWIS.Main.RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem cfg_eq {κ Λ σ : Type} {Γ : κ → Type} {c d : Cfg Γ Λ σ}
     (hl : c.l=d.l) (hv : c.var=d.var) (hs : c.stk=d.stk) : c=d := by
   cases c; cases d; simp_all

 def seqExtra (Q : Program) : ∀k : Q.machine.tm.K⊕Unit,List (StackSum Q.machine.tm.Γ (fun _ : Unit => Bool) k) :=
   extendStore (fun _ => []) (fun _ => [])
 theorem p_start (P Q : Program) (input : List Bool) :
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q)
       (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm))=
         Turing.initList (seqTM P Q) (input.map P.machine.inputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.initList P.machine.tm _).stk (seqExtra Q)=(Turing.initList (seqTM P Q) _).stk
   rw [initList_store,initList_store]
   funext k
   cases k with
   | inl k =>
     by_cases hk : k=P.machine.tm.k₀
     · subst k; simp [onlyStack,Function.update,seqTM,extendStore]
     · simp [onlyStack,Function.update,seqTM,extendStore,hk]
   | inr k => cases k with
     | inl k => simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
     | inr u => cases u; simp [onlyStack,Function.update,seqTM,extendStore,seqExtra]
 theorem p_finish (P Q : Program) (output : List Bool) :
     extendCfg (.inr Phase.out) (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q)
       (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm))=outCfg P Q output [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList P.machine.tm _).stk (seqExtra Q)=outStore P Q output []
   rw [haltList_store]
   rfl
 theorem finish_step (P Q : Program) (output : List Bool) :
     step (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm)))=
       some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)) := by
   change some (cfg none (seqInitial P Q)
     (prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _ : Unit => [])) (fun _ => [])))=some _
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change prefixStore (extendStore (Turing.haltList Q.machine.tm _).stk (fun _ : Unit => [])) (fun _ => [])=
     (Turing.haltList (seqTM P Q) _).stk
   rw [haltList_store,haltList_store]
   funext k
   cases k with
   | inl k => simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
   | inr k => cases k with
     | inl k =>
       by_cases hk : k=Q.machine.tm.k₁
       · subst k; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]
       · simp [prefixStore,extendStore,onlyStack,Function.update,seqTM,hk]
     | inr u => cases u; simp [prefixStore,extendStore,onlyStack,Function.update,seqTM]

 theorem sequence_runs (P Q : Program) (input middle output : List Bool) (T U : ℕ)
     (hP : Runs P input middle T) (hQ : Runs Q middle output U) :
     Runs (sequence P Q) input output (T+U+2*middle.length+3) := by
   obtain ⟨t,ht,hp⟩ := outputs_run P input middle T hP
   obtain ⟨u,hu,hq⟩ := outputs_run Q middle output U hQ
   have h1 := run_extend (.inr Phase.out) P.machine.tm.m (seqCode P Q) (fun _ => rfl)
     _ _ (Q.machine.tm.initialState,(none : Option Bool)) (seqExtra Q) t hp
   rw [p_start,p_finish] at h1
   have h2 := out_loop P Q middle []
   simp only [List.append_nil] at h2
   have h3 := into_loop P Q middle.reverse []
   simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h3
   have h4 := q_run P Q _ _ u hq
   have h5 : run (seqCode P Q) (qCfg P Q (Turing.haltList Q.machine.tm (output.map Q.machine.outputAlphabet.symm))) 1=
     some (Turing.haltList (seqTM P Q) (output.map Q.machine.outputAlphabet.symm)) := finish_step P Q output
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have hr := run_trans _ _ _ _ _ _ hr h4
   have hr := run_trans _ _ _ _ _ _ hr h5
   have he := RawStack.outputs (tm:=seqTM P Q) (input.map P.machine.inputAlphabet.symm)
     (output.map Q.machine.outputAlphabet.symm) _ hr
   obtain ⟨he⟩ := he
   refine ⟨{he with steps_le_m := he.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.RepeatStore
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open ProgramComposition
 theorem update_extend_right {κ μ : Type} [DecidableEq κ] [DecidableEq μ] {Γ : κ → Type} {Δ : μ → Type}
     (S : ∀k,List (Γ k)) (E : ∀k,List (Δ k)) (e : μ) (L : List (Δ e)) :
     Function.update (extendStore S E) (.inr e) L=extendStore S (Function.update E e L) := by
   funext k
   cases k with
   | inl k => simp [Function.update,extendStore]
   | inr j =>
     by_cases h : j=e
     · subst j; simp [Function.update,extendStore]
     · simp [Function.update,extendStore,h]
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.ProgramRepeat
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Extra where | raw | count | temp | out deriving Fintype,DecidableEq
 inductive Phase where | count | rawDrain | feed | check | bodyDrain | emitDrain | emitFeed deriving Fintype,DecidableEq
 abbrev K (U : Program) := U.machine.tm.K⊕Extra
 abbrev Gamma (U : Program) : K U → Type := StackSum U.machine.tm.Γ (fun _ : Extra => Bool)
 abbrev Label (U : Program) := U.machine.tm.Λ⊕Phase
 abbrev State (U : Program) := U.machine.tm.σ×Option Bool
 def carry {U : Program} (v : State U) (a : Option Bool) : State U := (v.1,a)
 def next {U : Program} (p : Phase) : Stmt (Gamma U) (Label U) (State U) :=
   .load (fun v => carry v none) (.goto (fun _ => .inr p))
 def code (U : Program) : Label U → Stmt (Gamma U) (Label U) (State U)
   | .inl l => extendStmt .bodyDrain (U.machine.tm.m l)
   | .inr .count =>
     .pop (.inr .raw) (fun v a => carry v a)
       (.branch (fun v => v.2.getD false)
         (.push (.inr .count) (fun _ => true) (next .count)) (next .rawDrain))
   | .inr .rawDrain =>
     .pop (.inr .raw) (fun v a => carry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (next .rawDrain)) (next .feed))
   | .inr .feed =>
     .pop (.inr .temp) (fun v a => carry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₀) (fun v => U.machine.inputAlphabet.symm (v.2.getD false)) (next .feed))
         (.load (fun _ => (U.machine.tm.initialState,none)) (.goto (fun _ => .inr .check))))
   | .inr .check =>
     .pop (.inr .count) (fun v a => carry v a)
       (.branch (fun v => v.2.isSome)
         (.load (fun _ => (U.machine.tm.initialState,none)) (.goto (fun _ => .inl U.machine.tm.main))) (next .emitDrain))
   | .inr .bodyDrain =>
     .pop (.inl U.machine.tm.k₁) (fun v a => carry v (a.map U.machine.outputAlphabet))
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (next .bodyDrain)) (next .feed))
   | .inr .emitDrain =>
     .pop (.inl U.machine.tm.k₀) (fun v a => carry v (a.map U.machine.inputAlphabet))
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (next .emitDrain)) (next .emitFeed))
   | .inr .emitFeed =>
     .pop (.inr .temp) (fun v a => carry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .out) (fun v => v.2.getD false) (next .emitFeed))
         (.load (fun _ => (U.machine.tm.initialState,none)) .halt))
 noncomputable instance alphabet (U : Program) (k : K U) : Fintype (Gamma U k) :=
   @Fintype.ofFinite _ (by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance)
 def tm (U : Program) : Turing.FinTM2 where
   K := K U
   Γ := Gamma U
   Λ := Label U
   σ := State U
   k₀ := .inr .raw
   k₁ := .inr .out
   initialState := (U.machine.tm.initialState,none)
   main := .inr .count
   m := code U
 def program (U : Program) : Program where
   machine := ⟨tm U,(by change Bool ≃ Bool; exact Equiv.refl _),(by change Bool ≃ Bool; exact Equiv.refl _)⟩
   finiteAlphabet k := by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance
 def store (R N T O : List Bool) : Extra → List Bool
   | .raw => R | .count => N | .temp => T | .out => O
 def stateCfg (U : Program) (p : Phase) (S : ∀k,List (U.machine.tm.Γ k)) (R N T O : List Bool) : (tm U).Cfg :=
   RawStack.cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (store R N T O))
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.RepeatSteps
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem count_true (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N T O : List Bool) :
     step (code U) (stateCfg U .count S (true::R) N T O)=some (stateCfg U .count S R (true::N) T O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.count≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem count_false (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N T O : List Bool) :
     step (code U) (stateCfg U .count S (false::R) N T O)=some (stateCfg U .rawDrain S R N T O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem rawDrain_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R N T O : List Bool) :
     step (code U) (stateCfg U .rawDrain S (b::R) N T O)=some (stateCfg U .rawDrain S R N (b::T) O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.temp≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem rawDrain_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (N T O : List Bool) :
     step (code U) (stateCfg U .rawDrain S [] N T O)=some (stateCfg U .feed S [] N T O) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
 theorem feed_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R N T O : List Bool) :
     step (code U) (stateCfg U .feed S R N (b::T) O)=some (stateCfg U .feed
       (Function.update S U.machine.tm.k₀ (U.machine.inputAlphabet.symm b::S U.machine.tm.k₀)) R N T O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
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
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem feed_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N O : List Bool) :
     step (code U) (stateCfg U .feed S R N [] O)=some (stateCfg U .check S R N [] O) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
 theorem check_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R N T O : List Bool) :
     step (code U) (stateCfg U .check S R (b::N) T O)=
       some (cfg (some (.inl U.machine.tm.main)) (U.machine.tm.initialState,none) (extendStore S (store R N T O))) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem check_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R T O : List Bool) :
     step (code U) (stateCfg U .check S R [] T O)=some (stateCfg U .emitDrain S R [] T O) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.RepeatTransfer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem bodyDrain_cons (U : Program) (b : Bool) (L R N T O : List Bool) :
     step (code U) (stateCfg U .bodyDrain (onlyStack U.machine.tm.k₁ ((b::L).map U.machine.outputAlphabet.symm)) R N T O)=
       some (stateCfg U .bodyDrain (onlyStack U.machine.tm.k₁ (L.map U.machine.outputAlphabet.symm)) R N (b::T) O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inl,
     onlyStack_self,List.map_cons,List.head?_cons,List.tail_cons,Option.map_some,Equiv.apply_symm_apply,
     Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend,onlyStack_update,extendStore_inr,store,update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem bodyDrain_nil (U : Program) (R N T O : List Bool) :
     step (code U) (stateCfg U .bodyDrain (fun _ => []) R N T O)=
       some (stateCfg U .feed (fun _ => []) R N T O) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
 theorem emitDrain_cons (U : Program) (b : Bool) (L R N T O : List Bool) :
     step (code U) (stateCfg U .emitDrain (onlyStack U.machine.tm.k₀ ((b::L).map U.machine.inputAlphabet.symm)) R N T O)=
       some (stateCfg U .emitDrain (onlyStack U.machine.tm.k₀ (L.map U.machine.inputAlphabet.symm)) R N (b::T) O) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inl,
     onlyStack_self,List.map_cons,List.head?_cons,List.tail_cons,Option.map_some,Equiv.apply_symm_apply,
     Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend,onlyStack_update,extendStore_inr,store,update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem emitDrain_nil (U : Program) (R N T O : List Bool) :
     step (code U) (stateCfg U .emitDrain (fun _ => []) R N T O)=
       some (stateCfg U .emitFeed (fun _ => []) R N T O) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
 theorem emitFeed_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R N T O : List Bool) :
     step (code U) (stateCfg U .emitFeed S R N (b::T) O)=some (stateCfg U .emitFeed S R N T (b::O)) := by
   simp only [stateCfg,cfg,step,code,stepAux,carry,next,extendStore_inr,store,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.out≠Extra.temp)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,store]
 theorem emitFeed_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N O : List Bool) :
     step (code U) (stateCfg U .emitFeed S R N [] O)=some (cfg none (U.machine.tm.initialState,none) (extendStore S (store R N [] O))) := by
   simp [stateCfg,cfg,step,code,stepAux,carry,next,store,extendStore,Function.update]
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.RepeatLoops
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem parse_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (n : ℕ) (R N T O : List Bool) :
     run (code U) (stateCfg U .count S (List.replicate n true++false::R) N T O) (n+1)=
       some (stateCfg U .rawDrain S R (List.replicate n true++N) T O) := by
   induction n generalizing N with
   | zero => exact count_false U S R N T O
   | succ n ih =>
     simp only [List.replicate_succ,List.cons_append]
     rw [run_first,count_true,Option.bind_some]
     have hh := ih (true::N)
     have he : List.replicate n true++true::N=true::(List.replicate n true++N) := by
       calc
         _ = (List.replicate n true++[true])++N := by simp
         _ = List.replicate (n+1) true++N := by rw [List.replicate_succ']
         _ = _ := rfl
     simpa only [he] using hh
 theorem rawDrain_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L N T O : List Bool) :
     run (code U) (stateCfg U .rawDrain S L N T O) (L.length+1)=
       some (stateCfg U .feed S [] N (L.reverse++T) O) := by
   induction L generalizing T with
   | nil => exact rawDrain_nil U S N T O
   | cons b L ih =>
     rw [List.length_cons,run_first,rawDrain_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem feed_loop (U : Program) (L acc R N O : List Bool) :
     run (code U) (stateCfg U .feed (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R N L O) (L.length+1)=
       some (stateCfg U .check (onlyStack U.machine.tm.k₀ ((L.reverse++acc).map U.machine.inputAlphabet.symm)) R N [] O) := by
   induction L generalizing acc with
   | nil => exact feed_nil U _ R N O
   | cons b L ih =>
     rw [List.length_cons,run_first,feed_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem bodyDrain_loop (U : Program) (L R N T O : List Bool) :
     run (code U) (stateCfg U .bodyDrain (onlyStack U.machine.tm.k₁ (L.map U.machine.outputAlphabet.symm)) R N T O) (L.length+1)=
       some (stateCfg U .feed (fun _ => []) R N (L.reverse++T) O) := by
   induction L generalizing T with
   | nil => simpa only [List.map_nil,onlyStack_nil,List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,run_one] using bodyDrain_nil U R N T O
   | cons b L ih =>
     rw [List.length_cons,run_first,bodyDrain_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem emitDrain_loop (U : Program) (L R N T O : List Bool) :
     run (code U) (stateCfg U .emitDrain (onlyStack U.machine.tm.k₀ (L.map U.machine.inputAlphabet.symm)) R N T O) (L.length+1)=
       some (stateCfg U .emitFeed (fun _ => []) R N (L.reverse++T) O) := by
   induction L generalizing T with
   | nil => simpa only [List.map_nil,onlyStack_nil,List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append,run_one] using emitDrain_nil U R N T O
   | cons b L ih =>
     rw [List.length_cons,run_first,emitDrain_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem emitFeed_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L R N O : List Bool) :
     run (code U) (stateCfg U .emitFeed S R N L O) (L.length+1)=
       some (cfg none (U.machine.tm.initialState,none) (extendStore S (store R N [] (L.reverse++O)))) := by
   induction L generalizing O with
   | nil => exact emitFeed_nil U S R N O
   | cons b L ih =>
     rw [List.length_cons,run_first,emitFeed_cons,Option.bind_some]
     have hh := ih (b::O)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.RepeatRuns
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem repeat_start (U : Program) (n : ℕ) (input : List Bool) :
     Turing.initList (tm U) (List.replicate n true++false::input)=
       stateCfg U .count (fun _ => []) (List.replicate n true++false::input) [] [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [tm,stateCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [tm,stateCfg,cfg,onlyStack,Function.update,extendStore,store]
 theorem repeat_body_start (U : Program) (input : List Bool) (N : List Bool) :
     extendCfg (Phase.bodyDrain) (none : Option Bool) (store [] N [] [])
       (Turing.initList U.machine.tm (input.map U.machine.inputAlphabet.symm))=
         cfg (some (.inl U.machine.tm.main)) (U.machine.tm.initialState,none)
           (extendStore (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm)) (store [] N [] [])) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.initList U.machine.tm _).stk _=_
   rw [initList_store]
   rfl
 theorem repeat_body_end (U : Program) (output : List Bool) (N : List Bool) :
     extendCfg (Phase.bodyDrain) (none : Option Bool) (store [] N [] [])
       (Turing.haltList U.machine.tm (output.map U.machine.outputAlphabet.symm))=
         stateCfg U .bodyDrain (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] N [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList U.machine.tm _).stk _=_
   rw [haltList_store]
   rfl
 theorem repeat_initial (U : Program) (n : ℕ) (input : List Bool) :
     run (code U) (Turing.initList (tm U) (List.replicate n true++false::input)) (n+2*input.length+3)=
       some (stateCfg U .check (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm)) [] (List.replicate n true) [] []) := by
   have h1 := parse_loop U (fun _ => []) n input [] [] []
   simp only [List.append_nil] at h1
   rw [← repeat_start] at h1
   have h2 := rawDrain_loop U (fun _ => []) input (List.replicate n true) [] []
   simp only [List.append_nil] at h2
   have h3 := feed_loop U input.reverse [] [] (List.replicate n true) []
   simp only [List.map_nil,onlyStack_nil,List.reverse_reverse,List.append_nil,List.length_reverse] at h3
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have he : n+2*input.length+3=(n+1+(input.length+1))+(input.length+1) := by omega
   rw [he]
   exact hr
 theorem repeat_turn (U : Program) (input output : List Bool) (N : List Bool) (b : Bool) (T : ℕ)
     (hU : Runs U input output T) :
     ∃ t, t ≤ T+2*output.length+3 ∧
       run (code U) (stateCfg U .check (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm)) [] (b::N) [] []) t=
         some (stateCfg U .check (onlyStack U.machine.tm.k₀ (output.map U.machine.inputAlphabet.symm)) [] N [] []) := by
   obtain ⟨t,ht,hu⟩ := outputs_run U input output T hU
   have h1 : run (code U) (stateCfg U .check (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm)) [] (b::N) [] []) 1=_ :=
     check_cons U _ b [] N [] []
   have h2 := run_extend .bodyDrain U.machine.tm.m (code U) (fun _ => rfl) _ _ (none : Option Bool) (store [] N [] []) t hu
   rw [repeat_body_start,repeat_body_end] at h2
   have h3 := bodyDrain_loop U output [] N [] []
   simp only [List.append_nil] at h3
   have h4 := feed_loop U output.reverse [] [] N []
   simp only [List.map_nil,onlyStack_nil,List.reverse_reverse,List.append_nil,List.length_reverse] at h4
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have hr := run_trans _ _ _ _ _ _ hr h4
   exact ⟨_,by omega,hr⟩
 theorem repeat_halt (U : Program) (output : List Bool) :
     run (code U) (stateCfg U .check (onlyStack U.machine.tm.k₀ (output.map U.machine.inputAlphabet.symm)) [] [] [] []) (2*output.length+3)=
       some (Turing.haltList (tm U) output) := by
   have h1 : run (code U) (stateCfg U .check (onlyStack U.machine.tm.k₀ (output.map U.machine.inputAlphabet.symm)) [] [] [] []) 1=_ :=
     check_nil U _ [] [] []
   have h2 := emitDrain_loop U output [] [] [] []
   simp only [List.append_nil] at h2
   have h3 := emitFeed_loop U (fun _ => []) output.reverse [] [] []
   simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h3
   have he : cfg (none : Option (Label U)) (U.machine.tm.initialState,none)
       (extendStore (fun k => ([] : List (U.machine.tm.Γ k))) (store [] [] [] output))=Turing.haltList (tm U) output := by
     apply cfg_eq
     case hl => rfl
     case hv => rfl
     rw [haltList_store]
     funext k
     cases k with
     | inl k => simp [cfg,tm,extendStore,store,onlyStack,Function.update]
     | inr e => cases e <;> simp [cfg,tm,extendStore,store,onlyStack,Function.update]
   rw [he] at h3
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have he : 2*output.length+3=(1+(output.length+1))+(output.length+1) := by omega
   rw [he]
   exact hr
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.RepeatBound
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramRepeat
open Turing.TM2 ProgramComposition RawStack
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 theorem repeat_loop (U : Program) (v : ℕ → List Bool) (n T V : ℕ) (N : List Bool)
     (hstep : ∀i,i< n → Runs U (v i) (v (i+1)) T)
     (hsize : ∀i,i≤ n → (v i).length≤ V) :
     ∃ t,t≤ n*(T+2*V+3) ∧
       run (code U) (stateCfg U .check (onlyStack U.machine.tm.k₀ ((v 0).map U.machine.inputAlphabet.symm)) [] (List.replicate n true++N) [] []) t=
         some (stateCfg U .check (onlyStack U.machine.tm.k₀ ((v n).map U.machine.inputAlphabet.symm)) [] N [] []) := by
   induction n generalizing v with
   | zero => exact ⟨0,by omega,rfl⟩
   | succ n ih =>
     obtain ⟨t,ht,hr⟩ := repeat_turn U (v 0) (v 1) (List.replicate n true++N) true T (hstep 0 (by omega))
     obtain ⟨s,hs,hsr⟩ := ih (fun i => v (i+1)) (by intro i hi; exact hstep (i+1) (by omega))
       (by intro i hi; exact hsize (i+1) (by omega))
     have hr' := run_trans _ _ _ _ _ _ hr hsr
     refine ⟨t+s,?_,?_⟩
     · have hv := hsize 1 (by omega)
       nlinarith
     · simpa only [List.replicate_succ,List.cons_append] using hr'
 theorem repeat_runs (U : Program) (v : ℕ → List Bool) (n T V : ℕ)
     (hstep : ∀i,i< n → Runs U (v i) (v (i+1)) T)
     (hsize : ∀i,i≤ n → (v i).length≤ V) :
     Runs (program U) (List.replicate n true++false::v 0) (v n) (10*(n+1)*(T+V+1)) := by
   have h1 := repeat_initial U n (v 0)
   obtain ⟨t,ht,h2⟩ := repeat_loop U v n T V [] hstep hsize
   simp only [List.append_nil] at h2
   have h3 := repeat_halt U (v n)
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   obtain ⟨ho⟩ := RawStack.outputs (tm:=tm U) (List.replicate n true++false::v 0) (v n) _ hr
   change Nonempty (Turing.TM2OutputsInTime (tm U) ((List.replicate n true++false::v 0).map id) (some ((v n).map id)) _)
   simp only [List.map_id]
   refine ⟨{ho with steps_le_m := ho.steps_le_m.trans ?_}⟩
   have hv0 := hsize 0 (by omega)
   have hvn := hsize n le_rfl
   nlinarith
end EdgeSublinearMWIS.Main.ProgramRepeat
end

-- Solutions.Sol_bounded_repeat
noncomputable section

open scoped Classical
set_option autoImplicit false
open EdgeSublinearMWIS.Main

theorem solution (U : Program) :
    ∃ M : Program, ∀ (v : ℕ → List Bool) (n T V : ℕ),
      (∀ i,i< n → Runs U (v i) (v (i+1)) T) →
      (∀ i,i≤ n → (v i).length≤ V) →
      Runs M (List.replicate n true++false::v 0) (v n) (10*(n+1)*(T+V+1)) := by
  exact ⟨ProgramRepeat.program U,ProgramRepeat.repeat_runs U⟩
end
