-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.polynomial_context_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T22:34:56.947493+00:00
-- url     : https://prove2.me/submissions/926fb0ac-ff4b-430c-8cdf-29bf1bedd718

import Mathlib
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_OAIThreeMachineSched02
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution
import Mathlib.Data.Nat.Digits.Lemmas

-- Solutions.WrapperRuntime
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

 theorem pipeline_time_bound (A C K₁ K₂ B D p r : ℕ) (hA : 0< A) (hC : 0< C) (hK₁ : 0< K₁) (hK₂ : 0< K₂) (hp : 0< p) :
     ∃ K : ℕ,0< K ∧ ∀ (L N T payload middle tcall tab post : ℕ),
       payload≤ L+B*(A*(L+N+1)^p) → tcall≤ T+6*payload+7 →
       tab=K₁*(A*(L+N+1)^p+tcall+L+1) → middle≤ L+D*tab →
       post=C*(middle+1)^r →
       K₂*(tab+post+L+1)≤ K*(T+L+N+1)^(p+p*r+1) := by
   let F := K₁*(A*(1+6*B)+15)
   refine ⟨K₂*(F+C*(2+D*F)^r+2),by dsimp [F]; positivity,?_⟩
   intro L N T payload middle tcall tab post hpay hcall hab hmid hpost
   let z := T+L+N+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hpre : (L+N+1)^p≤ z^p := Nat.pow_le_pow_left (by dsimp [z]; omega) p
   have hzp : z≤ z^p := by simpa only [pow_one] using Nat.pow_le_pow_right hz hp
   have hin : T+7*L+8≤15*z := by dsimp [z]; omega
   have hpay' : payload≤ L+B*(A*z^p) := hpay.trans (Nat.add_le_add_left (Nat.mul_le_mul_left B (Nat.mul_le_mul_left A hpre)) L)
   have habound : tab≤ F*z^p := by
     rw [hab]
     have hinner : A*(L+N+1)^p+tcall+L+1≤(A*(1+6*B)+15)*z^p := by
       have hh := Nat.mul_le_mul_left A hpre
       nlinarith only [hh,hcall,hpay',hin,hzp]
     exact (Nat.mul_le_mul_left K₁ hinner).trans_eq (by dsimp [F]; ring)
   have hL : L+1≤ z^p := (show L+1≤ z by dsimp [z]; omega).trans hzp
   have hinput : middle+1≤(2+D*F)*z^p := by
     have hmul := Nat.mul_le_mul_left D habound
     have hone : 1≤ z^p := one_le_pow₀ hz
     nlinarith only [hmid,hmul,hL,hone]
   have hpostbound : post≤ C*(2+D*F)^r*z^(p*r) := by
     rw [hpost]
     have hh := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput r)
     simpa only [mul_pow,← pow_mul,Nat.mul_assoc] using hh
   have hp1 : z^p≤ z^(p+p*r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr1 : z^(p*r)≤ z^(p+p*r+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 : z≤ z^(p+p*r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ p+p*r+1)
   have htab := habound.trans (Nat.mul_le_mul_left F hp1)
   have hpost' := hpostbound.trans (Nat.mul_le_mul_left (C*(2+D*F)^r) hr1)
   have hL' : L+1≤ z^(p+p*r+1) := (show L+1≤ z by dsimp [z]; omega).trans h1
   have hs : tab+post+L+1≤(F+C*(2+D*F)^r+2)*z^(p+p*r+1) := by
     nlinarith only [htab,hpost',hL']
   change _≤(K₂*(F+C*(2+D*F)^r+2))*z^(p+p*r+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left K₂ hs

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialTimeBounds
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.PolynomialTimeBounds
 theorem eval_monotone (p : Polynomial ℕ) : Monotone (fun x => p.eval x) := by
   intro x y hxy
   change p.eval x≤ p.eval y
   rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
   change (∑i∈p.support,p.coeff i*x^i)≤∑i∈p.support,p.coeff i*y^i
   apply Finset.sum_le_sum
   intro i hi
   exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hxy i)
end EdgeSublinearMWIS.Main.PolynomialTimeBounds
end

-- Solutions.RawBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def value : List Bool → ℕ
   | [] => 0
   | b::L => b.toNat+2*value L
 def increment : List Bool → List Bool
   | [] => [true]
   | false::L => true::L
   | true::L => false::increment L

 theorem increment_value (L : List Bool) : value (increment L)=value L+1 := by
  induction L with
  | nil => rfl
  | cons b L ih => cases b <;> simp [increment,value,ih] <;> omega

 theorem increment_length (L : List Bool) : (increment L).length≤ L.length+1 := by
  induction L with
  | nil => simp [increment]
  | cons b L ih => cases b <;> simp [increment] <;> omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdder
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open RawStack
abbrev State := List Bool × (List Bool × (Bool × List Bool))
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((a && b)||(a && c)||(b && c),(xor (xor a b) c)::s.2.2.2)))
 def word (A B : List Bool) : List Bool :=
   ((step^[A.length+B.length+1]) (A,(B,(false,[])))).2.2.2.reverse

 theorem value_head_tail (A : List Bool) : value A=(A.headD false).toNat+2*value A.tail := by
   cases A <;> rfl

 theorem value_append (A B : List Bool) : value (A++B)=value A+2^A.length*value B := by
   induction A with
   | nil => simp [value]
   | cons a A ih => simp [value,ih,pow_succ]; ring

 theorem full_adder (a b c : Bool) :
    (xor (xor a b) c).toNat+2*((a && b)||(a && c)||(b && c)).toNat=a.toNat+b.toNat+c.toNat := by
   cases a <;> cases b <;> cases c <;> decide

 theorem step_value (s : State) :
    value (step s).2.2.2.reverse+2^(step s).2.2.2.length*(value (step s).1+value (step s).2.1+(step s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   rcases s with ⟨A,B,c,R⟩
   have ha := value_head_tail A
   have hb := value_head_tail B
   have hf := full_adder (A.headD false) (B.headD false) c
   simp only [step,List.reverse_cons,value_append,List.length_reverse,List.length_cons,pow_succ,value,List.length_nil,Nat.mul_zero,Nat.add_zero]
   rw [ha,hb]
   have hfm := congrArg (fun z : ℕ => 2^R.length*z) hf
   nlinarith only [hfm]

 theorem iter_value (s : State) (t : ℕ) :
    value ((step^[t]) s).2.2.2.reverse+2^((step^[t]) s).2.2.2.length*(value ((step^[t]) s).1+value ((step^[t]) s).2.1+((step^[t]) s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_value ((step^[t]) s)).trans ih

 theorem iter_lists (s : State) (t : ℕ) :
    ((step^[t]) s).1=s.1.drop t ∧ ((step^[t]) s).2.1=s.2.1.drop t ∧
      ((step^[t]) s).2.2.2.length=s.2.2.2.length+t := by
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

 theorem word_value (A B : List Bool) : value (word A B)=value A+value B := by
   let t := A.length+B.length
   let s : State := (A,(B,(false,[])))
   have hlist := iter_lists s t
   have hA : ((step^[t]) s).1=[] := by rw [hlist.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hB : ((step^[t]) s).2.1=[] := by rw [hlist.2.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hzero : ((step^[t+1]) s).1=[] ∧ ((step^[t+1]) s).2.1=[] ∧ ((step^[t+1]) s).2.2.1=false := by
     rw [Function.iterate_succ_apply']
     simp [step,hA,hB]
   have hi := iter_value s (t+1)
   rw [hzero.1,hzero.2.1,hzero.2.2] at hi
   simpa only [word,s,t,value,List.reverse_nil,Bool.toNat_false,Nat.add_zero,Nat.mul_zero,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add] using hi

 theorem word_length (A B : List Bool) : (word A B).length=A.length+B.length+1 := by
   have hh := (iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [word,List.length_reverse,List.length_nil,Nat.zero_add] using hh

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryAdderRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 def headBit : Realizer (fun A : List Bool => A.headD false) where
   transform := Data.head
   charge := fun x => x.size+2
   routine := Routine.select true
   correct A := by cases A <;> rfl

 def tailBits : Realizer (fun A : List Bool => A.tail) where
   transform := Data.tail
   charge := fun x => x.size+2
   routine := Routine.select false
   correct A := by cases A <;> rfl

 def xorBits : Realizer (fun x : Bool×Bool => xor x.1 x.2) :=
   (Realizer.not.choose Realizer.id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 def bitA : Realizer (fun s : State => s.1.headD false) := Realizer.fst.comp headBit
 def bitB : Realizer (fun s : State => s.2.1.headD false) := (Realizer.snd.comp Realizer.fst).comp headBit
 def bitC : Realizer (fun s : State => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def revOutput : Realizer (fun s : State => s.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def sumBit : Realizer (fun s : State => xor (xor (s.1.headD false) (s.2.1.headD false)) s.2.2.1) :=
   (((bitA.pair bitB).comp xorBits).pair bitC).comp xorBits
 def carryBit : Realizer (fun s : State =>
     (s.1.headD false && s.2.1.headD false)||(s.1.headD false && s.2.2.1)||(s.2.1.headD false && s.2.2.1)) :=
   ((((bitA.pair bitB).comp Realizer.and).pair ((bitA.pair bitC).comp Realizer.and)).comp Realizer.or).pair
     ((bitB.pair bitC).comp Realizer.and) |>.comp Realizer.or

 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp tailBits).pair
       (carryBit.pair ((sumBit.pair revOutput).comp Realizer.cons)))).congr (fun _ => rfl)

 def wordLength : Realizer (fun A : List Bool => A.length) :=
   (Uniform.length (I := Unit) (α := fun _ => Bool)).specialize ()
 def lengthBound : Realizer (fun x : List Bool×List Bool => x.1.length+x.2.length+1) :=
   (((Realizer.fst.comp wordLength).pair (Realizer.snd.comp wordLength)).comp Realizer.add).comp Realizer.succ
 def initialState : Realizer (fun x : List Bool×List Bool => (x.1,(x.2,(false,([] : List Bool))))) :=
   Realizer.fst.pair (Realizer.snd.pair (Realizer.false.pair Realizer.nil))
 def wordRealizer : Realizer (fun x : List Bool×List Bool => word x.1 x.2) :=
   (((lengthBound.pair initialState).comp stepRealizer.iterate).comp revOutput).comp Realizer.reverse

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.NativeCompilerInterface
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.NativeCompiler
 theorem runs_mono (P : Program) (input output : List Bool) {t u : ℕ}
    (ht : Runs P input output t) (htu : t≤ u) : Runs P input output u := by
  obtain ⟨h⟩ := ht
  exact ⟨{h with steps_le_m := h.steps_le_m.trans htu}⟩
end EdgeSublinearMWIS.Main.NativeCompiler
end

-- Solutions.RealizerLinear
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def Linear {f : α → β} (R : Realizer f) : Prop :=
   ∃ C : ℕ,0< C ∧ ∀ x,R.time x ≤ C*(volume x+1) ∧ volume (f x) ≤ C*(volume x+1)

 theorem linear_of {f : α → β} (R : Realizer f) (C : ℕ) (hC : 0< C)
    (ht : ∀x,R.time x≤ C*(volume x+1)) (hv : ∀x,volume (f x)≤ C*(volume x+1)) : Linear R :=
   ⟨C,hC,fun x => ⟨ht x,hv x⟩⟩

 theorem linear_comp {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.comp S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨C+(D+10)*(C+1),by positivity,?_⟩
   intro x
   have h1 := hR x
   have h2 := hS (f x)
   have hV : volume (f x)+1 ≤ (C+1)*(volume x+1) := by nlinarith
   have htime := (h2.1).trans (Nat.mul_le_mul_left D hV)
   have hout := (h2.2).trans (Nat.mul_le_mul_left D hV)
   have hcopy := Nat.mul_le_mul_left 10 hV
   constructor
   · rw [Realizer.time_comp]
     nlinarith
   · change volume (g (f x))≤ _
     nlinarith

 theorem linear_pair {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.pair S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),by positivity,?_⟩
   intro x
   have h1 := hR x
   have h2 := hS x
   constructor
   · rw [Realizer.time_pair]
     nlinarith
   · simp only [volume_pair]
     nlinarith

 theorem linear_fst : Linear (Realizer.fst : Realizer (Prod.fst : α×β → α)) := by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_snd : Linear (Realizer.snd : Realizer (Prod.snd : α×β → β)) := by
   refine linear_of _ 3 (by omega) (fun x => by simp; omega) ?_
   rintro ⟨a,b⟩
   simp only [volume_pair]
   omega

 theorem linear_bool {f : α → Bool} (R : Realizer f) (C : ℕ) (ht : ∀x,R.time x≤ C*(volume x+1)) : Linear R := by
   refine linear_of R (C+3) (by omega) ?_ ?_
   · intro x; have hh := ht x; nlinarith
   · intro x; have hh := volume_bool (f x); nlinarith

 theorem linear_and : Linear Realizer.and := linear_bool _ 10000 (fun x =>
   (Realizer.time_and_le x).trans (by nlinarith))
 theorem linear_or : Linear Realizer.or := linear_bool _ 10000 (fun x =>
   (Realizer.time_or_le x).trans (by nlinarith))
 theorem linear_not : Linear Realizer.not := linear_bool _ 10000 (fun x =>
   (Realizer.time_not_le x).trans (by nlinarith))

theorem linear_finite [Fintype α] {f : α → β} (R : Realizer f) : Linear R := by
   let C := (∑ x : α, (R.time x+volume (f x)))+1
   refine ⟨C,by dsimp [C]; omega,?_⟩
   intro x
   have hx := Finset.single_le_sum (fun z (_ : z∈(Finset.univ : Finset α)) => Nat.zero_le (R.time z+volume (f z))) (Finset.mem_univ x)
   have hC : C≤ C*(volume x+1) := by nlinarith
   constructor <;> dsimp [C] at * <;> omega

 theorem linear_cons : Linear (Realizer.cons : Realizer (fun x : α×List α => x.1::x.2)) := by
   refine linear_of _ 3 (by omega) ?_ ?_
   · intro x
     change volume x+2≤3*(volume x+1)
     omega
   · rintro ⟨a,L⟩
     simp only [volume_cons,volume_pair]
     omega

 theorem linear_id : Linear (Realizer.id : Realizer (id : α → α)) :=
   linear_of _ 3 (by omega) (fun x => by change volume x+2≤ _; omega) (fun x => by change volume x≤3*(volume x+1); omega)

 theorem linear_choose {f g : α → β} {R : Realizer f} {S : Realizer g}
    (hR : Linear R) (hS : Linear S) : Linear (R.choose S) := by
   obtain ⟨C,hC,hR⟩ := hR
   obtain ⟨D,hD,hS⟩ := hS
   refine ⟨200*(C+D+1),by positivity,?_⟩
   rintro ⟨b,x⟩
   have hp : volume x+1≤ volume (b,x)+1 := by simp only [volume_pair]; omega
   have h1 := hR x
   have h2 := hS x
   have hc := Nat.mul_le_mul_left C hp
   have hd := Nat.mul_le_mul_left D hp
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd,Function.comp_apply]
     nlinarith
   · change volume (if b then f x else g x)≤ _
     split_ifs <;> nlinarith

 theorem linear_congr {f f' : α → β} (R : Realizer f) (hf : ∀x,f x=f' x) (hR : Linear R) : Linear (R.congr hf) := by
   obtain ⟨C,hC,hR⟩ := hR
   refine ⟨C,hC,?_⟩
   intro x
   have hh := hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AdderStepBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem headBit_linear : Linear headBit := by
   apply linear_bool headBit 3
   intro A
   change volume A+2≤3*(volume A+1)
   omega

 theorem tailBits_linear : Linear tailBits := by
   refine linear_of tailBits 3 (by omega) ?_ ?_
   · intro A
     change volume A+2≤3*(volume A+1)
     omega
   · intro A
     cases A with
     | nil => simp
     | cons a A => simp only [List.tail_cons,volume_cons]; omega

 theorem bitA_linear : Linear bitA := linear_comp linear_fst headBit_linear
 theorem bitB_linear : Linear bitB := linear_comp (linear_comp linear_snd linear_fst) headBit_linear
 theorem bitC_linear : Linear bitC := linear_comp (linear_comp linear_snd linear_snd) linear_fst
 theorem revOutput_linear : Linear revOutput := linear_comp (linear_comp linear_snd linear_snd) linear_snd
 theorem sumBit_linear : Linear sumBit :=
   linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) (linear_finite xorBits)) bitC_linear) (linear_finite xorBits)
 theorem carryBit_linear : Linear carryBit :=
   linear_comp (linear_pair (linear_comp (linear_pair (linear_comp (linear_pair bitA_linear bitB_linear) linear_and)
     (linear_comp (linear_pair bitA_linear bitC_linear) linear_and)) linear_or)
     (linear_comp (linear_pair bitB_linear bitC_linear) linear_and)) linear_or
 theorem step_linear : Linear stepRealizer := by
   have hh := linear_pair (linear_comp (linear_fst : Linear (Realizer.fst : Realizer (Prod.fst : State → List Bool))) tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) tailBits_linear)
       (linear_pair carryBit_linear (linear_comp (linear_pair sumBit_linear revOutput_linear) linear_cons)))
   exact hh

 theorem step_volume (s : State) : volume (step s)≤ volume s+6 := by
   rcases s with ⟨A,B,c,R⟩
   have hA : volume A.tail≤ volume A := by cases A <;> simp [volume_cons] <;> omega
   have hB : volume B.tail≤ volume B := by cases B <;> simp [volume_cons] <;> omega
   have hsum := volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry := volume_bool ((A.headD false && B.headD false)||(A.headD false && c)||(B.headD false && c))
   have hc : 1≤ volume c := volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.WordLengthBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 theorem volume_bits (A : List Bool) : volume A≤4*A.length+1 :=
   (volume_list_le A 3 (fun b _ => volume_bool b)).trans (by omega)

 theorem length_step_time (a : Bool) (b : ℕ) :
     ((Realizer.snd : Realizer (Prod.snd : Bool×ℕ → ℕ)).comp Realizer.succ).time (a,b)≤1000*(b+1) := by
   rw [Realizer.time_comp,Realizer.time_snd]
   have ht := Realizer.time_succ_le b
   simp only [volume_pair,volume_nat]
   have hb := volume_bool a
   nlinarith

 theorem length_fold_time (A : List Bool) (b : ℕ) :
     Realizer.foldTime ((Realizer.snd : Realizer (Prod.snd : Bool×ℕ → ℕ)).comp Realizer.succ) b A ≤
       10000*(A.length+1)*(volume A+2*b+2*A.length+1) := by
   induction A generalizing b with
   | nil => simp [Realizer.foldTime,volume_nil]; omega
   | cons a A ih =>
     have hh := ih (b+1)
     have ht := length_step_time a b
     have ha := volume_bool a
     have hp := volume_pos A
     change _+Realizer.foldTime _ (b+1) A+20*(volume (a::A)+volume b+volume (b+1)+1) ≤ _
     simp only [volume_cons,volume_nat,List.length_cons] at hh ⊢
     nlinarith

 theorem wordLength_time (A : List Bool) : wordLength.time A≤1000000*(A.length+1)^2 := by
   have hf := length_fold_time A 0
   have hv := volume_bits A
   change (Uniform.length (I:=Unit) (α:=fun _ => Bool)).time () A≤ _
   rw [Uniform.length,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,Uniform.time_id,Uniform.time_zero,Uniform.time_fold]
   simp only [Uniform.time_uniform,Function.comp_apply,volume_pair,volume_nat,Nat.mul_zero,Nat.add_zero] at hf ⊢
   have hfold : Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤
       10000*(A.length+1)*(volume A+2*A.length+1) := hf
   have hf' : Realizer.foldTime
       (((Uniform.snd (I:=Unit) (α:=fun _ => Bool) (β:=fun _ => ℕ)).comp (Realizer.succ.uniform Unit)).specialize ()) 0 A≤100000*(A.length+1)^2 := by
     calc
       _ ≤ 10000*(A.length+1)*(volume A+2*A.length+1) := hfold
       _ ≤ 10000*(A.length+1)*(6*A.length+2) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ _ := by nlinarith
   nlinarith

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem iter_volume (s : State) (t : ℕ) : volume ((step^[t]) s)≤ volume s+6*t := by
   induction t with
   | zero => simp
   | succ t ih => rw [Function.iterate_succ_apply']; have hh := step_volume ((step^[t]) s); omega

 theorem initial_volume (A B : List Bool) : volume (A,(B,(false,([] : List Bool))))≤4*(A.length+B.length)+7 := by
   have hA := volume_bits A
   have hB := volume_bits B
   simp only [volume_pair,volume_bool_false,volume_nil]
   omega

 theorem iterate_time : ∃ C : ℕ,0< C ∧ ∀ A B : List Bool,
     stepRealizer.iterate.time (A.length+B.length+1,(A,(B,(false,([] : List Bool)))))≤ C*(A.length+B.length+1)^2 := by
   obtain ⟨C,hC,hlinear⟩ := step_linear
   refine ⟨1000000*(C+1),by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   have hz : 1≤ z := by dsimp [z]; omega
   have hvol (j : ℕ) (hj : j≤ z) : volume ((step^[j]) s)≤14*z := by
     have hi := initial_volume A B
     have hv := iter_volume s j
     dsimp [s,z] at *
     omega
   have htime (j : ℕ) (hj : j< z) : stepRealizer.time ((step^[j]) s)≤ C*(14*z+1) :=
     ((hlinear _).1).trans (Nat.mul_le_mul_left C (by have hh := hvol j hj.le; omega))
   have hh := Realizer.time_iterate_le stepRealizer z s (C*(14*z+1)) (14*z) htime hvol
   calc
     _ ≤ 10000*(z+1)*(C*(14*z+1)+14*z+z+1) := hh
     _ ≤ 10000*(2*z)*((15*C+16)*z) := by
       apply Nat.mul_le_mul
       · exact Nat.mul_le_mul_left _ (by omega)
       · have hc := Nat.mul_le_mul_left C (show 14*z+1≤15*z by omega)
         nlinarith
     _ = (20000*(15*C+16))*z^2 := by ring
     _ ≤ (1000000*(C+1))*z^2 := Nat.mul_le_mul_right _ (by omega)

 theorem lengthBound_time (A B : List Bool) :
     lengthBound.time (A,B)≤1000000000*(A.length+B.length+1)^2 := by
   have hA := wordLength_time A
   have hB := wordLength_time B
   have hvA := volume_bits A
   have hvB := volume_bits B
   have ha := Realizer.time_add_le A.length B.length
   have hs := Realizer.time_succ_le (A.length+B.length)
   simp only [lengthBound,Realizer.time_comp,Realizer.time_pair,Realizer.time_fst,Realizer.time_snd,Function.comp_apply,volume_pair,volume_nat]
   have hLA : (A.length+1)^2≤(A.length+B.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
   have hLB : (B.length+1)^2≤(A.length+B.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
   have hA' := hA.trans (Nat.mul_le_mul_left 1000000 hLA)
   have hB' := hB.trans (Nat.mul_le_mul_left 1000000 hLB)
   nlinarith

 theorem initial_linear : Linear initialState := by
   have hfalse : Linear (Realizer.false : Realizer (fun _ : List Bool×List Bool => false)) := by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   have hnil : Linear (Realizer.nil : Realizer (fun _ : List Bool×List Bool => ([] : List Bool))) := by
     refine linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact linear_pair linear_fst (linear_pair linear_snd (linear_pair hfalse hnil))

 theorem reverse_time (A : List Bool) : (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time A≤200*(A.length+1)*(volume A+1) :=
   Uniform.time_reverse (I:=Unit) (α:=fun _ => Bool) () A

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderTotalRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem word_time : ∃ C : ℕ,0< C ∧ ∀ A B : List Bool,
     wordRealizer.time (A,B)≤ C*(A.length+B.length+1)^2 := by
   obtain ⟨C,hC,hiter⟩ := iterate_time
   obtain ⟨I,hI,hinit⟩ := initial_linear
   obtain ⟨O,hO,hout⟩ := revOutput_linear
   refine ⟨1000000000+C+5*I+15*O+20000,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   let t : State := (step^[z]) s
   have hz : 1≤ z := by dsimp [z]; omega
   have hzsq : z≤ z^2 := by nlinarith
   have hvA := volume_bits A
   have hvB := volume_bits B
   have hvx : volume (A,B)≤4*z := by simp only [volume_pair]; dsimp [z]; omega
   have hvs : volume s≤7*z := by have hh := initial_volume A B; dsimp [s,z] at *; omega
   have hvt : volume t≤14*z := by have hh := iter_volume s z; dsimp [t]; omega
   have hvr : volume t.2.2.2≤ volume t := by
     rcases t with ⟨T,U,c,R⟩
     simp only [volume_pair]
     omega
   have hlen : t.2.2.2.length=z := by
     have hh := (iter_lists s z).2.2
     simpa [s] using hh
   have hinit0 := (hinit (A,B)).1
   have hinit1 : initialState.time (A,B)≤5*I*z^2 := by
     calc
       _ ≤ I*(volume (A,B)+1) := hinit0
       _ ≤ I*(5*z) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ 5*I*z^2 := by nlinarith [Nat.mul_le_mul_left (5*I) hzsq]
   have hout0 := (hout t).1
   have hout1 : revOutput.time t≤15*O*z^2 := by
     calc
       _ ≤ O*(volume t+1) := hout0
       _ ≤ O*(15*z) := Nat.mul_le_mul_left _ (by omega)
       _ ≤ 15*O*z^2 := by nlinarith [Nat.mul_le_mul_left (15*O) hzsq]
   have hr := reverse_time t.2.2.2
   have hr1 : (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time t.2.2.2≤6000*z^2 := by
     calc
       _ ≤ 200*(z+1)*(volume t.2.2.2+1) := by simpa only [hlen] using hr
       _ ≤ 200*(2*z)*(15*z) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
       _ = 6000*z^2 := by ring
   have hiter1 : stepRealizer.iterate.time (z,s)≤ C*z^2 := hiter A B
   have hlen1 : lengthBound.time (A,B)≤1000000000*z^2 := lengthBound_time A B
   have hvolZ : volume z=2*z+1 := volume_nat z
   have hcopy0 : 20*(volume (A,B)+volume z+volume s+1)+10*(volume (z,s)+1)+10*(volume t+1)+10*(volume t.2.2.2+1)≤10000*z^2 := by
     simp only [volume_pair,hvolZ]
     omega
   have hrealtime : wordRealizer.time (A,B)=lengthBound.time (A,B)+initialState.time (A,B)+
       20*(volume (A,B)+volume z+volume s+1)+stepRealizer.iterate.time (z,s)+10*(volume (z,s)+1)+
       revOutput.time t+10*(volume t+1)+
       (Realizer.reverse : Realizer (fun A : List Bool => A.reverse)).time t.2.2.2+10*(volume t.2.2.2+1) := by
     dsimp only [wordRealizer,word]
     simp only [Realizer.time_comp,Realizer.time_pair,Function.comp_apply,volume_reverse]
     rfl
   rw [hrealtime]
   change _≤(1000000000+C+5*I+15*O+20000)*z^2
   nlinarith only [hinit1,hout1,hr1,hiter1,hlen1,hcopy0]

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrim
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def trim : List Bool → List Bool
   | [] => []
   | b::L => let T := trim L
             if T=[] then if b then [true] else [] else b::T

 theorem trim_value (L : List Bool) : value (trim L)=value L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · have hv : value L=0 := by rw [← ih,hT]; rfl
       cases b <;> simp [trim,hT,value,hv]
     · simp only [trim,hT,if_false,value,ih]

 theorem trim_length (L : List Bool) : (trim L).length≤ L.length := by
   induction L with
   | nil => simp [trim]
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp [trim,hT]
     · simp [trim,hT]; omega

 theorem value_lt (L : List Bool) : value L<2^L.length := by
   induction L with
   | nil => simp [value]
   | cons b L ih => cases b <;> simp [value,pow_succ] <;> omega

 theorem trim_lower (L : List Bool) (hL : trim L≠[]) : 2^((trim L).length-1)≤ value (trim L) := by
   induction L with
   | nil => exact False.elim (hL rfl)
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp_all [trim,value]
     · have hh := ih hT
       have hlen : 0<(trim L).length := by
         cases he : trim L with
         | nil => exact False.elim (hT he)
         | cons a T => simp
       have hp : 2^((trim L).length)=2*2^((trim L).length-1) := by
         rw [← Nat.pow_succ']
         congr 1
         omega
       simp only [trim,hT,if_false,List.length_cons,Nat.add_sub_cancel,value]
       rw [hp]
       omega

 theorem trim_length_of_lt (L : List Bool) (B : ℕ) (hB : value L<2^B) : (trim L).length≤ B := by
   by_cases hL : trim L=[]
   · simp [hL]
   · have hp := trim_lower L hL
     rw [trim_value] at hp
     have hh : (trim L).length-1< B := by
       by_contra hn
       have hpow := Nat.pow_le_pow_right (by omega : 1≤2) (by omega : B≤(trim L).length-1)
       omega
     omega

 def trimStep (x : Bool×List Bool) : List Bool :=
   if x.2=[] then if x.1 then [true] else [] else x.1::x.2

 theorem trim_fold (L : List Bool) : L.reverse.foldl (fun T b => trimStep (b,T)) []=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     rw [List.reverse_cons,List.foldl_append]
     change trimStep (b,L.reverse.foldl (fun T b => trimStep (b,T)) [])=trim (b::L)
     rw [ih]
     rfl

 theorem trim_idem (L : List Bool) : trim (trim L)=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp [trim,hT]
     · simp only [trim,hT,if_false,ih]


end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryTrimRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonemptyBits : Realizer (fun L : List Bool => !L.isEmpty) :=
   (Uniform.isCons (I:=Unit) (α:=fun _ => Bool)).specialize ()
 def keepBit : Realizer (fun x : Bool×List Bool => x.1 || !x.2.isEmpty) :=
   (Realizer.fst.pair (Realizer.snd.comp nonemptyBits)).comp Realizer.or
 def trimStepRealizer : Realizer trimStep :=
   ((keepBit.pair Realizer.id).comp (Realizer.cons.choose Realizer.nil)).congr (fun x => by
     rcases x with ⟨b,L⟩
     cases L with
     | nil => cases b <;> rfl
     | cons a L => cases b <;> rfl)
 def trimRealizer : Realizer trim :=
   (((Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).pair Realizer.nil).comp trimStepRealizer.fold).congr (fun L => trim_fold L)

 theorem nonempty_linear : Linear nonemptyBits := by
   apply linear_bool nonemptyBits 10000
   intro L
   exact Realizer.time_test_le (fun L : List Bool => !L.isEmpty) (by intro L; cases L <;> rfl) L

 theorem trimStep_linear : Linear trimStepRealizer := by
   have hkeep : Linear keepBit := linear_comp (linear_pair linear_fst (linear_comp linear_snd nonempty_linear)) linear_or
   have hcons : Linear (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)) := linear_cons
   have hnil : Linear (Realizer.nil : Realizer (fun _ : Bool×List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun x => by change 2≤ _; omega) (fun x => by simp; omega)
   unfold trimStepRealizer
   apply linear_congr
   exact linear_comp (linear_pair hkeep linear_id) (linear_choose hcons hnil)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.TrimRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem trimStep_volume (b : Bool) (T : List Bool) : volume (trimStep (b,T))≤ volume T+4 := by
   cases T with
   | nil => cases b <;> decide
   | cons a T => simp only [trimStep,List.cons_ne_nil,if_false,volume_cons]; have hb := volume_bool b; omega

 theorem trim_fold_time : ∃ C : ℕ,0< C ∧ ∀ (L T : List Bool),
     Realizer.foldTime trimStepRealizer T L≤ C*(L.length+1)*(volume L+volume T+4*L.length+1) := by
   obtain ⟨C,hC,hlin⟩ := trimStep_linear
   let K := 100*(C+1)
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
     let V := volume (b::L)+volume T+4*(b::L).length+1
     have hVpos : 1≤ V := by dsimp [V]; omega
     have hL := volume_pos L
     have hT := volume_pos T
     have hb := volume_bool b
     have hstep := trimStep_volume b T
     have hrec := ih (trimStep (b,T))
     have hsub : volume L+volume (trimStep (b,T))+4*L.length+1≤ V := by
       dsimp [V]
       simp only [volume_cons,List.length_cons]
       omega
     have hrec' : Realizer.foldTime trimStepRealizer (trimStep (b,T)) L≤ K*(L.length+1)*V :=
       hrec.trans (Nat.mul_le_mul_left _ hsub)
     have harg : volume (b,T)+1≤ V := by dsimp [V]; simp only [volume_cons,volume_pair,List.length_cons]; omega
     have htime : trimStepRealizer.time (b,T)≤ C*V :=
       ((hlin (b,T)).1).trans (Nat.mul_le_mul_left _ harg)
     have hcopy : 20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤80*V := by
       have hh1 : volume (b::L)≤ V := by dsimp [V]; omega
       have hh2 : volume T≤ V := by dsimp [V]; omega
       have hh3 : volume (trimStep (b,T))≤ V := by dsimp [V]; omega
       omega
     have hcoeff : (C+80)*V≤ K*V := Nat.mul_le_mul_right _ (by dsimp [K]; omega)
     change trimStepRealizer.time (b,T)+Realizer.foldTime trimStepRealizer (trimStep (b,T)) L+
       20*(volume (b::L)+volume T+volume (trimStep (b,T))+1)≤ K*((b::L).length+1)*V
     simp only [List.length_cons]
     nlinarith only [htime,hrec',hcopy,hcoeff]

 theorem trim_time : ∃ C : ℕ,0< C ∧ ∀ L : List Bool,trimRealizer.time L≤ C*(L.length+1)^2 := by
   obtain ⟨C,hC,hfold⟩ := trim_fold_time
   refine ⟨10000*(C+1),by positivity,?_⟩
   intro L
   have hv := BinaryAdder.volume_bits L
   have hr := BinaryAdder.reverse_time L
   have hf := hfold L.reverse []
   simp only [List.length_reverse,volume_reverse,volume_nil] at hf
   have hf' : Realizer.foldTime trimStepRealizer [] L.reverse≤8*C*(L.length+1)^2 := by
     calc
       _ ≤ C*(L.length+1)*(volume L+1+4*L.length+1) := hf
       _ ≤ C*(L.length+1)*(8*(L.length+1)) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by ring
   have hr' : (Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).time L≤1000*(L.length+1)^2 := by
     calc
       _ ≤ 200*(L.length+1)*(volume L+1) := hr
       _ ≤ 200*(L.length+1)*(5*(L.length+1)) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by ring
   have hnil : (Realizer.nil : Realizer (fun _ : List Bool => ([] : List Bool))).time L=2 := rfl
   have he : trimRealizer.time L=(Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).time L+2+
       20*(volume L+volume L+1+1)+(2*volume (L.reverse,([] : List Bool))+6+Realizer.foldTime trimStepRealizer [] L.reverse)+
       10*(volume (L.reverse,([] : List Bool))+1) := by
     simp only [trimRealizer,Realizer.time_congr,Realizer.time_comp,Realizer.time_pair,hnil,volume_nil,Realizer.time_fold,Function.comp_apply,volume_reverse]
   rw [he]
   simp only [volume_pair,volume_reverse,volume_nil]
   nlinarith only [hr',hf',hv]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryMultiply
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def multiplyStep (x : Bool×(List Bool×List Bool)) : List Bool×List Bool :=
   (false::x.2.1,if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2)
 def multiply (A B : List Bool) : List Bool :=
   trim (B.foldl (fun s b => multiplyStep (b,s)) (A,[])).2

 theorem multiply_fold_value (A B S : List Bool) :
     value (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=value S+value A*value B := by
   induction B generalizing A S with
   | nil => simp [value]
   | cons b B ih =>
     rw [List.foldl_cons]
     change value (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).2=_
     rw [ih]
     cases b <;> simp only [Bool.false_eq_true,if_false,if_true,trim_value,BinaryAdder.word_value,value,Bool.toNat_false,Bool.toNat_true] <;> ring

 theorem multiply_value (A B : List Bool) : value (multiply A B)=value A*value B := by
   rw [multiply,trim_value,multiply_fold_value]
   simp [value]

 theorem product_lt (A B : List Bool) : value A*value B<2^(A.length+B.length) := by
   calc
     _ ≤ value A*2^B.length := Nat.mul_le_mul_left _ (value_lt B).le
     _ < 2^A.length*2^B.length := Nat.mul_lt_mul_of_pos_right (value_lt A) (by positivity)
     _ = _ := (pow_add _ _ _).symm

 theorem multiply_length (A B : List Bool) : (multiply A B).length≤ A.length+B.length := by
   apply trim_length_of_lt
   rw [multiply_fold_value]
   simpa only [value,Nat.zero_add] using product_lt A B

 theorem multiply_first_length (A B S : List Bool) :
     (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).1.length=A.length+B.length := by
   induction B generalizing A S with
   | nil => simp
   | cons b B ih =>
     rw [List.foldl_cons]
     change (B.foldl _ (false::A,if b then trim (BinaryAdder.word S A) else S)).1.length=_
     rw [ih]
     simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

 theorem multiply_canonical (A B S : List Bool) (hS : trim S=S) :
     trim (B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2=(B.foldl (fun s b => multiplyStep (b,s)) (A,S)).2 := by
   induction B generalizing A S with
   | nil => exact hS
   | cons b B ih =>
     rw [List.foldl_cons]
     apply ih
     cases b
     · exact hS
     · exact trim_idem _

 theorem multiply_prefix_length (A B : List Bool) (j : ℕ) :
     ((B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])).2.length≤ A.length+B.length := by
   let P := (B.take j).foldl (fun s b => multiplyStep (b,s)) (A,[])
   have hc : trim P.2=P.2 := multiply_canonical A (B.take j) [] rfl
   rw [← hc]
   apply trim_length_of_lt
   have hfull := multiply_fold_value A B []
   rw [← List.take_append_drop j B,List.foldl_append] at hfull
   have hpartial := multiply_fold_value P.1 (B.drop j) P.2
   change value ((B.drop j).foldl _ P).2=_ at hfull
   rw [hpartial,List.take_append_drop] at hfull
   have hle : value P.2≤ value A*value B := by simpa only [value,Nat.zero_add] using (show value P.2≤ value []+value A*value B by omega)
   exact hle.trans_lt (product_lt A B)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryMultiplyRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def addThenTrim : Realizer (fun x : List Bool×List Bool => trim (BinaryAdder.word x.2 x.1)) :=
   ((Realizer.snd.pair Realizer.fst).comp BinaryAdder.wordRealizer).comp trimRealizer
 def selectedSum : Realizer (fun x : Bool×(List Bool×List Bool) =>
     if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2) :=
   addThenTrim.choose Realizer.snd
 def shiftedWord : Realizer (fun x : Bool×(List Bool×List Bool) => false::x.2.1) :=
   (Realizer.false.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons
 def multiplyStepRealizer : Realizer multiplyStep :=
   (shiftedWord.pair selectedSum).congr (fun _ => rfl)
 def multiplyInitial : Realizer (fun x : List Bool×List Bool => (x.2,(x.1,([] : List Bool)))) :=
   Realizer.snd.pair (Realizer.fst.pair Realizer.nil)
 def multiplyRealizer : Realizer (fun x : List Bool×List Bool => multiply x.1 x.2) :=
   (((multiplyInitial.comp multiplyStepRealizer.fold).comp Realizer.snd).comp trimRealizer).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RealizerPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def PolyBound {f : α → β} (R : Realizer f) : Prop :=
   ∃ C q : ℕ,0< C ∧ ∀ x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q

 theorem linear_polynomial {f : α → β} {R : Realizer f} (hR : Linear R) : PolyBound R := by
   obtain ⟨C,hC,hR⟩ := hR
   exact ⟨C,1,hC,by simpa only [pow_one] using hR⟩

 theorem polynomial_comp {f : α → β} {g : β → γ} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.comp S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨C+D*(C+1)^r+10*(C+1),q+q*r,by positivity,?_⟩
   intro x
   let z := volume x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hq : 1≤ z^q := one_le_pow₀ hz
   have h1 := hR x
   change R.time x≤ C*z^q ∧ volume (f x)≤ C*z^q at h1
   have h2 := hS (f x)
   have hV : volume (f x)+1≤(C+1)*z^q := by change volume (f x)+1≤ _; nlinarith
   have hVp := Nat.pow_le_pow_left hV r
   have hPow : ((C+1)*z^q)^r=(C+1)^r*z^(q*r) := by rw [mul_pow,pow_mul]
   rw [hPow] at hVp
   have hqr : z^q≤ z^(q+q*r) := Nat.pow_le_pow_right hz (by omega)
   have hrr : z^(q*r)≤ z^(q+q*r) := Nat.pow_le_pow_right hz (by omega)
   have htime1 := h1.1.trans (Nat.mul_le_mul_left C hqr)
   have htime2 := h2.1.trans (Nat.mul_le_mul_left D hVp)
   have htime2 := htime2.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   have hcopy := (Nat.mul_le_mul_left 10 hV).trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (10*(C+1)) hqr)
   have hout := h2.2.trans (Nat.mul_le_mul_left D hVp)
   have hout := hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*(C+1)^r) hrr)
   constructor
   · rw [Realizer.time_comp]
     change _≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     nlinarith only [htime1,htime2,hcopy]
   · change volume (g (f x))≤(C+D*(C+1)^r+10*(C+1))*z^(q+q*r)
     exact hout.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (z^(q+q*r)) (show D*(C+1)^r≤ C+D*(C+1)^r+10*(C+1) by omega))

 theorem polynomial_pair {f : α → β} {g : α → γ} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.pair S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨100*(C+D+1),q+r+1,by positivity,?_⟩
   intro x
   let z := volume x+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : z≤ z^(q+r+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1)
   have hq : z^q≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have hr : z^r≤ z^(q+r+1) := Nat.pow_le_pow_right hz (by omega)
   have h1 := hR x
   have h2 := hS x
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1 := h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2 := h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · rw [Realizer.time_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     change z≤ z^(q+r+1) at hp
     have hsmall : R.time x+S.time x+20*(volume x+volume (f x)+volume (g x)+1)≤(21*C+21*D+20)*z^(q+r+1) := by
       have hp' : volume x+1≤ z^(q+r+1) := hp
       nlinarith only [ht1,ht2,hv1,hv2,hp']
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · simp only [volume_pair]
     change _≤100*(C+D+1)*z^(q+r+1)
     have hp1 : 1≤ z^(q+r+1) := one_le_pow₀ hz
     have hsmall : volume (f x)+volume (g x)+1≤(C+D+1)*z^(q+r+1) := by nlinarith only [hv1,hv2,hp1]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))

 theorem polynomial_congr {f f' : α → β} (R : Realizer f) (hf : ∀x,f x=f' x)
    (hR : PolyBound R) : PolyBound (R.congr hf) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨C,q,hC,?_⟩
   intro x
   have hh := hR x
   refine ⟨?_,?_⟩
   · simpa only [Realizer.time_congr] using hh.1
   · rw [← hf x]
     exact hh.2

 theorem polynomial_choose {f g : α → β} {R : Realizer f} {S : Realizer g}
    (hR : PolyBound R) (hS : PolyBound S) : PolyBound (R.choose S) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨D,r,hD,hS⟩ := hS
   refine ⟨200*(C+D+1),q+r+1,by positivity,?_⟩
   rintro ⟨b,x⟩
   let z := volume (b,x)+1
   let p := z^(q+r+1)
   have hz : 1≤ z := by dsimp [z]; omega
   have hx : volume x+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hq : (volume x+1)^q≤ p := (Nat.pow_le_pow_left hx q).trans (Nat.pow_le_pow_right hz (by omega))
   have hr : (volume x+1)^r≤ p := (Nat.pow_le_pow_left hx r).trans (Nat.pow_le_pow_right hz (by omega))
   have hp : z≤ p := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+r+1)
   have h1 := hR x
   have h2 := hS x
   have ht1 := h1.1.trans (Nat.mul_le_mul_left C hq)
   have ht2 := h2.1.trans (Nat.mul_le_mul_left D hr)
   have hv1 := h1.2.trans (Nat.mul_le_mul_left C hq)
   have hv2 := h2.2.trans (Nat.mul_le_mul_left D hr)
   constructor
   · simp only [Realizer.time_choose,Realizer.time_comp,Realizer.time_snd]
     change _≤200*(C+D+1)*p
     have hsmall : volume (b,x)+2+R.time x+10*(volume x+1)+(volume (b,x)+2+S.time x+10*(volume x+1))+
         30*(volume (b,x)+volume (f x)+volume (g x)+1)≤(31*C+31*D+100)*p := by
       dsimp [z] at hx hp
       nlinarith only [ht1,ht2,hv1,hv2,hx,hp]
     exact hsmall.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (if b then f x else g x)≤200*(C+D+1)*p
     split_ifs
     · exact hv1.trans (Nat.mul_le_mul_right _ (by omega))
     · exact hv2.trans (Nat.mul_le_mul_right _ (by omega))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryArithmeticPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem bits_length_volume (L : List Bool) : L.length≤ volume L := by
   induction L with
   | nil => simp
   | cons b L ih => simp only [List.length_cons,volume_cons]; omega

 theorem word_polynomial : PolyBound BinaryAdder.wordRealizer := by
   obtain ⟨C,hC,hT⟩ := BinaryAdder.word_time
   refine ⟨C+5,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have ha := bits_length_volume A
   have hb := bits_length_volume B
   have hV : A.length+B.length+1≤ volume (A,B)+1 := by simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hV 2
   have ht := (hT A B).trans (Nat.mul_le_mul_left C hp)
   have hv := BinaryAdder.volume_bits (BinaryAdder.word A B)
   rw [BinaryAdder.word_length] at hv
   have hz : 1≤ volume (A,B)+1 := by omega
   have hsq : volume (A,B)+1≤(volume (A,B)+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (BinaryAdder.word A B)≤ _
     have hv' : volume (BinaryAdder.word A B)≤5*(volume (A,B)+1)^2 := by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem trim_polynomial : PolyBound trimRealizer := by
   obtain ⟨C,hC,hT⟩ := trim_time
   refine ⟨C+5,2,by omega,?_⟩
   intro L
   have hlen := bits_length_volume L
   have hp := Nat.pow_le_pow_left (show L.length+1≤ volume L+1 by omega) 2
   have ht := (hT L).trans (Nat.mul_le_mul_left C hp)
   have hv := BinaryAdder.volume_bits (trim L)
   have htrim := trim_length L
   have hz : 1≤ volume L+1 := by omega
   have hsq : volume L+1≤(volume L+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · have hv' : volume (trim L)≤5*(volume L+1)^2 := by nlinarith
     exact hv'.trans (Nat.mul_le_mul_right _ (by omega))

 theorem addThenTrim_polynomial : PolyBound addThenTrim :=
   polynomial_comp (polynomial_comp (polynomial_pair (linear_polynomial linear_snd) (linear_polynomial linear_fst)) word_polynomial) trim_polynomial
 theorem selectedSum_polynomial : PolyBound selectedSum :=
   polynomial_choose addThenTrim_polynomial (linear_polynomial linear_snd)
 theorem shiftedWord_polynomial : PolyBound shiftedWord := by
   have hf : Linear (Realizer.false : Realizer (fun _ : Bool×(List Bool×List Bool) => false)) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact linear_polynomial (linear_comp (linear_pair hf (linear_comp linear_snd linear_fst)) linear_cons)
 theorem multiplyStep_polynomial : PolyBound multiplyStepRealizer := by
   unfold multiplyStepRealizer
   apply polynomial_congr
   exact polynomial_pair shiftedWord_polynomial selectedSum_polynomial

 theorem reverse_polynomial : PolyBound (Realizer.reverse : Realizer (fun L : List Bool => L.reverse)) := by
   refine ⟨201,2,by omega,?_⟩
   intro L
   have hlen := bits_length_volume L
   have hT := BinaryAdder.reverse_time L
   have hmul := Nat.mul_le_mul_right (200*(volume L+1)) (show L.length+1≤ volume L+1 by omega)
   have hv : volume L≤(volume L+1)^2 := by nlinarith
   constructor
   · have hh : 200*(L.length+1)*(volume L+1)≤200*(volume L+1)^2 := by nlinarith only [hmul]
     exact (hT.trans hh).trans (Nat.mul_le_mul_right _ (by omega))
   · rw [volume_reverse]
     exact hv.trans (Nat.le_mul_of_pos_left _ (by omega))

 theorem lengthBound_polynomial : PolyBound BinaryAdder.lengthBound := by
   refine ⟨1000000001,2,by omega,?_⟩
   rintro ⟨A,B⟩
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hbase : A.length+B.length+1≤ volume (A,B)+1 := by simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have ht := (BinaryAdder.lengthBound_time A B).trans (Nat.mul_le_mul_left 1000000000 hp)
   have hz : volume (A,B)+1≤(volume (A,B)+1)^2 := by nlinarith
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume (A.length+B.length+1)≤ _
     rw [volume_nat]
     nlinarith

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialMap
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 theorem length_volume (L : List α) : L.length≤ volume L := by
   induction L with
   | nil => simp
   | cons a L ih => simp only [List.length_cons,volume_cons]; omega
 def mapEnvironment {f : α×γ → β} (R : Realizer f) :
     Realizer (fun x : List α×γ => x.1.map (fun a => f (a,x.2))) := (R.uniform Unit).map.specialize ()
 theorem mapEnvironment_time {f : α×γ → β} (R : Realizer f) (x : List α×γ) :
     (mapEnvironment R).time x=(R.uniform Unit).map.time () x := rfl

 theorem polynomial_mapEnvironment {f : α×γ → β} {R : Realizer f} (hR : PolyBound R) : PolyBound (mapEnvironment R) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   refine ⟨100000*(C+10),q+2,by positivity,?_⟩
   rintro ⟨xs,e⟩
   let z := volume (xs,e)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hlen := length_volume xs
   have hlenz : xs.length+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hvolz : volume xs+volume e+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   have hp1 : 1≤ z^(q+1) := one_le_pow₀ hz
   have hbounds (a : α) (ha : a∈xs) : R.time (a,e)≤ C*z^q ∧ volume (f (a,e))≤ C*z^q := by
     have hv := volume_mem_le ha
     have hbase : volume (a,e)+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
     have hh := hR (a,e)
     exact ⟨hh.1.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q)),
       hh.2.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))⟩
   have hout : volume (xs.map (fun a => f (a,e)))≤(C+2)*z^(q+1) := by
     have hh := volume_list_le (xs.map (fun a => f (a,e))) (C*z^q) (by
       intro b hb
       obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
       exact (hbounds a ha).2)
     rw [List.length_map] at hh
     have hm := Nat.mul_le_mul (show xs.length≤ z by omega) (show C*z^q+1≤ C*z^q+1 by rfl)
     have he : z*(C*z^q+1)=C*z^(q+1)+z := by rw [pow_succ]; ring
     rw [he] at hm
     nlinarith only [hh,hm,hze,hp1]
   have ht := Uniform.time_map (R.uniform Unit) () xs e (C*z^q) (fun a ha => (hbounds a ha).1)
   rw [Nat.mul_assoc] at ht
   have hinner : C*z^q+volume xs+volume e+volume (xs.map (fun a => f (a,e)))+1≤(2*C+6)*z^(q+1) := by
     have htime := Nat.mul_le_mul_left C hq
     nlinarith only [htime,hout,hvolz,hze,hp1]
   have hmul := Nat.mul_le_mul_left 30000 (Nat.mul_le_mul hlenz hinner)
   have he : 30000*(z*((2*C+6)*z^(q+1)))=30000*(2*C+6)*z^(q+2) := by rw [pow_succ]; ring
   rw [he] at hmul
   have hcoef : 30000*(2*C+6)≤100000*(C+10) := by omega
   constructor
   · rw [mapEnvironment_time]
     change (R.uniform Unit).map.time () (xs,e)≤100000*(C+10)*z^(q+2)
     have hh : (R.uniform Unit).map.time () (xs,e)≤30000*(2*C+6)*z^(q+2) := ht.trans hmul
     exact hh.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (xs.map (fun a => f (a,e)))≤ _
     have hp := Nat.pow_le_pow_right hz (by omega : q+1≤ q+2)
     exact hout.trans ((Nat.mul_le_mul_left (C+2) hp).trans (Nat.mul_le_mul_right _ (by omega)))

 def mapList {f : α → β} (R : Realizer f) : Realizer (fun xs : List α => xs.map f) :=
   ((Realizer.id.pair Realizer.unit).comp (mapEnvironment (Realizer.fst.comp R))).congr (fun _ => rfl)
 theorem polynomial_mapList {f : α → β} {R : Realizer f} (hR : PolyBound R) : PolyBound (mapList R) := by
   have hu : Linear (Realizer.unit : Realizer (fun _ : List α => ())) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold mapList
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hu))
     (polynomial_mapEnvironment (polynomial_comp (linear_polynomial linear_fst) hR))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.PolynomialProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem realizer_poly_program {f : List Bool → List Bool} (R : Realizer f) (hR : PolyBound R) :
     ∃ (P : EdgeSublinearMWIS.Main.Program) (K q : ℕ),0< K ∧ 0< q ∧
       ∀ input, EdgeSublinearMWIS.Main.Runs P input (f input) (K*(input.length+1)^q) := by
   obtain ⟨C,q,hC,hR⟩ := hR
   obtain ⟨P,F,hF,hRuns⟩ := EdgeSublinearMWIS.Main.realizer_native_program f R
   refine ⟨P,F*(2*C*5^q+2),q+1,by positivity,by omega,?_⟩
   intro input
   have hRun := hRuns input
   apply NativeCompiler.runs_mono _ _ _ hRun
   let z := input.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hv := EdgeSublinearMWIS.Main.BinaryAdder.volume_bits input
   have hi : volume input+1≤5*z := by dsimp [z]; omega
   have hp := Nat.pow_le_pow_left hi q
   rw [mul_pow] at hp
   have hq : z^q≤ z^(q+1) := Nat.pow_le_pow_right hz (by omega)
   have hqp : (volume input+1)^q≤5^q*z^(q+1) := hp.trans (Nat.mul_le_mul_left _ hq)
   have ht := ((hR input).1).trans (Nat.mul_le_mul_left C hqp)
   have ho := ((hR input).2).trans (Nat.mul_le_mul_left C hqp)
   have hl := EdgeSublinearMWIS.Main.RawStack.bits_length_volume (f input)
   have hze : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   change input.length+1≤ z^(q+1) at hze
   have hs : R.time input+input.length+(f input).length+1≤(2*C*5^q+2)*z^(q+1) := by
     nlinarith only [ht,ho,hl,hze]
   change F*(R.time input+input.length+(f input).length+1)≤ F*(2*C*5^q+2)*z^(q+1)
   simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left F hs

end EdgeSublinearMWIS.Main.TreeToTM2
end

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
     ∃ t,t≤ T ∧ run P.machine.tm.m (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
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

-- Solutions.ProgramCompositionBound
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

 theorem spaceRun_eq (tm : Turing.FinTM2) (c : tm.Cfg) (t : ℕ) :
     StackSpace.run tm c t=RawStack.run tm.m c t := by
   induction t with
   | zero => rfl
   | succ t ih => simp only [StackSpace.run,RawStack.run,ih]; rfl
 theorem output_length (P : Program) (input output : List Bool) (T : ℕ) (h : Runs P input output T) :
     output.length≤ input.length+StackSpace.bound P.machine.tm*T := by
   obtain ⟨t,ht,hr⟩ := outputs_run P input output T h
   have hr' : StackSpace.run P.machine.tm (Turing.initList P.machine.tm (input.map P.machine.inputAlphabet.symm)) t=
     some (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)) := by rw [spaceRun_eq]; exact hr
   have hs := StackSpace.input_run_space P.machine.tm (input.map P.machine.inputAlphabet.symm) t _ hr'
   have hl := StackSpace.stack_length_le_space (Turing.haltList P.machine.tm (output.map P.machine.outputAlphabet.symm)).stk P.machine.tm.k₁
   simp only [haltList_store,onlyStack_self,List.length_map] at hl
   rw [haltList_store] at hs
   simp only [List.length_map] at hs
   have hmul := Nat.mul_le_mul_left (StackSpace.bound P.machine.tm) ht
   omega

 theorem sequence_runs_linear (P Q : Program) :
     ∃ K : ℕ,0< K ∧ ∀ (input middle output : List Bool) (T U : ℕ),
       Runs P input middle T → Runs Q middle output U →
       Runs (sequence P Q) input output (K*(T+U+input.length+1)) := by
   refine ⟨2*StackSpace.bound P.machine.tm+4,by omega,?_⟩
   intro input middle output T U hP hQ
   obtain ⟨hr⟩ := sequence_runs P Q input middle output T U hP hQ
   refine ⟨{hr with steps_le_m := hr.steps_le_m.trans ?_}⟩
   have hl := output_length P input middle T hP
   nlinarith

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.BinarySubtract
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinarySubtract
open RawStack
abbrev State := BinaryAdder.State
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((!a && (b || c)) || (b && c),(xor (xor a b) c)::s.2.2.2)))
 def raw (A B : List Bool) : Bool×List Bool :=
   let s := (step^[A.length+B.length+1]) (A,(B,(false,[])))
   (s.2.2.1,s.2.2.2.reverse)
 def difference (A B : List Bool) : List Bool := if (raw A B).1 then [] else trim (raw A B).2
 def less (A B : List Bool) : Bool := (raw A B).1

 theorem bit_balance (a b c : Bool) :
     a.toNat+2*((!a && (b || c)) || (b && c)).toNat=b.toNat+c.toNat+(xor (xor a b) c).toNat := by
   cases a <;> cases b <;> cases c <;> decide

 def potential (s : State) : ℤ :=
   (value s.2.2.2.reverse:ℤ)+(2:ℤ)^s.2.2.2.length*((value s.1:ℤ)-(value s.2.1:ℤ)-s.2.2.1.toNat)

 theorem step_potential (s : State) : potential (step s)=potential s := by
   rcases s with ⟨A,B,c,R⟩
   have ha := BinaryAdder.value_head_tail A
   have hb := BinaryAdder.value_head_tail B
   have hf := bit_balance (A.headD false) (B.headD false) c
   have haZ : (value A:ℤ)=(A.headD false).toNat+2*(value A.tail:ℤ) := by exact_mod_cast ha
   have hbZ : (value B:ℤ)=(B.headD false).toNat+2*(value B.tail:ℤ) := by exact_mod_cast hb
   have hfZ : ((A.headD false).toNat:ℤ)+2*((!A.headD false && (B.headD false || c)) || (B.headD false && c)).toNat=
       (B.headD false).toNat+c.toNat+(xor (xor (A.headD false) (B.headD false)) c).toNat := by exact_mod_cast hf
   simp only [potential,step,List.reverse_cons,BinaryAdder.value_append,List.length_reverse,List.length_cons,pow_succ,value,Nat.mul_zero,Nat.add_zero]
   push_cast
   rw [haZ,hbZ]
   have hh := congrArg (fun z : ℤ => (2:ℤ)^R.length*z) hfZ
   nlinarith only [hh]

 theorem iter_potential (s : State) (t : ℕ) : potential (step^[t] s)=potential s := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_potential _).trans ih

 theorem iter_lists (s : State) (t : ℕ) :
     (step^[t] s).1=s.1.drop t ∧ (step^[t] s).2.1=s.2.1.drop t ∧
       (step^[t] s).2.2.2.length=s.2.2.2.length+t := by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     exact ⟨List.tail_drop,List.tail_drop,by omega⟩

 theorem raw_balance (A B : List Bool) : value A+2^(A.length+B.length+1)*(raw A B).1.toNat=value B+value (raw A B).2 := by
   let n := A.length+B.length+1
   let s : State := (A,(B,(false,[])))
   let t := step^[n] s
   have hh := iter_potential s n
   have hl := iter_lists s n
   have hA : t.1=[] := by rw [hl.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hB : t.2.1=[] := by rw [hl.2.1]; exact List.drop_eq_nil_of_le (by dsimp [n,s]; omega)
   have hlen : t.2.2.2.length=n := by simpa only [s,List.length_nil,Nat.zero_add] using hl.2.2
   change potential t=potential s at hh
   dsimp only [potential] at hh
   rw [hA,hB,hlen] at hh
   dsimp only [s] at hh
   simp only [value,List.reverse_nil,List.length_nil,pow_zero,Bool.toNat_false,Int.ofNat_zero,zero_sub,mul_one] at hh
   have heq : (value A:ℤ)+(2:ℤ)^n*(t.2.2.1.toNat:ℤ)=(value B:ℤ)+(value t.2.2.2.reverse:ℤ) := by linarith only [hh]
   exact_mod_cast heq

 theorem raw_length (A B : List Bool) : (raw A B).2.length=A.length+B.length+1 := by
   have hh := (iter_lists (A,(B,(false,[]))) (A.length+B.length+1)).2.2
   simpa only [raw,List.length_reverse,List.length_nil,Nat.zero_add] using hh

 theorem less_iff (A B : List Bool) : less A B=true ↔ value A< value B := by
   have hb := raw_balance A B
   have hl := value_lt (raw A B).2
   rw [raw_length] at hl
   unfold less
   cases h : (raw A B).1 <;> simp only [h,Bool.toNat_false,Bool.toNat_true,Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hb ⊢ <;> simp only [Bool.false_eq_true,false_iff,true_iff] <;> omega

 theorem difference_value (A B : List Bool) : value (difference A B)=value A-value B := by
   unfold difference
   by_cases h : (raw A B).1=true
   · rw [if_pos h]
     have hh := (less_iff A B).mp h
     simp [value,Nat.sub_eq_zero_of_le hh.le]
   · have hb := raw_balance A B
     have hf : (raw A B).1=false := Bool.eq_false_iff.mpr h
     rw [hf,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at hb
     rw [if_neg h,trim_value]
     omega

 theorem difference_canonical (A B : List Bool) : trim (difference A B)=difference A B := by
   unfold difference
   split_ifs
   · rfl
   · exact trim_idem _

 theorem difference_length (A B : List Bool) : (difference A B).length≤ A.length := by
   rw [← difference_canonical A B]
   apply trim_length_of_lt
   rw [difference_value]
   exact (Nat.sub_le _ _).trans_lt (value_lt A)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryDivision
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def divideStep (x : Bool×(List Bool×(List Bool×List Bool))) : List Bool×(List Bool×List Bool) :=
   let B := x.2.1
   let R := x.1::x.2.2.1
   if BinarySubtract.less R B then (B,(trim R,false::x.2.2.2))
   else (B,(BinarySubtract.difference R B,true::x.2.2.2))
 def divide (A B : List Bool) : List Bool×List Bool :=
   let s := A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   (trim s.2.2,trim s.2.1)

 theorem divideStep_base (b : Bool) (B R Q : List Bool) : (divideStep (b,(B,(R,Q)))).1=B := by
   dsimp only [divideStep]
   split_ifs <;> rfl

 theorem divideStep_balance (b : Bool) (B R Q : List Bool) :
     value (divideStep (b,(B,(R,Q)))).2.1+value B*value (divideStep (b,(B,(R,Q)))).2.2=
       b.toNat+2*(value R+value B*value Q) := by
   unfold divideStep
   by_cases h : BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     have hb := (BinarySubtract.less_iff _ _).mp h
     simp only [value,Bool.toNat_false]
     ring
   · rw [if_neg h]
     rw [BinarySubtract.difference_value]
     have hb : value B≤ value (b::R) := by
       exact Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have he := Nat.sub_add_cancel hb
     simp only [value,Bool.toNat_true] at he ⊢
     nlinarith only [he]

 theorem divideStep_remainder (b : Bool) (B R Q : List Bool) (hB : 0< value B) (hR : value R< value B) :
     value (divideStep (b,(B,(R,Q)))).2.1< value B := by
   unfold divideStep
   by_cases h : BinarySubtract.less (b::R) B=true
   · rw [if_pos h]
     rw [trim_value]
     exact (BinarySubtract.less_iff _ _).mp h
   · rw [if_neg h,BinarySubtract.difference_value]
     have hb : value B≤ value (b::R) := Nat.le_of_not_gt (fun hh => h ((BinarySubtract.less_iff _ _).mpr hh))
     have hbit : b.toNat≤1 := by cases b <;> decide
     simp only [value] at hb ⊢
     omega

 theorem divide_fold_base (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).1=B := by
   induction L generalizing R Q with
   | nil => rfl
   | cons b L ih =>
     rw [List.foldl_cons]
     have hs := divideStep_base b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hs
     subst B'
     exact ih R' Q'

 theorem divide_fold_balance (L B R Q : List Bool) :
     let s := L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))
     value s.2.1+value B*value s.2.2=value L.reverse+2^L.length*(value R+value B*value Q) := by
   induction L generalizing R Q with
   | nil => simp [value]
   | cons b L ih =>
     dsimp only
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hstep := divideStep_balance b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     have hh := ih R' Q'
     dsimp only at hh
     rw [hh,List.reverse_cons,BinaryAdder.value_append]
     simp only [value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     rw [hstep]
     ring

 theorem divide_fold_remainder (L B R Q : List Bool) (hB : 0< value B) (hR : value R< value B) :
     value (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1< value B := by
   induction L generalizing R Q with
   | nil => exact hR
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hstep := divideStep_remainder b B R Q hB hR
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hstep
     subst B'
     exact ih R' Q' hstep

 theorem divide_value (A B : List Bool) (hB : 0< value B) :
     value (divide A B).1=value A/value B ∧ value (divide A B).2=value A%value B := by
   have hb := divide_fold_balance A.reverse B [] []
   have hr := divide_fold_remainder A.reverse B [] [] hB (by simpa only [value] using hB)
   dsimp only at hb
   simp only [List.reverse_reverse,value,Nat.mul_zero,Nat.add_zero] at hb
   have he := (Nat.div_mod_unique hB).mpr ⟨hb,hr⟩
   dsimp only [divide]
   simp only [trim_value]
   exact ⟨he.1.symm,he.2.symm⟩

 theorem divideStep_qlength (b : Bool) (B R Q : List Bool) :
     (divideStep (b,(B,(R,Q)))).2.2.length=Q.length+1 := by
   dsimp only [divideStep]
   split_ifs <;> simp

 theorem divideStep_canonical (b : Bool) (B R Q : List Bool) :
     trim (divideStep (b,(B,(R,Q)))).2.1=(divideStep (b,(B,(R,Q)))).2.1 := by
   dsimp only [divideStep]
   split_ifs
   · exact trim_idem _
   · dsimp only [BinarySubtract.difference]
     split_ifs
     · rfl
     · exact trim_idem _

 theorem divide_fold_qlength (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.2.length=Q.length+L.length := by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hlen := divideStep_qlength b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     rw [ih,hlen]
     simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

 theorem divide_fold_canonical (L B R Q : List Bool) (hR : trim R=R) :
     trim (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1=(L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1 := by
   induction L generalizing R Q with
   | nil => exact hR
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hcanon := divideStep_canonical b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hcanon
     subst B'
     exact ih R' Q' hcanon

 theorem divide_prefix_lengths (A B : List Bool) (hB : 0< value B) (j : ℕ) (hj : j≤ A.length) :
     let s := (A.reverse.take j).foldl (fun s b => divideStep (b,s)) (B,([],[]))
     s.1=B ∧ s.2.1.length≤ B.length ∧ s.2.2.length≤ A.length := by
   let L := A.reverse.take j
   have hbase := divide_fold_base L B [] []
   have hr := divide_fold_remainder L B [] [] hB (by simpa only [value] using hB)
   have hc := divide_fold_canonical L B [] [] rfl
   have hq := divide_fold_qlength L B [] []
   have hlen : L.length≤ A.length := by dsimp [L]; simp only [List.length_take,List.length_reverse]; omega
   refine ⟨hbase,?_,?_⟩
   · rw [← hc]
     exact trim_length_of_lt _ B.length (hr.trans (value_lt B))
   · simp only [List.length_nil,Nat.zero_add] at hq
     exact hq.le.trans hlen

 theorem divideStep_rlength (b : Bool) (B R Q : List Bool) :
     (divideStep (b,(B,(R,Q)))).2.1.length≤ R.length+1 := by
   dsimp only [divideStep]
   split_ifs
   · exact (trim_length _).trans (by simp)
   · exact (BinarySubtract.difference_length _ _).trans (by simp)

 theorem divide_fold_rlength (L B R Q : List Bool) :
     (L.foldl (fun s b => divideStep (b,s)) (B,(R,Q))).2.1.length≤ R.length+L.length := by
   induction L generalizing R Q with
   | nil => simp
   | cons b L ih =>
     rw [List.foldl_cons]
     have hbase := divideStep_base b B R Q
     have hlen := divideStep_rlength b B R Q
     generalize he : divideStep (b,(B,(R,Q)))=s at *
     rcases s with ⟨B',R',Q'⟩
     dsimp only at hbase hlen
     subst B'
     have hh := ih R' Q'
     simp only [List.length_cons]
     omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EuclidBound
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryEuclid

 def step (s : ℕ×ℕ) : ℕ×ℕ := if s.2=0 then s else (s.2,s.1%s.2)

 theorem mod_mod_half (b r : ℕ) (hr : 0< r) (hrb : r< b) : 2*(b%r)< b := by
   by_cases h : 2*r≤ b
   · have hm := Nat.mod_lt b hr
     omega
   · have hb : r≤ b := by omega
     have hsmall : b-r< r := by omega
     have he : b%r=b-r := by rw [Nat.mod_eq_sub_mod hb,Nat.mod_eq_of_lt hsmall]
     rw [he]
     omega

 theorem two_step (a b L : ℕ) (hb : b<2^(L+1)) : (step^[2] (a,b)).2<2^L := by
   by_cases hb0 : b=0
   · simp [step,hb0]
   · have hbpos : 0< b := by omega
     by_cases hr0 : a%b=0
     · simp [Function.iterate_succ_apply,step,hb0,hr0]
     · have hr : 0< a%b := by omega
       have hrb := Nat.mod_lt a hbpos
       have hh := mod_mod_half b (a%b) hr hrb
       simp only [Function.iterate_succ_apply,Function.iterate_zero_apply,step,hb0,if_false,hr0]
       rw [pow_succ] at hb
       omega

 theorem terminates (a b L : ℕ) (hb : b<2^L) : (step^[2*L] (a,b)).2=0 := by
   induction L generalizing a b with
   | zero =>
     simp only [pow_zero] at hb
     have hb0 : b=0 := by omega
     simpa using hb0
   | succ L ih =>
     have hh := two_step a b L hb
     have ht := ih (step^[2] (a,b)).1 (step^[2] (a,b)).2 hh
     rw [Nat.mul_succ,Function.iterate_add_apply]
     exact ht

 theorem gcd_step (s : ℕ×ℕ) : (step s).1.gcd (step s).2=s.1.gcd s.2 := by
   rcases s with ⟨a,b⟩
   by_cases hb : b=0
   · simp [step,hb]
   · simp only [step,hb,if_false]
     rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm]

 theorem gcd_iter (s : ℕ×ℕ) (t : ℕ) : (step^[t] s).1.gcd (step^[t] s).2=s.1.gcd s.2 := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (gcd_step _).trans ih

end EdgeSublinearMWIS.Main.BinaryEuclid
end

-- Solutions.BinaryGcd
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
namespace BinaryGcd

 def step (s : List Bool×List Bool) : List Bool×List Bool :=
   if s.2=[] then s else (s.2,(divide s.1 s.2).2)
 def run (A B : List Bool) : List Bool×List Bool := step^[2*B.length] (trim A,trim B)
 def gcd (A B : List Bool) : List Bool := (run A B).1

 theorem divide_lengths (A B : List Bool) :
     (divide A B).1.length≤ A.length ∧ (divide A B).2.length≤ A.length := by
   have hr := divide_fold_rlength A.reverse B [] []
   have hq := divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   constructor
   · exact (trim_length _).trans hq.le
   · exact (trim_length _).trans hr

 theorem divide_canonical (A B : List Bool) : trim (divide A B).1=(divide A B).1 ∧
     trim (divide A B).2=(divide A B).2 := ⟨trim_idem _,trim_idem _⟩

 theorem canonical_step (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) :
     trim (step s).1=(step s).1 ∧ trim (step s).2=(step s).2 := by
   unfold step
   split_ifs
   · exact ⟨hA,hB⟩
   · exact ⟨hB,(divide_canonical _ _).2⟩

 theorem canonical_iter (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) (t : ℕ) :
     trim (step^[t] s).1=(step^[t] s).1 ∧ trim (step^[t] s).2=(step^[t] s).2 := by
   induction t with
   | zero => exact ⟨hA,hB⟩
   | succ t ih => rw [Function.iterate_succ_apply']; exact canonical_step _ ih.1 ih.2

 theorem value_positive (A : List Bool) (hA : trim A=A) (hn : A≠[]) : 0< value A := by
   have h := trim_lower A (by simpa only [hA] using hn)
   rw [hA] at h
   exact lt_of_lt_of_le (by positivity : 0<2^(A.length-1)) h

 theorem values_step (s : List Bool×List Bool) (hB : trim s.2=s.2) :
     (value (step s).1,value (step s).2)=BinaryEuclid.step (value s.1,value s.2) := by
   by_cases hb : s.2=[]
   · simp [step,hb,value,BinaryEuclid.step]
   · have hp := value_positive s.2 hB hb
     have he := (divide_value s.1 s.2 hp).2
     simp only [step,hb,if_false,BinaryEuclid.step,ne_of_gt hp,he]

 theorem values_iter (s : List Bool×List Bool) (hA : trim s.1=s.1) (hB : trim s.2=s.2) (t : ℕ) :
     (value (step^[t] s).1,value (step^[t] s).2)=BinaryEuclid.step^[t] (value s.1,value s.2) := by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
     rw [values_step _ (canonical_iter s hA hB t).2,ih]

 theorem run_second (A B : List Bool) : (run A B).2=[] := by
   have hc := (canonical_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)).2
   have hv := values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have ht := BinaryEuclid.terminates (value (trim A)) (value (trim B)) B.length (by rw [trim_value]; exact value_lt B)
   have hz : value (run A B).2=0 := by
     exact (congrArg Prod.snd hv).trans ht
   by_contra hn
   exact (ne_of_gt (value_positive _ hc hn)) hz

 theorem gcd_value (A B : List Bool) : value (gcd A B)=(value A).gcd (value B) := by
   have hv := values_iter (trim A,trim B) (trim_idem A) (trim_idem B) (2*B.length)
   have hg := BinaryEuclid.gcd_iter (value (trim A),value (trim B)) (2*B.length)
   have hv1 := congrArg Prod.fst hv
   have hv2 := congrArg Prod.snd hv
   change value (run A B).1=_ at hv1
   change value (run A B).2=_ at hv2
   rw [← hv1,← hv2,run_second,value,Nat.gcd_zero_right,trim_value,trim_value] at hg
   exact hg

 theorem length_step (s : List Bool×List Bool) : (step s).1.length+(step s).2.length≤ s.1.length+s.2.length := by
   unfold step
   split_ifs
   · rfl
   · have hh := (divide_lengths s.1 s.2).2
     dsimp only
     omega

 theorem length_iter (s : List Bool×List Bool) (t : ℕ) :
     (step^[t] s).1.length+(step^[t] s).2.length≤ s.1.length+s.2.length := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (length_step _).trans ih

end BinaryGcd
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryCanonical
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 theorem natBits_eq_bits (n : ℕ) : natBits n=n.bits := by
   simp only [natBits,Nat.digits_two_eq_bits,List.map_map]
   have he : ((fun b : ℕ => b==1) ∘ (fun b : Bool => cond b 1 0))=id := by funext b; cases b <;> rfl
   rw [he,List.map_id]

 theorem trim_eq_bits_value (A : List Bool) : trim A=(value A).bits := by
   induction A with
   | nil => exact Nat.zero_bits.symm
   | cons b A ih =>
     by_cases hA : trim A=[]
     · have hv : value A=0 := by rw [← trim_value A,hA]; rfl
       cases b <;> simp [trim,hA,value,hv,Nat.zero_bits,Nat.one_bits]
     · have hp := BinaryGcd.value_positive (trim A) (trim_idem A) hA
       rw [trim_value] at hp
       have hb : Nat.bit b (value A)=b.toNat+2*value A := by cases b <;> simp [Nat.bit]; omega
       simp only [trim,hA,if_false]
       rw [ih,value,← hb,Nat.bits_append_bit (value A) b (by omega)]

 theorem trim_eq_natBits (A : List Bool) : trim A=natBits (value A) := by
   rw [natBits_eq_bits]
   exact trim_eq_bits_value A

 theorem canonical_eq_natBits (A : List Bool) (hA : trim A=A) : A=natBits (value A) := by
   exact hA.symm.trans (trim_eq_natBits A)

 theorem canonical_value_injective (A B : List Bool) (hA : trim A=A) (hB : trim B=B) (h : value A=value B) : A=B := by
   rw [canonical_eq_natBits A hA,canonical_eq_natBits B hB,h]

 theorem value_natBits (n : ℕ) : value (natBits n)=n := by
   rw [natBits_eq_bits]
   induction n using Nat.binaryRecFromOne with
   | zero => simp [Nat.zero_bits,value]
   | one => simp [Nat.one_bits,value]
   | bit b n hn ih =>
     rw [Nat.bits_append_bit n b (fun h => False.elim (hn h))]
     cases b <;> simp [value,ih,Nat.bit] <;> omega

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterate
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem iterate_coefficient (F D : ℕ) : 10000*F+10000*(D+3)≤100000*(F+D+10) := by omega
 theorem iterate_output_coefficient (F D : ℕ) : D+1≤100000*(F+D+10) := by omega

 theorem polynomial_iterate {f : α → α} {R : Realizer f} (hR : PolyBound R) (D : ℕ)
    (hg : ∀x,volume (f x)≤ volume x+D) : PolyBound R.iterate := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(D+2)^q
   refine ⟨100000*(F+D+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z := volume (n,a)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha : volume a≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hiter (j : ℕ) : volume (f^[j] a)≤ volume a+D*j := by
     induction j with
     | zero => simp
     | succ j ih => rw [Function.iterate_succ_apply']; have hh := hg (f^[j] a); nlinarith
   have hV (j : ℕ) (hj : j≤ n) : volume (f^[j] a)≤(D+1)*z := by
     have hh := hiter j
     have hd := Nat.mul_le_mul_left D (show j≤ z by omega)
     nlinarith
   have hT (j : ℕ) (hj : j< n) : R.time (f^[j] a)≤ F*z^q := by
     have hh := (hR (f^[j] a)).1
     have hv := hV j hj.le
     have hbase : volume (f^[j] a)+1≤(D+2)*z := by nlinarith
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht := Realizer.time_iterate_le R n a (F*z^q) ((D+1)*z) hT hV
   have hq : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+2) := by exact (show z≤ z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+D+10)*z^(q+2)
     have hmul : (n+1)*(F*z^q+(D+1)*z+n+1)≤ z*(F*z^q+(D+3)*z) :=
       Nat.mul_le_mul hn (by nlinarith)
     have hmul' := Nat.mul_le_mul_left 10000 hmul
     have hp1 := Nat.mul_le_mul_left (10000*F) hq
     have hp2 := Nat.mul_le_mul_left (10000*(D+3)) hq2
     have hsmall : R.iterate.time (n,a)≤(10000*F+10000*(D+3))*z^(q+2) := by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     have hcoef := iterate_coefficient F D
     exact hsmall.trans (Nat.mul_le_mul_right (z^(q+2)) hcoef)
   · change volume (f^[n] a)≤100000*(F+D+10)*z^(q+2)
     have hcoef := iterate_output_coefficient F D
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left (D+1) hze).trans (Nat.mul_le_mul_right (z^(q+2)) hcoef))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinarySubtractRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def notA : Realizer (fun s : State => !s.1.headD false) := BinaryAdder.bitA.comp Realizer.not
 def borrowBit : Realizer (fun s : State =>
     (!s.1.headD false && (s.2.1.headD false || s.2.2.1))||(s.2.1.headD false && s.2.2.1)) :=
   ((notA.pair ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.or)).comp Realizer.and).pair
     ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.and) |>.comp Realizer.or
 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp BinaryAdder.tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
       (borrowBit.pair ((BinaryAdder.sumBit.pair BinaryAdder.revOutput).comp Realizer.cons)))).congr (fun _ => rfl)
 def rawRealizer : Realizer (fun x : List Bool×List Bool => raw x.1 x.2) :=
   (((BinaryAdder.lengthBound.pair BinaryAdder.initialState).comp stepRealizer.iterate).comp
     (BinaryAdder.bitC.pair (BinaryAdder.revOutput.comp Realizer.reverse))).congr (fun _ => rfl)
 def lessRealizer : Realizer (fun x : List Bool×List Bool => less x.1 x.2) := rawRealizer.comp Realizer.fst
 def differenceRealizer : Realizer (fun x : List Bool×List Bool => difference x.1 x.2) :=
   (rawRealizer.comp (Realizer.nil.choose RawStack.trimRealizer)).congr (fun _ => rfl)

 theorem step_linear : Linear stepRealizer := by
   have hnot : Linear notA := linear_comp BinaryAdder.bitA_linear linear_not
   have hborrow : Linear borrowBit := linear_comp
     (linear_pair (linear_comp (linear_pair hnot (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_or)) linear_and)
       (linear_comp (linear_pair BinaryAdder.bitB_linear BinaryAdder.bitC_linear) linear_and)) linear_or
   unfold stepRealizer
   apply linear_congr
   exact linear_pair (linear_comp linear_fst BinaryAdder.tailBits_linear)
     (linear_pair (linear_comp (linear_comp linear_snd linear_fst) BinaryAdder.tailBits_linear)
       (linear_pair hborrow (linear_comp (linear_pair BinaryAdder.sumBit_linear BinaryAdder.revOutput_linear) linear_cons)))

 theorem step_volume (s : State) : volume (step s)≤ volume s+6 := by
   rcases s with ⟨A,B,c,R⟩
   have hA : volume A.tail≤ volume A := by cases A <;> simp [volume_cons] <;> omega
   have hB : volume B.tail≤ volume B := by cases B <;> simp [volume_cons] <;> omega
   have hsum := volume_bool (xor (xor (A.headD false) (B.headD false)) c)
   have hcarry := volume_bool ((!A.headD false && (B.headD false || c))||(B.headD false && c))
   have hc : 1≤ volume c := volume_pos c
   simp only [step,volume_pair,volume_cons]
   omega

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.SubtractPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem raw_polynomial : PolyBound rawRealizer := by
   have hpre := polynomial_pair RawStack.lengthBound_polynomial (linear_polynomial BinaryAdder.initial_linear)
   have hiter := polynomial_iterate (linear_polynomial step_linear) 6 step_volume
   have hpost := polynomial_pair (linear_polynomial BinaryAdder.bitC_linear)
     (polynomial_comp (linear_polynomial BinaryAdder.revOutput_linear) RawStack.reverse_polynomial)
   unfold rawRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_comp hpre hiter) hpost

 theorem less_polynomial : PolyBound lessRealizer :=
   polynomial_comp raw_polynomial (linear_polynomial linear_fst)

 theorem difference_polynomial : PolyBound differenceRealizer := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold differenceRealizer
   apply polynomial_congr
   exact polynomial_comp raw_polynomial (polynomial_choose (linear_polynomial hn) RawStack.trim_polynomial)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryDivisionRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
abbrev DivisionState := List Bool×(List Bool×List Bool)
abbrev DivisionInput := Bool×DivisionState

 def divisionDen : Realizer (fun x : DivisionInput => x.2.1) := Realizer.snd.comp Realizer.fst
 def divisionOldR : Realizer (fun x : DivisionInput => x.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def divisionOldQ : Realizer (fun x : DivisionInput => x.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def divisionNewR : Realizer (fun x : DivisionInput => x.1::x.2.2.1) :=
   (Realizer.fst.pair divisionOldR).comp Realizer.cons
 def divisionPair : Realizer (fun x : DivisionInput => (x.1::x.2.2.1,x.2.1)) := divisionNewR.pair divisionDen
 def divisionTest : Realizer (fun x : DivisionInput => BinarySubtract.less (x.1::x.2.2.1) x.2.1) :=
   divisionPair.comp BinarySubtract.lessRealizer
 def divisionRemainder : Realizer (fun x : DivisionInput =>
     if BinarySubtract.less (x.1::x.2.2.1) x.2.1 then trim (x.1::x.2.2.1) else BinarySubtract.difference (x.1::x.2.2.1) x.2.1) :=
   (divisionTest.pair divisionPair).comp ((Realizer.fst.comp trimRealizer).choose BinarySubtract.differenceRealizer)
 def divisionQ : Realizer (fun x : DivisionInput => (!BinarySubtract.less (x.1::x.2.2.1) x.2.1)::x.2.2.2) :=
   ((divisionTest.comp Realizer.not).pair divisionOldQ).comp Realizer.cons
 def divideStepRealizer : Realizer divideStep :=
   (divisionDen.pair (divisionRemainder.pair divisionQ)).congr (fun x => by
     rcases x with ⟨b,B,R,Q⟩
     cases h : BinarySubtract.less (b::R) B <;> simp [divideStep,h])
 def divideInitial : Realizer (fun x : List Bool×List Bool => (x.1.reverse,(x.2,(([] : List Bool),([] : List Bool))))) :=
   (Realizer.fst.comp Realizer.reverse).pair (Realizer.snd.pair (Realizer.nil.pair Realizer.nil))
 def divisionFinish : Realizer (fun x : DivisionState => (trim x.2.2,trim x.2.1)) :=
   ((Realizer.snd.comp Realizer.snd).comp trimRealizer).pair ((Realizer.snd.comp Realizer.fst).comp trimRealizer)
 def divideRealizer : Realizer (fun x : List Bool×List Bool => divide x.1 x.2) :=
   ((divideInitial.comp divideStepRealizer.fold).comp divisionFinish).congr (fun _ => rfl)

 theorem divideStep_polynomial : PolyBound divideStepRealizer := by
   have hden : PolyBound divisionDen := linear_polynomial (linear_comp linear_snd linear_fst)
   have hr : PolyBound divisionOldR := linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_fst)
   have hq : PolyBound divisionOldQ := linear_polynomial (linear_comp (linear_comp linear_snd linear_snd) linear_snd)
   have hnew : PolyBound divisionNewR := polynomial_comp (polynomial_pair (linear_polynomial linear_fst) hr) (linear_polynomial linear_cons)
   have hp : PolyBound divisionPair := polynomial_pair hnew hden
   have ht : PolyBound divisionTest := polynomial_comp hp BinarySubtract.less_polynomial
   have hrem : PolyBound divisionRemainder := polynomial_comp (polynomial_pair ht hp)
     (polynomial_choose (polynomial_comp (linear_polynomial linear_fst) trim_polynomial) BinarySubtract.difference_polynomial)
   have hQ : PolyBound divisionQ := polynomial_comp (polynomial_pair (polynomial_comp ht (linear_polynomial linear_not)) hq) (linear_polynomial linear_cons)
   unfold divideStepRealizer
   apply polynomial_congr
   exact polynomial_pair hden (polynomial_pair hrem hQ)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldPrefixBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

 theorem fold_prefix_bound {f : α×β → β} (R : Realizer f) (xs : List α) (b : β) (T V : ℕ)
    (hvol : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) b)≤ V)
    (htime : ∀j (hj : j< xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) b)≤ T) :
    Realizer.foldTime R b xs≤ xs.length*(T+20*(volume xs+2*V+1))+1 := by
   induction xs generalizing b with
   | nil => simp [Realizer.foldTime]
   | cons a xs ih =>
     have hb : volume b≤ V := by simpa using hvol 0 (by simp)
     have hb' : volume (f (a,b))≤ V := by simpa using hvol 1 (by simp)
     have ht : R.time (a,b)≤ T := by
       have ht0 := htime 0 (by simp)
       change R.time (a,b)≤ T at ht0
       exact ht0
     have hvol' : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤ V := by
       intro j hj
       have hh := hvol (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons] using hh
     have htime' : ∀j (hj : j< xs.length),R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) (f (a,b)))≤ T := by
       intro j hj
       have hh := htime (j+1) (by simp only [List.length_cons]; omega)
       simpa only [List.take_succ_cons,List.foldl_cons,List.getElem_cons_succ] using hh
     have hh := ih (f (a,b)) hvol' htime'
     simp only [Realizer.foldTime,List.length_cons] at hh ⊢
     have hvolxs : volume xs≤ volume (a::xs) := by simp only [volume_cons]; omega
     have hbound : xs.length*(T+20*(volume xs+2*V+1))≤ xs.length*(T+20*(volume (a::xs)+2*V+1)) :=
       Nat.mul_le_mul_left _ (by omega)
     nlinarith only [hh,ht,hb,hb',hbound]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BitFoldEnvelope
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {β : Type} [Coding β]

 theorem bit_fold_envelope {f : Bool×β → β} (R : Realizer f) (C q : ℕ)
    (htime : ∀x,R.time x≤ C*(volume x+1)^q)
    (xs : List Bool) (acc : β) (z : ℕ) (hz : 1≤ z) (hlen : xs.length≤ z)
    (hxs : volume xs≤5*z)
    (hvol : ∀j,j≤ xs.length → volume ((xs.take j).foldl (fun b a => f (a,b)) acc)≤12*z) :
    R.fold.time (xs,acc)≤(C*17^q+2000)*z^(q+2) := by
   have hT (j : ℕ) (hj : j< xs.length) : R.time (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)≤ C*17^q*z^q := by
     have hh := htime (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)
     have hb := volume_bool xs[j]
     have hs := hvol j hj.le
     have hv : volume (xs[j],(xs.take j).foldl (fun b a => f (a,b)) acc)+1≤17*z := by simp only [volume_pair]; omega
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hv q))
     simpa only [mul_pow,Nat.mul_assoc] using ht
   have hf := fold_prefix_bound R xs acc (C*17^q*z^q) (12*z) hvol hT
   have hq1 : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hzgrow : z≤ z^2 := by nlinarith
   have hmul : xs.length*(C*17^q*z^q+20*(volume xs+2*(12*z)+1))≤ z*(C*17^q*z^q+600*z) := Nat.mul_le_mul hlen (by omega)
   have hqprod : z*(C*17^q*z^q)=C*17^q*z^(q+1) := by rw [pow_succ]; ring
   have hf' : Realizer.foldTime R acc xs≤(C*17^q+1000)*z^(q+2) := by
     have ht := Nat.mul_le_mul_left (C*17^q) hq1
     have hc := Nat.mul_le_mul_left 1000 hq2
     simp only [Nat.mul_add,hqprod] at hmul
     nlinarith only [hf,hmul,ht,hc,hzgrow,hz]
   have hacc : volume acc≤12*z := by simpa only [List.take_zero,List.foldl_nil] using hvol 0 (by omega)
   have hpow : z≤ z^(q+2) := hzgrow.trans hq2
   rw [Realizer.time_fold]
   simp only [volume_pair]
   nlinarith only [hf',hxs,hacc,hpow,hz]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DivisionRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem division_prefix_volume (A B : List Bool) (j : ℕ) (hj : j≤ A.length) :
     volume ((A.reverse.take j).foldl (fun s b => divideStep (b,s)) (B,([],[])))≤12*(A.length+B.length+1) := by
   let L := A.reverse.take j
   let s := L.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hb := divide_fold_base L B [] []
   have hr := divide_fold_rlength L B [] []
   have hq := divide_fold_qlength L B [] []
   have hlen : L.length≤ A.length := by dsimp [L]; simp only [List.length_take,List.length_reverse]; omega
   change s.1=B at hb
   change s.2.1.length≤[].length+L.length at hr
   change s.2.2.length=[].length+L.length at hq
   simp only [List.length_nil,Nat.zero_add] at hr hq
   have hvB := BinaryAdder.volume_bits s.1
   have hvR := BinaryAdder.volume_bits s.2.1
   have hvQ := BinaryAdder.volume_bits s.2.2
   rw [hb] at hvB
   change volume (s.1,(s.2.1,s.2.2))≤ _
   simp only [volume_pair]
   rw [hb]
   omega

 theorem division_fold_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     divideStepRealizer.fold.time (A.reverse,(B,([],[])))≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hR⟩ := divideStep_polynomial
   refine ⟨C*17^q+2000,q+2,by positivity,?_⟩
   intro A B
   apply bit_fold_envelope divideStepRealizer C q (fun x => (hR x).1)
   · omega
   · simp only [List.length_reverse]; omega
   · rw [volume_reverse]
     have hA := BinaryAdder.volume_bits A
     omega
   · intro j hj
     exact division_prefix_volume A B j (by simpa only [List.length_reverse] using hj)

 theorem divideInitial_polynomial : PolyBound divideInitial := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : List Bool×List Bool => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   exact polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (polynomial_pair (linear_polynomial linear_snd) (polynomial_pair (linear_polynomial hn) (linear_polynomial hn)))

 theorem divisionFinish_polynomial : PolyBound divisionFinish :=
   polynomial_pair (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_snd)) trim_polynomial)
     (polynomial_comp (linear_polynomial (linear_comp linear_snd linear_fst)) trim_polynomial)

 theorem divide_time : ∃ C q : ℕ,0< C ∧ ∀ A B : List Bool,
     divideRealizer.time (A,B)≤ C*(A.length+B.length+1)^q := by
   obtain ⟨C,q,hC,hfold⟩ := division_fold_time
   obtain ⟨I,p,hI,hinit⟩ := divideInitial_polynomial
   obtain ⟨D,r,hD,hpost⟩ := divisionFinish_polynomial
   let e := p+q+r+2
   refine ⟨I*5^p+C+D*13^r+1000,e,by positivity,?_⟩
   intro A B
   let z := A.length+B.length+1
   let initial : List Bool×DivisionState := (A.reverse,(B,([],[])))
   let final := A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   have hz : 1≤ z := by dsimp [z]; omega
   have hp : z^p≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hq : z^q≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hr : z^r≤ z^e := Nat.pow_le_pow_right hz (by dsimp [e]; omega)
   have hze : z≤ z^e := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by dsimp [e]; omega : 1≤ e)
   have hA := BinaryAdder.volume_bits A
   have hB := BinaryAdder.volume_bits B
   have hvx : volume (A,B)+1≤5*z := by simp only [volume_pair]; dsimp [z]; omega
   have hvi : volume initial≤7*z := by dsimp [initial]; simp only [volume_pair,volume_nil,volume_reverse]; dsimp [z]; omega
   have hvf : volume final≤12*z := by
     have hh := division_prefix_volume A B A.length le_rfl
     rw [← List.length_reverse (as := A), List.take_length] at hh
     simpa only [List.length_reverse] using hh
   have hi : divideInitial.time (A,B)≤ I*5^p*z^e := by
     have hh := ((hinit (A,B)).1).trans (Nat.mul_le_mul_left I (Nat.pow_le_pow_left hvx p))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (I*5^p) hp)
   have hf : divideStepRealizer.fold.time initial≤ C*z^e := (hfold A B).trans (Nat.mul_le_mul_left C hq)
   have ho : divisionFinish.time final≤ D*13^r*z^e := by
     have hh := ((hpost final).1).trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_left (show volume final+1≤13*z by omega) r))
     simp only [mul_pow] at hh
     exact hh.trans (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (D*13^r) hr)
   have hcopy : 10*(volume initial+1)+10*(volume final+1)≤1000*z^e := by omega
   have heq : divideRealizer.time (A,B)=divideInitial.time (A,B)+divideStepRealizer.fold.time initial+
       10*(volume initial+1)+divisionFinish.time final+10*(volume final+1) := by
     dsimp only [divideRealizer,divide]
     simp only [Realizer.time_congr,Realizer.time_comp,Function.comp_apply]
     rfl
   rw [heq]
   change _≤(I*5^p+C+D*13^r+1000)*z^e
   nlinarith only [hi,hf,ho,hcopy]

 theorem divide_lengths (A B : List Bool) :
     (divide A B).1.length≤ A.length ∧ (divide A B).2.length≤ A.length := by
   have hr := divide_fold_rlength A.reverse B [] []
   have hq := divide_fold_qlength A.reverse B [] []
   simp only [List.length_nil,Nat.zero_add,List.length_reverse] at hr hq
   exact ⟨(trim_length _).trans hq.le,(trim_length _).trans hr⟩

 theorem divide_polynomial : PolyBound divideRealizer := by
   obtain ⟨C,q,hC,hT⟩ := divide_time
   refine ⟨C+12,q+1,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := volume (A,B)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hbase : A.length+B.length+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hp : (A.length+B.length+1)^q≤ z^(q+1) := (Nat.pow_le_pow_left hbase q).trans (Nat.pow_le_pow_right hz (by omega))
   have ht := (hT A B).trans (Nat.mul_le_mul_left C hp)
   have hvQ := BinaryAdder.volume_bits (divide A B).1
   have hvR := BinaryAdder.volume_bits (divide A B).2
   have hlen := divide_lengths A B
   have hpow : z≤ z^(q+1) := by simpa only [pow_one] using Nat.pow_le_pow_right hz (by omega : 1≤ q+1)
   constructor
   · exact ht.trans (Nat.mul_le_mul_right _ (by omega))
   · change volume ((divide A B).1,(divide A B).2)≤ _
     simp only [volume_pair]
     have hv : volume (divide A B).1+volume (divide A B).2+1≤12*z^(q+1) := by omega
     simpa only [z,volume_pair] using hv.trans (Nat.mul_le_mul_right (z^(q+1)) (show 12≤ C+12 from Nat.le_add_left _ _))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterateBounded
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 theorem polynomial_iterate_bounded {f : α → α} {R : Realizer f} (hR : PolyBound R) (E : ℕ)
    (hg : ∀x j,volume (f^[j] x)≤ E*(volume x+1)) : PolyBound R.iterate := by
   obtain ⟨C,q,hC,hR⟩ := hR
   let F := C*(E+1)^q
   refine ⟨100000*(F+E+10),q+2,by dsimp [F]; positivity,?_⟩
   rintro ⟨n,a⟩
   let z := volume (n,a)+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hn : n+1≤ z := by dsimp [z]; simp only [volume_pair,volume_nat]; omega
   have ha : volume a+1≤ z := by dsimp [z]; simp only [volume_pair]; omega
   have hV (j : ℕ) (_hj : j≤ n) : volume (f^[j] a)≤ E*z :=
     (hg a j).trans (Nat.mul_le_mul_left E ha)
   have hT (j : ℕ) (hj : j< n) : R.time (f^[j] a)≤ F*z^q := by
     have hh := (hR (f^[j] a)).1
     have hv := hV j hj.le
     have hbase : volume (f^[j] a)+1≤(E+1)*z := by nlinarith
     have ht := hh.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbase q))
     simpa only [F,mul_pow,Nat.mul_assoc] using ht
   have ht := Realizer.time_iterate_le R n a (F*z^q) (E*z) hT hV
   have hq : z^(q+1)≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hq2 : z^2≤ z^(q+2) := Nat.pow_le_pow_right hz (by omega)
   have hze : z≤ z^(q+2) := (show z≤ z^2 by nlinarith).trans hq2
   constructor
   · change _≤100000*(F+E+10)*z^(q+2)
     have hmul : (n+1)*(F*z^q+E*z+n+1)≤ z*(F*z^q+(E+3)*z) := Nat.mul_le_mul hn (by nlinarith)
     have hmul' := Nat.mul_le_mul_left 10000 hmul
     have hp1 := Nat.mul_le_mul_left (10000*F) hq
     have hp2 := Nat.mul_le_mul_left (10000*(E+3)) hq2
     have hs : R.iterate.time (n,a)≤(10000*F+10000*(E+3))*z^(q+2) := by
       rw [pow_succ] at hp1
       nlinarith only [ht,hmul',hp1,hp2]
     exact hs.trans (Nat.mul_le_mul_right _ (iterate_coefficient F E))
   · change volume (f^[n] a)≤100000*(F+E+10)*z^(q+2)
     exact (hV n le_rfl).trans ((Nat.mul_le_mul_left E hze).trans
       (Nat.mul_le_mul_right _ (by have := iterate_output_coefficient F E; omega)))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryGcdRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack.BinaryGcd
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def stepRealizer : Realizer step :=
   (((Realizer.snd.comp nonemptyBits).pair Realizer.id).comp
     ((Realizer.snd.pair (divideRealizer.comp Realizer.snd)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨A,B⟩
       cases B <;> simp [step,nonemptyBits])

 theorem step_polynomial : PolyBound stepRealizer := by
   unfold stepRealizer
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (linear_polynomial (linear_comp linear_snd nonempty_linear)) (linear_polynomial linear_id))
     (polynomial_choose (polynomial_pair (linear_polynomial linear_snd)
       (polynomial_comp divide_polynomial (linear_polynomial linear_snd))) (linear_polynomial linear_id))

 theorem iterate_volume (s : List Bool×List Bool) (t : ℕ) : volume (step^[t] s)≤5*(volume s+1) := by
   rcases s with ⟨A,B⟩
   have hlen := length_iter (A,B) t
   dsimp only at hlen
   have hA := bits_length_volume A
   have hB := bits_length_volume B
   have hvA := BinaryAdder.volume_bits (step^[t] (A,B)).1
   have hvB := BinaryAdder.volume_bits (step^[t] (A,B)).2
   change volume ((step^[t] (A,B)).1,(step^[t] (A,B)).2)≤ _
   simp only [volume_pair]
   omega

 theorem iterate_polynomial : PolyBound stepRealizer.iterate :=
   polynomial_iterate_bounded step_polynomial 5 iterate_volume

 def iterationCount : Realizer (fun s : List Bool×List Bool => 2*s.2.length) :=
   ((Realizer.snd.comp BinaryAdder.wordLength).pair (Realizer.snd.comp BinaryAdder.wordLength)).comp Realizer.add
     |>.congr (fun s => by dsimp only [Function.comp_apply]; omega)
 def initialRealizer : Realizer (fun s : List Bool×List Bool => (trim s.1,trim s.2)) :=
   (Realizer.fst.comp trimRealizer).pair (Realizer.snd.comp trimRealizer)
 def runRealizer : Realizer (fun s : List Bool×List Bool => run s.1 s.2) :=
   ((iterationCount.pair initialRealizer).comp stepRealizer.iterate).congr (fun _ => rfl)
 def gcdRealizer : Realizer (fun s : List Bool×List Bool => gcd s.1 s.2) := runRealizer.comp Realizer.fst

 theorem wordLength_polynomial : PolyBound BinaryAdder.wordLength := by
   refine ⟨1000002,2,by omega,?_⟩
   intro A
   have ht := BinaryAdder.wordLength_time A
   have hlen := bits_length_volume A
   have hp := Nat.pow_le_pow_left (show A.length+1≤ volume A+1 by omega) 2
   have hz : 1≤ volume A+1 := by omega
   have hpow : volume A+1≤(volume A+1)^2 := by nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 1000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · simp only [volume_nat]
     omega

 theorem nat_add_polynomial : PolyBound Realizer.add := by
   refine ⟨10000001,2,by omega,?_⟩
   rintro ⟨a,b⟩
   have ht := Realizer.time_add_le a b
   have hbase : a+b+1≤ volume (a,b)+1 := by simp only [volume_pair,volume_nat]; omega
   have hp := Nat.pow_le_pow_left hbase 2
   have hv : volume (a+b)≤2*(volume (a,b)+1)^2 := by
     simp only [volume_nat,volume_pair]
     nlinarith
   constructor
   · exact ht.trans ((Nat.mul_le_mul_left 10000000 hp).trans (Nat.mul_le_mul_right _ (by omega)))
   · exact hv.trans (Nat.mul_le_mul_right _ (by omega))

 theorem iterationCount_polynomial : PolyBound iterationCount := by
   unfold iterationCount
   apply polynomial_congr
   exact polynomial_comp
     (polynomial_pair (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial)
       (polynomial_comp (linear_polynomial linear_snd) wordLength_polynomial))
     nat_add_polynomial

 theorem initial_polynomial : PolyBound initialRealizer :=
   polynomial_pair (polynomial_comp (linear_polynomial linear_fst) trim_polynomial)
     (polynomial_comp (linear_polynomial linear_snd) trim_polynomial)

 theorem gcd_polynomial : PolyBound gcdRealizer := by
   apply polynomial_comp _ (linear_polynomial linear_fst)
   unfold runRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair iterationCount_polynomial initial_polynomial) iterate_polynomial

end EdgeSublinearMWIS.Main.RawStack.BinaryGcd
end

-- Solutions.BinaryRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def normalizeWords (A B : List Bool) : List Bool×List Bool :=
   let D := BinaryGcd.gcd A B
   ((divide A D).1,(divide B D).1)

 def gcdArguments : Realizer (fun x : List Bool×List Bool => (x,BinaryGcd.gcd x.1 x.2)) :=
   Realizer.id.pair BinaryGcd.gcdRealizer
 def normalizeFirst : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.1 x.2).1) :=
   (((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeSecond : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.2 x.2).1) :=
   (((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeWordsRealizer : Realizer (fun x : List Bool×List Bool => normalizeWords x.1 x.2) :=
   (gcdArguments.comp (normalizeFirst.pair normalizeSecond)).congr (fun _ => rfl)

 theorem normalizeWords_polynomial : PolyBound normalizeWordsRealizer := by
   have h1 : PolyBound normalizeFirst := polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_fst)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   have h2 : PolyBound normalizeSecond := polynomial_comp
     (polynomial_comp (polynomial_pair (linear_polynomial (linear_comp linear_fst linear_snd)) (linear_polynomial linear_snd)) divide_polynomial)
     (linear_polynomial linear_fst)
   unfold normalizeWordsRealizer
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (linear_polynomial linear_id) BinaryGcd.gcd_polynomial) (polynomial_pair h1 h2)

 theorem normalizeWords_values (A B : List Bool) (hB : 0< value B) :
     value (normalizeWords A B).1=value A/(value A).gcd (value B) ∧
     value (normalizeWords A B).2=value B/(value A).gcd (value B) := by
   have hD : 0< value (BinaryGcd.gcd A B) := by rw [BinaryGcd.gcd_value]; exact Nat.gcd_pos_of_pos_right _ hB
   exact ⟨(divide_value A _ hD).1.trans (by rw [BinaryGcd.gcd_value]),
     (divide_value B _ hD).1.trans (by rw [BinaryGcd.gcd_value])⟩

 theorem normalizeWords_canonical (A B : List Bool) :
     trim (normalizeWords A B).1=(normalizeWords A B).1 ∧ trim (normalizeWords A B).2=(normalizeWords A B).2 :=
   ⟨trim_idem _,trim_idem _⟩

 def signedValue (b : Bool) (A : List Bool) : ℤ := if b then -(value A : ℤ) else value A

 theorem signedValue_natAbs (b : Bool) (A : List Bool) : (signedValue b A).natAbs=value A := by
   cases b <;> simp [signedValue]

 theorem normalized_rat_num_den (z : ℤ) (d : ℕ) (hd : 0< d) :
     ((z : ℚ)/d).num.natAbs=z.natAbs/(z.natAbs.gcd d) ∧
     ((z : ℚ)/d).den=d/(z.natAbs.gcd d) := by
   have he : (z : ℚ)/(d : ℚ)=Rat.normalize z d (by omega) := by
     rw [Rat.normalize_eq_mkRat,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
     norm_cast
   rw [he,Rat.num_normalize,Rat.den_normalize]
   constructor
   · rw [Int.natAbs_ediv_of_dvd]
     · simp
     · exact Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
   · rfl

 theorem normalizeWords_rat (b : Bool) (A B : List Bool) (hB : 0< value B) :
     (normalizeWords A B).1=natBits (((signedValue b A : ℚ)/value B).num.natAbs) ∧
     (normalizeWords A B).2=natBits (((signedValue b A : ℚ)/value B).den) := by
   have hv := normalizeWords_values A B hB
   have hr := normalized_rat_num_den (signedValue b A) (value B) hB
   rw [signedValue_natAbs] at hr
   have hc := normalizeWords_canonical A B
   constructor
   · rw [canonical_eq_natBits _ hc.1,hv.1,← hr.1]
   · rw [canonical_eq_natBits _ hc.2,hv.2,← hr.2]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryListCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def appendBits : Realizer (fun x : List Bool×List Bool => x.1++x.2) :=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun x => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

 theorem cons_fold_polynomial : PolyBound (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)).fold := by
   refine ⟨100000,3,by omega,?_⟩
   rintro ⟨A,B⟩
   let z := A.length+B.length+1
   have hz : 1≤ z := by dsimp [z]; omega
   have hvol : ∀j,j≤ A.length → volume ((A.take j).foldl (fun s b => b::s) B)≤12*z := by
     intro j hj
     rw [Realizer.fold_cons_eq]
     have hv := BinaryAdder.volume_bits ((A.take j).reverse++B)
     simp only [List.length_append,List.length_reverse,List.length_take] at hv
     dsimp [z]
     omega
   have ht := bit_fold_envelope (Realizer.cons : Realizer (fun x : Bool×List Bool => x.1::x.2)) 3 1
     (fun x => by change volume x+2≤3*(volume x+1)^1; simp only [pow_one]; omega) A B z hz (by dsimp [z]; omega)
     (by have hh := BinaryAdder.volume_bits A; dsimp [z]; omega) hvol
   have hbase : z≤ volume (A,B)+1 := by
     have hA := bits_length_volume A
     have hB := bits_length_volume B
     dsimp [z]; simp only [volume_pair]; omega
   have hp := Nat.pow_le_pow_left hbase 3
   constructor
   · have he : 3*17^1+2000≤100000 := by norm_num
     exact ht.trans ((Nat.mul_le_mul_left _ hp).trans (Nat.mul_le_mul_right _ he))
   · change volume (A.foldl (fun s b => b::s) B)≤ _
     have hv := hvol A.length le_rfl
     rw [List.take_length] at hv
     have hh : z≤(volume (A,B)+1)^3 := hbase.trans (by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1≤ volume (A,B)+1) (by omega : 1≤3))
     have hs : volume (A.foldl (fun s b => b::s) B)≤12*(volume (A,B)+1)^3 := by omega
     exact hs.trans (Nat.mul_le_mul_right _ (by omega))

 theorem appendBits_polynomial : PolyBound appendBits := by
   unfold appendBits
   apply polynomial_congr
   exact polynomial_comp (polynomial_pair (polynomial_comp (linear_polynomial linear_fst) reverse_polynomial)
     (linear_polynomial linear_snd)) cons_fold_polynomial

 def prependTrue : Realizer (fun L : List Bool => true::L) := ((Realizer.constant true).pair Realizer.id).comp Realizer.cons
 theorem prependTrue_linear : Linear prependTrue := by
   have ht : Linear (Realizer.constant true : Realizer (fun _ : List Bool => true)) := linear_bool _ 2000 (fun L => by change (2*3+1)*(20*volume L+50*3+50)≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def replicateTrue : Realizer (fun n : ℕ => List.replicate n true) :=
   ((Realizer.id.pair Realizer.nil).comp prependTrue.iterate).congr (fun n => by
     change (fun L : List Bool => true::L)^[n] []=List.replicate n true
     induction n with
     | zero => rfl
     | succ n ih => rw [Function.iterate_succ_apply',ih,List.replicate_succ])
 theorem replicateTrue_polynomial : PolyBound replicateTrue := by
   have hn : Linear (Realizer.nil : Realizer (fun _ : ℕ => ([] : List Bool))) :=
     linear_of _ 3 (by omega) (fun _ => by change 2≤ _; omega) (fun _ => by simp; omega)
   unfold replicateTrue
   apply polynomial_congr
   apply polynomial_comp (polynomial_pair (linear_polynomial linear_id) (linear_polynomial hn))
   exact polynomial_iterate (linear_polynomial prependTrue_linear) 4 (fun L => by simp only [volume_cons,volume_bool_true]; omega)

 def prefixBits (A : List Bool) : List Bool := List.replicate A.length true++false::A
 def falseCons : Realizer (fun L : List Bool => false::L) := (Realizer.false.pair Realizer.id).comp Realizer.cons
 theorem falseCons_linear : Linear falseCons := by
   have ht : Linear (Realizer.false : Realizer (fun _ : List Bool => false)) := linear_bool _ 3 (fun _ => by change 2≤ _; omega)
   exact linear_comp (linear_pair ht linear_id) linear_cons
 def prefixRealizer : Realizer prefixBits :=
   ((BinaryAdder.wordLength.comp replicateTrue).pair falseCons).comp appendBits
 theorem prefix_polynomial : PolyBound prefixRealizer :=
   polynomial_comp (polynomial_pair (polynomial_comp BinaryGcd.wordLength_polynomial replicateTrue_polynomial)
     (linear_polynomial falseCons_linear)) appendBits_polynomial

 theorem prefix_natBits (n : ℕ) : prefixBits (natBits n)=encodeNat n := by
   simp only [prefixBits,encodeNat,List.append_assoc,List.singleton_append]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ContextCall
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
attribute [local instance] Turing.FinTM2.kFin Turing.FinTM2.ΛFin Turing.FinTM2.kDecidableEq Turing.FinTM2.σFin

 inductive Extra where | raw | context | count | consume | temp deriving Fintype,DecidableEq
 inductive CallPhase where | count | context | out | into | emitContext | prefix deriving Fintype,DecidableEq
 abbrev CallK (U : Program) := U.machine.tm.K⊕Extra
 abbrev CallΓ (U : Program) : CallK U → Type := StackSum U.machine.tm.Γ (fun _ : Extra => Bool)
 abbrev CallΛ (U : Program) := U.machine.tm.Λ⊕CallPhase
 abbrev Callσ (U : Program) := U.machine.tm.σ×Option Bool
 def callCarry {U : Program} (v : Callσ U) (a : Option Bool) : Callσ U := (v.1,a)
 def callNext {U : Program} (p : CallPhase) : Stmt (CallΓ U) (CallΛ U) (Callσ U) :=
   .load (fun v => callCarry v none) (.goto (fun _ => .inr p))
 def callCode (U : Program) : CallΛ U → Stmt (CallΓ U) (CallΛ U) (Callσ U)
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

 noncomputable instance callAlphabet (U : Program) (k : CallK U) : Fintype (CallΓ U k) :=
   @Fintype.ofFinite _ (by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance)
 def callTM (U : Program) : Turing.FinTM2 where
   K := CallK U
   Γ := CallΓ U
   Λ := CallΛ U
   σ := Callσ U
   k₀ := .inr .raw
   k₁ := .inl U.machine.tm.k₁
   initialState := (U.machine.tm.initialState,none)
   main := .inr .count
   m := callCode U
 def callWithContext (U : Program) : Program where
   machine := ⟨callTM U,(by change Bool ≃ Bool; exact Equiv.refl _),
     (by change U.machine.tm.Γ U.machine.tm.k₁ ≃ Bool; exact U.machine.outputAlphabet)⟩
   finiteAlphabet k := by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextState
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

 def extraStore (R C N D T : List Bool) : Extra → List Bool
   | .raw => R
   | .context => C
   | .count => N
   | .consume => D
   | .temp => T
 def callCfg (U : Program) (p : CallPhase) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) : (callTM U).Cfg :=
   cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (extraStore R C N D T))
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

 theorem count_step_true (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .count S (true::R) C N D T)=
       some (callCfg U .count S R C (true::N) (true::D) T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.count≠Extra.raw),
     Function.update_of_ne (by decide : Extra.consume≠Extra.raw),Function.update_of_ne (by decide : Extra.consume≠Extra.count)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]

 theorem count_step_false (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .count S (false::R) C N D T)=some (callCfg U .context S R C N D T) := by
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

-- Solutions.ContextSteps
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

 theorem context_step_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b d : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .context S (b::R) C N (d::D) T)=
       some (callCfg U .context S R (b::C) N D T) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.raw≠Extra.consume),
     Function.update_of_ne (by decide : Extra.context≠Extra.consume),Function.update_of_ne (by decide : Extra.context≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem context_step_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N T : List Bool) :
     step (callCode U) (callCfg U .context S R C N [] T)=some (callCfg U .out S R C N [] T) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]
 theorem call_out_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .out S (b::R) C N D T)=some (callCfg U .out S R C N D (b::T)) := by
   simp only [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.isSome_some,cond_true,Option.getD_some]
   simp only [update_extend_right,Function.update_of_ne (by decide : Extra.temp≠Extra.raw)]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   funext k
   cases k with
   | inl k => rfl
   | inr e => cases e <;> simp [extendStore,Function.update,extraStore]
 theorem call_out_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (C N D T : List Bool) :
     step (callCode U) (callCfg U .out S [] C N D T)=some (callCfg U .into S [] C N D T) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update]

 theorem call_into_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .into S R C N D (b::T))=some (callCfg U .into
       (Function.update S U.machine.tm.k₀ (U.machine.inputAlphabet.symm b::S U.machine.tm.k₀)) R C N D T) := by
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
 theorem call_into_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C N D : List Bool) :
     step (callCode U) (callCfg U .into S R C N D [])=
       some (extendCfg .emitContext (none : Option Bool) (extraStore R C N D [])
         (cfg (some U.machine.tm.main) U.machine.tm.initialState S)) := by
   simp [callCfg,cfg,step,callCode,stepAux,callCarry,callNext,extraStore,extendStore,Function.update,extendCfg]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextEmission
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

 theorem emit_context_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .emitContext S R (b::C) N D T)=some (callCfg U .emitContext
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm b::S U.machine.tm.k₁)) R C N D T) := by
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
 theorem emit_context_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R N D T : List Bool) :
     step (callCode U) (callCfg U .emitContext S R [] N D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm false::S U.machine.tm.k₁)) R [] N D T) := by
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
 theorem prefix_step_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R C N D T : List Bool) :
     step (callCode U) (callCfg U .prefix S R C (b::N) D T)=some (callCfg U .prefix
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm true::S U.machine.tm.k₁)) R C N D T) := by
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
 def callHaltCfg (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C D T : List Bool) : (callTM U).Cfg :=
   cfg none (U.machine.tm.initialState,none) (extendStore S (extraStore R C [] D T))
 theorem prefix_step_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (R C D T : List Bool) :
     step (callCode U) (callCfg U .prefix S R C [] D T)=some (callHaltCfg U S R C D T) := by
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

 theorem callHalt_only (U : Program) (output : List Bool) :
     callHaltCfg U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []=
       Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (onlyStack U.machine.tm.k₁ _) (extraStore [] [] [] [] [])=(Turing.haltList (callTM U) _).stk
   rw [haltList_store]
   funext k
   cases k with
   | inl k =>
     by_cases h : k=U.machine.tm.k₁
     · subst k; simp [onlyStack,Function.update,extendStore,callTM]
     · simp [onlyStack,Function.update,extendStore,callTM,h]
   | inr e => cases e <;> simp [onlyStack,Function.update,extendStore,callTM,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextReadLoops
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

 theorem count_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (n : ℕ) (rest C N D T : List Bool) :
     run (callCode U) (callCfg U .count S (List.replicate n true++false::rest) C N D T) (n+1)=
       some (callCfg U .context S rest C (List.replicate n true++N) (List.replicate n true++D) T) := by
   induction n generalizing N D with
   | zero => exact count_step_false U S rest C N D T
   | succ n ih =>
     simp only [List.replicate_succ,List.cons_append]
     rw [run_first,count_step_true,Option.bind_some]
     have hh := ih (true::N) (true::D)
     have hn : ∀L : List Bool,List.replicate n true++true::L=true::(List.replicate n true++L) := by
       intro L
       calc
         _ = (List.replicate n true++[true])++L := by simp
         _ = List.replicate (n+1) true++L := by rw [List.replicate_succ']
         _ = _ := rfl
     simpa only [hn] using hh
 theorem context_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L rest C N T : List Bool) :
     run (callCode U) (callCfg U .context S (L++rest) C N (List.replicate L.length true) T) (L.length+1)=
       some (callCfg U .out S rest (L.reverse++C) N [] T) := by
   induction L generalizing C with
   | nil => exact context_step_nil U S rest C N T
   | cons b L ih =>
     simp only [List.length_cons,List.replicate_succ,List.cons_append]
     rw [run_first,context_step_cons,Option.bind_some]
     have hh := ih (b::C)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem call_out_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L C N D T : List Bool) :
     run (callCode U) (callCfg U .out S L C N D T) (L.length+1)=
       some (callCfg U .into S [] C N D (L.reverse++T)) := by
   induction L generalizing T with
   | nil => exact call_out_nil U S C N D T
   | cons b L ih =>
     rw [List.length_cons,run_first,call_out_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem inputCfg_only (U : Program) (input : List Bool) :
     cfg (some U.machine.tm.main) U.machine.tm.initialState
       (onlyStack U.machine.tm.k₀ (input.map U.machine.inputAlphabet.symm))=
       Turing.initList U.machine.tm (input.map U.machine.inputAlphabet.symm) := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   exact (initList_store _ _).symm
 theorem call_into_loop (U : Program) (L acc R C N D : List Bool) :
     run (callCode U) (callCfg U .into (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D L) (L.length+1)=
       some (extendCfg .emitContext (none : Option Bool) (extraStore R C N D [])
         (Turing.initList U.machine.tm ((L.reverse++acc).map U.machine.inputAlphabet.symm))) := by
   induction L generalizing acc with
   | nil =>
     have hh := call_into_nil U (onlyStack U.machine.tm.k₀ (acc.map U.machine.inputAlphabet.symm)) R C N D
     rw [inputCfg_only] at hh
     exact hh
   | cons b L ih =>
     rw [List.length_cons,run_first,call_into_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::acc)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextWriteLoops
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

 theorem emit_context_loop (U : Program) (C output R N D T : List Bool) :
     run (callCode U) (callCfg U .emitContext
       (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R C N D T) (C.length+1)=
       some (callCfg U .prefix (onlyStack U.machine.tm.k₁
         ((false::(C.reverse++output)).map U.machine.outputAlphabet.symm)) R [] N D T) := by
   induction C generalizing output with
   | nil =>
     have hh := emit_context_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) R N D T
     rw [onlyStack_self,onlyStack_update] at hh
     exact hh
   | cons b C ih =>
     rw [List.length_cons,run_first,emit_context_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::output)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem prefix_loop (U : Program) (n : ℕ) (output : List Bool) :
     run (callCode U) (callCfg U .prefix (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
       [] [] (List.replicate n true) [] []) (n+1)=
       some (Turing.haltList (callTM U) ((List.replicate n true++output).map U.machine.outputAlphabet.symm)) := by
   induction n generalizing output with
   | zero =>
     have hh := prefix_step_nil U (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [] [] []
     rw [callHalt_only] at hh
     exact hh
   | succ n ih =>
     rw [List.replicate_succ,run_first,prefix_step_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (true::output)
     have he : List.replicate n true++true::output=List.replicate (n+1) true++output := by
       rw [List.replicate_succ',List.append_assoc,List.singleton_append]
     simpa only [List.map_cons,he,List.replicate_succ,List.cons_append] using hh

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.ContextCallRuns
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

 theorem call_start (U : Program) (ctx input : List Bool) :
     Turing.initList (callTM U) (prefixBits ctx++input)=
       callCfg U .count (fun _ => []) (List.replicate ctx.length true++false::(ctx++input)) [] [] [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [callTM,callCfg,cfg,onlyStack,Function.update,extendStore,extraStore,prefixBits,List.append_assoc]
 theorem call_after_halt (U : Program) (ctx output : List Bool) :
     extendCfg .emitContext (none : Option Bool) (extraStore [] ctx.reverse (List.replicate ctx.length true) [] [])
       (Turing.haltList U.machine.tm (output.map U.machine.outputAlphabet.symm))=
         callCfg U .emitContext (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm))
           [] ctx.reverse (List.replicate ctx.length true) [] [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (Turing.haltList U.machine.tm _).stk _=extendStore (onlyStack U.machine.tm.k₁ _) _
   rw [haltList_store]

 theorem call_context_runs (U : Program) (ctx input output : List Bool) (T : ℕ) (hU : Runs U input output T) :
     Runs (callWithContext U) (prefixBits ctx++input) (prefixBits ctx++output)
       (T+4*ctx.length+2*input.length+6) := by
   change Nonempty (Turing.TM2OutputsInTime (callTM U) ((prefixBits ctx++input).map id)
     (some ((prefixBits ctx++output).map U.machine.outputAlphabet.symm)) (T+4*ctx.length+2*input.length+6))
   rw [List.map_id]
   obtain ⟨t,ht,hu⟩ := outputs_run U input output T hU
   let S : ∀k,List (U.machine.tm.Γ k) := fun _ => []
   let N := List.replicate ctx.length true
   have h1 := count_loop U S ctx.length (ctx++input) [] [] [] []
   simp only [List.append_nil] at h1
   rw [← call_start] at h1
   have h2 := context_loop U S ctx input [] N []
   simp only [List.append_nil] at h2
   have h3 := call_out_loop U S input ctx.reverse N [] []
   simp only [List.append_nil] at h3
   have h4 := call_into_loop U input.reverse [] [] ctx.reverse N []
   simp only [List.map_nil,onlyStack_nil,List.reverse_reverse,List.append_nil,List.length_reverse] at h4
   have h5 := run_extend .emitContext U.machine.tm.m (callCode U) (fun _ => rfl) _ _ (none : Option Bool)
     (extraStore [] ctx.reverse N [] []) t hu
   rw [call_after_halt] at h5
   have h6 := emit_context_loop U ctx.reverse output [] N [] []
   simp only [List.reverse_reverse,List.length_reverse] at h6
   have h7 := prefix_loop U ctx.length (false::(ctx++output))
   have hr := run_trans _ _ _ _ _ _ h1 h2
   have hr := run_trans _ _ _ _ _ _ hr h3
   have hr := run_trans _ _ _ _ _ _ hr h4
   have hr := run_trans _ _ _ _ _ _ hr h5
   have hr := run_trans _ _ _ _ _ _ hr h6
   have hr := run_trans _ _ _ _ _ _ hr h7
   have he : List.replicate ctx.length true++false::(ctx++output)=prefixBits ctx++output := by
     simp only [prefixBits,List.append_assoc,List.cons_append]
   rw [he] at hr
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=callTM U) (prefixBits ctx++input)
     ((prefixBits ctx++output).map U.machine.outputAlphabet.symm) _ hr
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.PolynomialContextPipeline
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ProgramComposition
open RawStack OAI.ThreeMachine.StackCompiler RealizerBounds

 theorem polynomial_context_pipeline {f g : List Bool → List Bool} (R : Realizer f) (S : Realizer g)
     (hR : PolyBound R) (hS : PolyBound S) (U : Program) :
     ∃ (P : Program) (time size : Polynomial ℕ),
       ∀ (input ctx middle output : List Bool) (T : ℕ), f input=prefixBits ctx++middle → Runs U middle output T →
         ∃ s,Runs P input (g (prefixBits ctx++output)) s ∧
           s≤ time.eval (T+input.length+1) ∧ middle.length+1≤ size.eval (input.length+1) := by
   obtain ⟨Pre,A,p,hA,hp,hPre⟩ := TreeToTM2.realizer_poly_program R hR
   obtain ⟨Post,C,r,hC,hr,hPost⟩ := TreeToTM2.realizer_poly_program S hS
   let AB := sequence Pre (callWithContext U)
   let P := sequence AB Post
   obtain ⟨K₁,hK₁,hSeq₁⟩ := sequence_runs_linear Pre (callWithContext U)
   obtain ⟨K₂,hK₂,hSeq₂⟩ := sequence_runs_linear AB Post
   let B := StackSpace.bound Pre.machine.tm
   obtain ⟨K,hK,hBound⟩ := pipeline_time_bound A C K₁ K₂ B (StackSpace.bound AB.machine.tm) p r hA hC hK₁ hK₂ hp
   refine ⟨P,Polynomial.C K*Polynomial.X^(p+p*r+1),Polynomial.X+Polynomial.C (B*A)*Polynomial.X^p,?_⟩
   intro input ctx middle output T hf hU
   let ret := prefixBits ctx++output
   let preTime := A*(input.length+1)^p
   let callTime := T+4*ctx.length+2*middle.length+6
   let abTime := K₁*(preTime+callTime+input.length+1)
   let postTime := C*(ret.length+1)^r
   have hpre := hPre input
   have hcall := call_context_runs U ctx middle output T hU
   rw [← hf] at hcall
   have hab : Runs AB input ret abTime := hSeq₁ input (f input) ret preTime callTime hpre hcall
   have hpost := hPost ret
   have hfinal := hSeq₂ input ret (g ret) abTime postTime hab hpost
   refine ⟨K₂*(abTime+postTime+input.length+1),hfinal,?_,?_⟩
   · have hcallBound : callTime≤ T+6*(f input).length+7 := by
       rw [hf]
       simp only [List.length_append,prefixBits,List.length_replicate,List.length_cons]
       dsimp only [callTime]
       omega
     have hb := hBound input.length 0 T (f input).length ret.length callTime abTime postTime
       (by simpa only [Nat.add_zero] using output_length Pre input (f input) preTime hpre) hcallBound
       (by simp only [Nat.add_zero]; rfl) (output_length AB input ret abTime hab) rfl
     simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Nat.add_zero] using hb
   · have hout := output_length Pre input (f input) preTime hpre
     rw [hf] at hout
     have hmid : middle.length≤(prefixBits ctx++middle).length := by simp only [List.length_append]; omega
     have hh : middle.length+1≤ input.length+1+(B*A)*(input.length+1)^p := by
       dsimp only [B,preTime] at hout ⊢
       nlinarith only [hout,hmid]
     simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow] using hh
end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.Sol_context_pipeline
noncomputable section

open scoped Classical
set_option autoImplicit false
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main

theorem solution (f g : List Bool → List Bool) (R : Realizer f) (S : Realizer g)
    (hR : ∃ C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q)
    (hS : ∃ C q : ℕ,0< C ∧ ∀x,S.time x≤ C*(volume x+1)^q ∧ volume (g x)≤ C*(volume x+1)^q)
    (U : EdgeSublinearMWIS.Main.Program) :
    ∃ (P : EdgeSublinearMWIS.Main.Program) (time size : Polynomial ℕ),
      ∀ (input ctx middle output : List Bool) (T : ℕ),
        f input=(List.replicate ctx.length true++false::ctx)++middle → Runs U middle output T →
        ∃s,Runs P input (g ((List.replicate ctx.length true++false::ctx)++output)) s ∧
          s≤ time.eval (T+input.length+1) ∧ middle.length+1≤ size.eval (input.length+1) := by
  simpa only [RawStack.prefixBits] using ProgramComposition.polynomial_context_pipeline R S hR hS U
end
