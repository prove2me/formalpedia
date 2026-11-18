-- Prove2me | solution 1 for EdgeSublinearMWIS.Main.gated_polynomial_context_program
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:35:31.985208+00:00
-- url     : https://prove2.me/submissions/2d964227-6f2d-498f-a00b-582feec74aa0

import Mathlib
import Theorems.Thm_EdgeSublinearMWIS_Main_realizer_native_program
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Definitions.Def_EdgeSublinearMWIS_Main_BitExecution

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
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler
 theorem bits_length_volume (L : List Bool) : L.length≤ volume L := by
   induction L with
   | nil => simp
   | cons b L ih => simp only [List.length_cons,volume_cons]; omega

end EdgeSublinearMWIS.Main.RawStack
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler
 theorem volume_bits (A : List Bool) : volume A≤4*A.length+1 :=
   (volume_list_le A 3 (fun b _ => volume_bool b)).trans (by omega)

end EdgeSublinearMWIS.Main.BinaryAdder
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
namespace EdgeSublinearMWIS.Main.StackCompiler
 noncomputable instance alphabetFintype (P : EdgeSublinearMWIS.Main.Program) (k : P.machine.tm.K) : Fintype (P.machine.tm.Γ k) := @Fintype.ofFinite _ (P.finiteAlphabet k)
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

-- Solutions.PolynomialSandwich
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ProgramComposition
open RawStack OAI.ThreeMachine.StackCompiler RealizerBounds
 theorem polynomial_sandwich {f g : List Bool → List Bool} (R : Realizer f) (S : Realizer g)
     (hR : PolyBound R) (hS : PolyBound S) (U : Program) :
     ∃ (P : Program) (time size : Polynomial ℕ),
       ∀ (input output : List Bool) (T : ℕ), Runs U (f input) output T →
         ∃ s,Runs P input (g output) s ∧ s≤ time.eval (T+input.length+1) ∧
           (f input).length+1≤ size.eval (input.length+1) := by
   obtain ⟨Pre,A,p,hA,hp,hPre⟩ := TreeToTM2.realizer_poly_program R hR
   obtain ⟨Post,C,r,hC,hr,hPost⟩ := TreeToTM2.realizer_poly_program S hS
   let AB := sequence Pre U
   let P := sequence AB Post
   obtain ⟨K₁,hK₁,hSeq₁⟩ := sequence_runs_linear Pre U
   obtain ⟨K₂,hK₂,hSeq₂⟩ := sequence_runs_linear AB Post
   let B := StackSpace.bound Pre.machine.tm
   obtain ⟨K,hK,hBound⟩ := pipeline_time_bound A C K₁ K₂ B (StackSpace.bound AB.machine.tm) p r hA hC hK₁ hK₂ hp
   refine ⟨P,Polynomial.C K*Polynomial.X^(p+p*r+1),Polynomial.X+Polynomial.C (B*A)*Polynomial.X^p,?_⟩
   intro input output T hU
   let preTime := A*(input.length+1)^p
   let abTime := K₁*(preTime+T+input.length+1)
   let postTime := C*(output.length+1)^r
   have hpre := hPre input
   have hab : Runs AB input output abTime := hSeq₁ input (f input) output preTime T hpre hU
   have hfinal := hSeq₂ input output (g output) abTime postTime hab (hPost output)
   refine ⟨K₂*(abTime+postTime+input.length+1),hfinal,?_,?_⟩
   · have hb := hBound input.length 0 T (f input).length output.length T abTime postTime
       (by simpa only [Nat.add_zero] using output_length Pre input (f input) preTime hpre) (by omega)
       (by simp only [Nat.add_zero];rfl) (output_length AB input output abTime hab) rfl
     simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,Nat.add_zero] using hb
   · have hout := output_length Pre input (f input) preTime hpre
     have hh : (f input).length+1≤ input.length+1+(B*A)*(input.length+1)^p := by
       dsimp only [B,preTime] at hout ⊢
       nlinarith only [hout]
     simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow] using hh
end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.BinaryListCode
noncomputable section
namespace EdgeSublinearMWIS.Main.RawStack
 def prefixBits (A : List Bool) : List Bool := List.replicate A.length true++false::A
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

-- Solutions.ProgramLabelMap
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EdgeSublinearMWIS.Main.ProgramComposition
open Turing.TM2
variable {κ Λ Ω σ : Type} [DecidableEq κ] {Γ : κ → Type}

 def labelCfg (inj : Λ → Ω) (c : Cfg Γ Λ σ) : Cfg Γ Ω σ := ⟨c.l.map inj,c.var,c.stk⟩
 def labelStmt (inj : Λ → Ω) : Stmt Γ Λ σ → Stmt Γ Ω σ
   | .push k f q => .push k f (labelStmt inj q)
   | .pop k f q => .pop k f (labelStmt inj q)
   | .peek k f q => .peek k f (labelStmt inj q)
   | .load f q => .load f (labelStmt inj q)
   | .branch f q r => .branch f (labelStmt inj q) (labelStmt inj r)
   | .goto f => .goto (inj ∘ f)
   | .halt => .halt
 theorem stepAux_label (inj : Λ → Ω) (q : Stmt Γ Λ σ) (v : σ) (S : ∀k,List (Γ k)) :
     stepAux (labelStmt inj q) v S=labelCfg inj (stepAux q v S) := by
   induction q generalizing v S with
   | push k f q ih => exact ih _ _
   | pop k f q ih => exact ih _ _
   | peek k f q ih => exact ih _ _
   | load f q ih => exact ih _ _
   | branch f q r iq ir =>
     cases hf : f v <;> simp only [labelStmt,stepAux,hf,cond_true,cond_false] <;> first | exact iq v S | exact ir v S
   | goto f => rfl
   | halt => rfl
 theorem step_label (inj : Λ → Ω) (code : Λ → Stmt Γ Λ σ) (target : Ω → Stmt Γ Ω σ)
     (hc : ∀l,target (inj l)=labelStmt inj (code l)) (c : Cfg Γ Λ σ) :
     step target (labelCfg inj c)=(step code c).map (labelCfg inj) := by
   rcases c with ⟨l,v,S⟩
   cases l with
   | none => rfl
   | some l => simp only [labelCfg,Option.map_some,step,hc]; exact congrArg some (stepAux_label inj (code l) v S)
 theorem run_label (inj : Λ → Ω) (code : Λ → Stmt Γ Λ σ) (target : Ω → Stmt Γ Ω σ)
     (hc : ∀l,target (inj l)=labelStmt inj (code l)) (c : Cfg Γ Λ σ) (t : ℕ) :
     RawStack.run target (labelCfg inj c) t=(RawStack.run code c t).map (labelCfg inj) := by
   induction t with
   | zero => rfl
   | succ t ih =>
     rw [RawStack.run,ih,RawStack.run]
     cases hr : RawStack.run code c t with
     | none => rfl
     | some d => simp only [Option.map_some,Option.bind_some,step_label inj code target hc,Option.map_bind]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextCall
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

 inductive GatePhase where | gate | out | into deriving Fintype,DecidableEq
 abbrev GatedΛ (U : Program) := CallΛ U⊕GatePhase
 def gateNext {U : Program} (p : GatePhase) : Stmt (CallΓ U) (GatedΛ U) (Callσ U) :=
   .load (fun v => callCarry v none) (.goto (fun _ => .inr p))
 def gateCode (U : Program) : GatedΛ U → Stmt (CallΓ U) (GatedΛ U) (Callσ U)
   | .inl l => labelStmt Sum.inl (callCode U l)
   | .inr .gate =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.getD false)
         (.load (fun v => callCarry v none) (.goto (fun _ => .inl (.inr .count))))
         (gateNext .out))
   | .inr .out =>
     .pop (.inr .raw) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inr .temp) (fun v => v.2.getD false) (gateNext .out))
         (gateNext .into))
   | .inr .into =>
     .pop (.inr .temp) (fun v a => callCarry v a)
       (.branch (fun v => v.2.isSome)
         (.push (.inl U.machine.tm.k₁) (fun v => U.machine.outputAlphabet.symm (v.2.getD false)) (gateNext .into))
         (.load (fun _ => (U.machine.tm.initialState,none)) .halt))
 def gateTM (U : Program) : Turing.FinTM2 where
   K := CallK U
   Γ := CallΓ U
   Λ := GatedΛ U
   σ := Callσ U
   k₀ := .inr .raw
   k₁ := .inl U.machine.tm.k₁
   initialState := (U.machine.tm.initialState,none)
   main := .inr .gate
   m := gateCode U
 def gatedCall (U : Program) : Program where
   machine := ⟨gateTM U,(by change Bool ≃ Bool; exact Equiv.refl _),
     (by change U.machine.tm.Γ U.machine.tm.k₁ ≃ Bool; exact U.machine.outputAlphabet)⟩
   finiteAlphabet k := by cases k with | inl k => exact U.finiteAlphabet k | inr k => change Finite Bool; infer_instance

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextSteps
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

 def gateCfg (U : Program) (p : GatePhase) (S : ∀k,List (U.machine.tm.Γ k)) (R T : List Bool) : (gateTM U).Cfg :=
   cfg (some (.inr p)) (U.machine.tm.initialState,none) (extendStore S (extraStore R [] [] [] T))
 theorem gate_init (U : Program) (input : List Bool) : Turing.initList (gateTM U) input=gateCfg U .gate (fun _ => []) input [] := by
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [gateTM,gateCfg,cfg,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [gateTM,gateCfg,cfg,onlyStack,Function.update,extendStore,extraStore]
 theorem gate_true_step (U : Program) (input : List Bool) :
     step (gateCode U) (gateCfg U .gate (fun _ => []) (true::input) [])=
       some (labelCfg Sum.inl (Turing.initList (callTM U) input)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,extendStore_inr,extraStore,
     List.head?_cons,List.tail_cons,Option.getD_some,cond_true]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   change extendStore (fun _ => []) (Function.update (extraStore (true::input) [] [] [] []) Extra.raw input)=
     (Turing.initList (callTM U) input).stk
   rw [initList_store]
   funext k
   cases k with
   | inl k => simp [callTM,onlyStack,Function.update,extendStore]
   | inr e => cases e <;> simp [callTM,onlyStack,Function.update,extendStore,extraStore]
 theorem gate_false_step (U : Program) (input : List Bool) :
     step (gateCode U) (gateCfg U .gate (fun _ => []) (false::input) [])=
       some (gateCfg U .out (fun _ => []) input []) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
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
 theorem gated_out_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R T : List Bool) :
     step (gateCode U) (gateCfg U .out S (b::R) T)=some (gateCfg U .out S R (b::T)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
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
 theorem gated_out_nil (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (T : List Bool) :
     step (gateCode U) (gateCfg U .out S [] T)=some (gateCfg U .into S [] T) := by
   simp [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extraStore,extendStore,Function.update]
 theorem gated_into_cons (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (b : Bool) (R T : List Bool) :
     step (gateCode U) (gateCfg U .into S R (b::T))=some (gateCfg U .into
       (Function.update S U.machine.tm.k₁ (U.machine.outputAlphabet.symm b::S U.machine.tm.k₁)) R T) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
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
 theorem gated_into_nil (U : Program) (output : List Bool) :
     step (gateCode U) (gateCfg U .into (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] [])=
       some (Turing.haltList (gateTM U) (output.map U.machine.outputAlphabet.symm)) := by
   simp only [gateCfg,cfg,step,gateCode,stepAux,callCarry,gateNext,extendStore_inr,extraStore,
     List.head?_nil,List.tail_nil,Option.isSome_none,cond_false]
   rw [update_extend_right]
   congr 1
   apply cfg_eq
   case hl => rfl
   case hv => rfl
   rw [haltList_store]
   funext k
   cases k with
   | inl k =>
     by_cases h : k=U.machine.tm.k₁
     · subst k; simp [onlyStack,Function.update,extendStore,gateTM]
     · simp [onlyStack,Function.update,extendStore,gateTM,h]
   | inr e => cases e <;> simp [onlyStack,Function.update,extendStore,gateTM,extraStore]

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.GatedContextRuns
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

 theorem gated_out_loop (U : Program) (S : ∀k,List (U.machine.tm.Γ k)) (L T : List Bool) :
     run (gateCode U) (gateCfg U .out S L T) (L.length+1)=some (gateCfg U .into S [] (L.reverse++T)) := by
   induction L generalizing T with
   | nil => exact gated_out_nil U S T
   | cons b L ih =>
     rw [List.length_cons,run_first,gated_out_cons,Option.bind_some]
     have hh := ih (b::T)
     simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using hh
 theorem gated_into_loop (U : Program) (L output : List Bool) :
     run (gateCode U) (gateCfg U .into (onlyStack U.machine.tm.k₁ (output.map U.machine.outputAlphabet.symm)) [] L) (L.length+1)=
       some (Turing.haltList (gateTM U) ((L.reverse++output).map U.machine.outputAlphabet.symm)) := by
   induction L generalizing output with
   | nil => exact gated_into_nil U output
   | cons b L ih =>
     rw [List.length_cons,run_first,gated_into_cons,onlyStack_self,onlyStack_update,Option.bind_some]
     have hh := ih (b::output)
     simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hh

 theorem gated_false_runs (U : Program) (output : List Bool) :
     Runs (gatedCall U) (false::output) output (2*output.length+3) := by
   change Nonempty (Turing.TM2OutputsInTime (gateTM U) ((false::output).map id)
     (some (output.map U.machine.outputAlphabet.symm)) (2*output.length+3))
   rw [List.map_id]
   have h0 : run (gateCode U) (Turing.initList (gateTM U) (false::output)) 1=
       some (gateCfg U .out (fun _ => []) output []) := by rw [gate_init]; exact gate_false_step U output
   have h1 := gated_out_loop U (fun _ => []) output []
   simp only [List.append_nil] at h1
   have h2 := gated_into_loop U output.reverse []
   simp only [List.map_nil,onlyStack_nil,List.length_reverse,List.reverse_reverse,List.append_nil] at h2
   have hr := run_trans _ _ _ _ _ _ h0 h1
   have hr := run_trans _ _ _ _ _ _ hr h2
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=gateTM U) (false::output) (output.map U.machine.outputAlphabet.symm) _ hr
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

 theorem gated_true_runs (U : Program) (input output : List Bool) (T : ℕ)
     (h : Runs (callWithContext U) input output T) : Runs (gatedCall U) (true::input) output (T+1) := by
   change Nonempty (Turing.TM2OutputsInTime (gateTM U) ((true::input).map id)
     (some (output.map U.machine.outputAlphabet.symm)) (T+1))
   rw [List.map_id]
   obtain ⟨t,ht,hr⟩ := outputs_run (callWithContext U) input output T h
   change run (callCode U) (Turing.initList (callTM U) (input.map id)) t=
     some (Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm)) at hr
   rw [List.map_id] at hr
   have h0 : run (gateCode U) (Turing.initList (gateTM U) (true::input)) 1=
       some (labelCfg Sum.inl (Turing.initList (callTM U) input)) := by rw [gate_init]; exact gate_true_step U input
   have h1 := run_label Sum.inl (callCode U) (gateCode U) (fun _ => rfl) (Turing.initList (callTM U) input) t
   rw [hr,Option.map_some] at h1
   have hhalt : labelCfg Sum.inl (Turing.haltList (callTM U) (output.map U.machine.outputAlphabet.symm))=
     Turing.haltList (gateTM U) (output.map U.machine.outputAlphabet.symm) := rfl
   rw [hhalt] at h1
   have hh := run_trans _ _ _ _ _ _ h0 h1
   obtain ⟨hrun⟩ := RawStack.outputs (tm:=gateTM U) (true::input) (output.map U.machine.outputAlphabet.symm) _ hh
   refine ⟨{hrun with steps_le_m := hrun.steps_le_m.trans ?_}⟩
   omega

 theorem gated_context_runs (U : Program) (ctx input output : List Bool) (T : ℕ) (h : Runs U input output T) :
     Runs (gatedCall U) (true::(prefixBits ctx++input)) (prefixBits ctx++output)
       (T+4*ctx.length+2*input.length+7) := by
   have hh := gated_true_runs U _ _ _ (call_context_runs U ctx input output T h)
   convert hh using 1 <;> omega

end EdgeSublinearMWIS.Main.ProgramComposition
end

-- Solutions.Sol_gated_pipeline
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.RealizerBounds
open EdgeSublinearMWIS.Main.RawStack EdgeSublinearMWIS.Main.ProgramComposition

theorem solution (f g : List Bool → List Bool) (R : Realizer f) (S : Realizer g)
    (hR : ∃C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q)
    (hS : ∃C q : ℕ,0< C ∧ ∀x,S.time x≤ C*(volume x+1)^q ∧ volume (g x)≤ C*(volume x+1)^q)
    (U : Program) :
    ∃ (P : Program) (time : Polynomial ℕ),
      (∀input output : List Bool,f input=false::output →
        ∃s,Runs P input (g output) s ∧ s≤ time.eval (2*output.length+input.length+4)) ∧
      (∀(input ctx middle output : List Bool) (T : ℕ),
        f input=true::((List.replicate ctx.length true++false::ctx)++middle) → Runs U middle output T →
        ∃s,Runs P input (g ((List.replicate ctx.length true++false::ctx)++output)) s ∧
          s≤ time.eval (T+4*ctx.length+2*middle.length+input.length+8)) := by
  obtain ⟨P,time,Q,hP⟩ := polynomial_sandwich R S hR hS (gatedCall U)
  refine ⟨P,time,?_,?_⟩
  · intro input output hf
    have hg := gated_false_runs U output
    rw [← hf] at hg
    obtain ⟨s,hr,ht,hQ⟩ := hP input output _ hg
    refine ⟨s,hr,?_⟩
    convert ht using 1 <;> congr 1 <;> omega
  · intro input ctx middle output T hf hU
    have hg := gated_context_runs U ctx middle output T hU
    change Runs (gatedCall U) (true::((List.replicate ctx.length true++false::ctx)++middle))
      ((List.replicate ctx.length true++false::ctx)++output) _ at hg
    rw [← hf] at hg
    obtain ⟨s,hr,ht,hQ⟩ := hP input _ _ hg
    refine ⟨s,hr,?_⟩
    convert ht using 1 <;> congr 1 <;> omega
end
