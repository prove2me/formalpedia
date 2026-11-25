-- Prove2me | solution 1 for DetDLP.d4_small_regime_terminal_machine
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T06:25:17.187399+00:00
-- url     : https://prove2.me/submissions/193e73bc-8a38-4a18-9857-940e9bf1c358

import Theorems.Thm_DetDLP_d4_small_input_length
import Theorems.Thm_DetDLP_d4_small_kernel_word_function
import Theorems.Thm_DetDLP_m14a_separator_edge_budget
import Definitions.Def_DetDLP_D4Slice
import Theorems.Thm_DetDLP_f6a_small_z_readout_poly
import Theorems.Thm_DetDLP_f6b_terminal_instance_decode_poly
import Definitions.Def_DetDLP_PolyTBridge
set_option autoImplicit false
set_option maxHeartbeats 550000
open Groundwork DetDLP DetDLP.D4Plan DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
namespace D4SR
abbrev W := List Bool
attribute [local fun_prop] PolyT.comp PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.div PolyT.mul PolyT.bits PolyT.bval' PolyT.flatMap PolyT.map PolyT.length first_poly more_poly D4Slice.field_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_ite__226169acf219
private def clock : ℕ → W → W
  | 0,_ => [true]
  | k+1,w => w.flatMap (fun _ => clock k w)
private theorem clockP (k : ℕ) : PolyT (clock k) := by
  induction k with
  | zero => exact PolyT.const _
  | succ k ih => exact PolyT.flatMap (f:=fun (w : W) (_ : Bool) => clock k w) (ih.comp (PolyT.fst PolyT.id')) PolyT.id'
private theorem cl (k : ℕ) (w : W) : (clock k w).length = w.length^k := by induction k <;> simp_all [clock,List.length_flatMap,pow_succ,Nat.mul_comm]
private def repeatW (n : ℕ) (w : W) := (List.replicate n true).flatMap (fun _ => w)
@[local fun_prop] private theorem repeatP {α : Type} [Enc α] {w : α → W} (hw : PolyT w) (n : ℕ) : PolyT (fun x => repeatW n (w x)) := PolyT.flatMap (hw.comp (PolyT.fst PolyT.id')) (PolyT.const _)
private theorem rl (n : ℕ) (w : W) : (repeatW n w).length = n*w.length := by simp [repeatW,List.length_flatMap]
private def chooseW (key : W → ℕ) (f : ℕ → W → W) : ℕ → W → W
  | 0,_ => []
  | n+1,w => if key w=n then f n w else chooseW key f n w
private theorem chooseP {key : W → ℕ} (hk : PolyT key) {f : ℕ → W → W} (hf : ∀ n,PolyT (f n)) (n : ℕ) : PolyT (chooseW key f n) := by
  induction n with
  | zero => exact PolyT.const _
  | succ n ih => change PolyT (fun w => if key w=n then f n w else chooseW key f n w); fun_prop
private theorem chooseE {key : W → ℕ} {f : ℕ → W → W} {n : ℕ} {w : W} (h : key w < n) : chooseW key f n w = f (key w) w := by induction n with | zero => omega | succ n ih => rw [chooseW]; split <;> rename_i H; simp [H]; exact ih (by omega)
private def F (i : ℕ) (w : W) := D4Slice.field i (F6B.decode w)
@[local fun_prop] private theorem fp (i : ℕ) : PolyT (F i) := D4Slice.field_poly i f6b_terminal_instance_decode_poly.1
private def verts (w : W) := D4Slice.field 2 (D4Slice.field 1 w)
@[local fun_prop] private theorem vp : PolyT verts := D4Slice.field_poly 2 (D4Slice.field_poly 1 PolyT.id')
private def wid (e p l : ℕ) (w : W) := List.replicate (e+1+p) true ++ repeatW (p+Nat.clog 2 l) (verts w)
@[local fun_prop] private theorem widP (e p l : ℕ) : PolyT (wid e p l) := by unfold wid; fun_prop
private def base (e p l : ℕ) (w : W) : ℕ := 2^(wid e p l w).length
@[local fun_prop] private theorem baseP (e p l : ℕ) : PolyT (base e p l) := PolyT.pow_unary (PolyT.const 2) (Unary.of_length (widP e p l))
private def bank (s e p l : ℕ) (w : W) : List W :=
  let d := F 0 w; let nv := F 2 w; let r := F 5 w; let c := F 6 w; let B := base e p l w
  List.replicate 8 [] ++ [(2^e:ℕ).bits,nv,[],[],(1:ℕ).bits,[],[],[],(1:ℕ).bits,(1:ℕ).bits,(2^e:ℕ).bits] ++
    [d,r,c,(PolyT.bval c / PolyT.bval r).bits,(B-1).bits,B.bits,(B-1-2).bits] ++ List.replicate s []
@[local fun_prop] private theorem bankP (s e p l : ℕ) : PolyT (bank s e p l) := by unfold bank; fun_prop
private def key (i : ℕ) (w : W) := PolyT.bval (F i w)
private theorem keyP (i : ℕ) : PolyT (key i) := by unfold key; fun_prop
private def fuel (S K : ℕ) (w : W) := repeatW K (clock K (List.replicate (S+1) true ++ F 0 w))
@[local fun_prop] private theorem fuelP (S K : ℕ) : PolyT (fuel S K) := by unfold fuel; apply repeatP; apply (clockP K).comp; fun_prop
private def fixed (sim : List W × W → W) (s S K e p l : ℕ) (w : W) := F6AReadout.readout (sim (bank s e p l w,fuel S K w),(base e p l w).bits,(2^p:ℕ).bits,List.replicate l true)
private theorem fixedP (sim : List W × W → W) (hs : PolyT sim) (s S K e p l : ℕ) : PolyT (fixed sim s S K e p l) := by unfold fixed; apply f6a_small_z_readout_poly.1.comp; fun_prop
private def full (sim : List W × W → W) (s K C L : ℕ) :=
  chooseW (fun w => PolyT.bval (D4Slice.field 5 w)) (fun S => chooseW (key 1) (fun e => chooseW (key 3) (fun p => chooseW (key 4) (fun l => fixed sim s S K e p l) (C*2*S+1)) (S+1)) (3*S+1)) (2^L+1)
private theorem fullP (sim : List W × W → W) (hs : PolyT sim) (s K C L : ℕ) : PolyT (full sim s K C L) := by
  apply chooseP (by fun_prop); intro S; apply chooseP (keyP 1); intro e; apply chooseP (keyP 3); intro p; apply chooseP (keyP 4); exact fixedP sim hs s S K e p
private theorem compBound (a b : ℕ) : ∃ d : ℕ, ∀ i j : ℕ, i ≤ a*(j+1)^a → polyBound b i ≤ polyBound d j := by
  let t := b*(a+1)^b
  let d := t+a*b
  refine ⟨d,?_⟩; intro i j h
  have h1 : 1 ≤ (j+1)^a := Nat.one_le_pow _ _ (by omega)
  have h2 : i+1 ≤ (a+1)*(j+1)^a := by nlinarith only [h,h1]
  have h3 := Nat.mul_le_mul_left b (Nat.pow_le_pow_left h2 b)
  rw [mul_pow,← pow_mul,← Nat.mul_assoc] at h3
  have h4 : b*(i+1)^b ≤ d*(j+1)^d := h3.trans (Nat.mul_le_mul (show b*(a+1)^b ≤ d by dsimp [d,t]; omega) (Nat.pow_le_pow_right (by omega) (by dsimp [d]; omega)))
  unfold polyBound; exact_mod_cast h4
end D4SR
open D4SR

theorem solution (C c : ℕ) (hC : 0 < C) (hc : 0 < c) (E : PrimitiveMachine) (o : Fin E.tapeCount) (L₀ : ℕ) :
    ∃ (M : PrimitiveMachine) (om : Fin M.tapeCount) (K : ℕ), ∀ x : Input C c,
      Nat.clog 2 x.S < L₀ → entry x E o → RunsWithin M om (input x) (answer x) (polyBound K (size x)) (polyBound K (size x)) := by
  obtain ⟨s,K,sim,sp,run⟩ := d4_small_kernel_word_function C c L₀ E o
  obtain ⟨M,om,b,exec⟩ := PolyTBridge.polyT_listBool_runsWithin _ (fullP sim sp s K C L₀)
  obtain ⟨a,ha⟩ := d4_small_input_length C c L₀ hc
  obtain ⟨d,hd⟩ := compBound a b
  refine ⟨M,om,d,?_⟩; intro x hl he
  have wlen := hd _ _ (ha x hl)
  have sem := PolyTBridge.runsWithin_mono_local (exec (input x)) wlen wlen
  suffices out : full sim s K C L₀ (input x) = answer x by rwa [out] at sem
  let r := x.G.nV+3
  let pairs := (List.finRange x.G.nE).map fun e => ((x.G.endpoints e).1.val,(x.G.endpoints e).2.val)
  let code := Nat.ofDigits r (pairs.flatMap fun xy => [xy.1,xy.2])+r^(2*pairs.length)
  let ww := x.G.nE+x.G.nV*(x.p+Nat.clog 2 x.l)+1+x.p
  have dec : F6B.decode (input x) = Encoding.encodeList id [x.desc,x.G.nE.bits,x.G.nV.bits,x.p.bits,x.l.bits,r.bits,code.bits] := f6b_terminal_instance_decode_poly.2 ..
  have src : D4Slice.field 5 (input x) = SqrtLogSpace.countWord x.S := by simp [input,encodeTerminalBTNInstance,D4Slice.field]
  have vlen : (verts (input x)).length = x.G.nV := by simp [verts,input,encodeTerminalBTNInstance,BipartiteMultigraph.encode,D4Slice.field]
  have key1 : key 1 (input x) = x.G.nE := by simp [key,F,dec,D4Slice.field,PolyT.bval_bits]
  have key3 : key 3 (input x) = x.p := by simp [key,F,dec,D4Slice.field,PolyT.bval_bits]
  have key4 : key 4 (input x) = x.l := by simp [key,F,dec,D4Slice.field,PolyT.bval_bits]
  have s₀ : x.S ≤ 2^L₀ := (Nat.clog_le_iff_le_pow (b:=2) (by decide)).mp hl.le
  obtain ⟨hβ,hE⟩ := m14a_separator_edge_budget x.spec
  have hmb : x.m ≤ 2*x.S := by have hm := Nat.mul_le_mul_left (4*x.m) x.hk; omega
  have ls := x.lm.trans (Nat.mul_le_mul_left C hmb)
  let q : List Bool → ℕ := fun w => PolyT.bval (D4Slice.field 5 w)
  have hq : q (input x) = x.S := by simp only [q,src,decode_count]
  have select (g : List Bool → ℕ) (xw : List Bool) (n u : ℕ) (eq : g xw=u) (lt : u<n) (f : ℕ → List Bool → List Bool) : chooseW g f n xw = f u xw := by
    subst u; exact chooseE (key:=g) (f:=f) (w:=xw) lt
  unfold full
  rw [select q (input x) (2^L₀+1) x.S hq (by omega)]
  rw [select (key 1) (input x) (3*x.S+1) x.G.nE key1 (by omega)]
  rw [select (key 3) (input x) (x.S+1) x.p key3 (by have := x.pS; omega)]
  rw [select (key 4) (input x) (C*2*x.S+1) x.l key4 (by nlinarith only [ls])]
  have hwidth : (wid x.G.nE x.p x.l (input x)).length = ww := by
    rw [wid,List.length_append,List.length_replicate,rl,vlen]; dsimp only [ww]; ring
  have bas : base x.G.nE x.p x.l (input x) = 2^ww := congrArg (fun n : ℕ => 2^n) hwidth
  have hdesc : F 0 (input x) = x.desc := by simp only [F,dec,D4Slice.field,first_cons,id_eq]
  have ck : (fuel x.S K (input x)).length = K*(size x+1)^K := by
    rw [fuel,rl,cl,List.length_append,List.length_replicate,hdesc,Nat.add_right_comm x.S 1 x.desc.length]; rfl
  obtain ⟨z,hz,out⟩ := run x hl he (fuel x.S K (input x)) ck.ge
  have word : sim (bank s x.G.nE x.p x.l (input x),fuel x.S K (input x)) = z.bits := by
    rw [← hz]; congr 2
    simp [bank,F,dec,D4Slice.field,PolyT.bval_bits,bas,ww,r,code,pairs]
  unfold fixed; rw [word,bas,f6a_small_z_readout_poly.2]; simpa [answer,D4Plan.Z] using out
