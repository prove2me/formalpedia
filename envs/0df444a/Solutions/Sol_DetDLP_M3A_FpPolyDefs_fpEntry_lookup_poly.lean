-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_lookup_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T02:15:32.29613+00:00
-- url     : https://prove2.me/submissions/fb1f07d3-096b-4945-9254-c8241310e782

import Theorems.Thm_Groundwork_Unary_of_le
import Theorems.Thm_Groundwork_Unary_of_length
import Theorems.Thm_Groundwork_PolyT_len_mul_le
import Definitions.Def_DetDLP_M3A_FpPolyDefs
set_option autoImplicit false
namespace DetDLP.M3A.FpPolyDefs
set_option maxHeartbeats 800000
attribute [local fun_prop] w4_M5Evaluator.n0_poly w4_M5Evaluator.J_poly w4_M5Evaluator.L1_poly w4_M5Evaluator.L2_poly
open Groundwork S8H.PointAddresses S8L.FpPair.Address w4_MulParams w4_M5GraphBounds
attribute [local fun_prop] PolyT.add PolyT.mul PolyT.div PolyT.mod PolyT.sub PolyT.const PolyT.fst PolyT.snd PolyT.comp PolyT.prodMk PolyT.id' P2M_Groundwork_PolyT_ite__226169acf219
variable {α : Type} [Enc α]
attribute [local fun_prop] PolyT.const PolyT.add PolyT.mul PolyT.sub PolyT.length PolyT.getD PolyT.id' PolyT.comp PolyT.bits PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.append m89_enum_words.fields_poly w5_M6Sort.decode_poly w5_M6Sort.cw_poly DetDLP_W1_Queries.frame_poly P2M_Groundwork_PolyT_id__1c5d0f44cc8f
private theorem uadd {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x+g x) := by
  apply (PolyT.append hf hg).congr;intro x;rw [List.replicate_add]
private theorem umul {α} [Enc α] {f g : α → ℕ} (hf : Unary f) (hg : Unary g) : Unary (fun x => f x*g x) := by
  have H := PolyT.flatMap (f:=fun x (_ : Unit) => List.replicate (g x) ()) (PolyT.comp hg (PolyT.fst PolyT.id')) hf
  apply H.congr;intro x;change _ = List.replicate (f x*g x) ();generalize f x=n;induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ,List.flatMap_cons,ih,Nat.succ_mul];rw [← List.replicate_add,Nat.add_comm]
private theorem uconst {α} [Enc α] (k : ℕ) : Unary (fun _ : α => k) := PolyT.const _
attribute [local fun_prop] PolyT.sub PolyT.mul PolyT.div PolyT.mod P2M_Groundwork_PolyT_cons__3a60f43a3b86
private theorem params : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first | unfold d | unfold m | unfold k | unfold pre | unfold sizeField | unfold prec | unfold len
  all_goals dsimp only [d,m,k,pre,prec,len,width,num,field,nums,fld,prime,threshold,groupSize,dFilt];fun_prop
attribute [local fun_prop] PolyT.idxOf PolyT.filter PolyT.sum PolyT.all PolyT.getD PolyT.take PolyT.zip PolyT.testBit PolyT.ofBits PolyT.decide_and PolyT.decide_le PolyT.decide_lt PolyT.and' w4_M5GateOps.portList_poly w4_M5EdgeNat.srcNat_poly P2M_Groundwork_PolyT_cond__4c673073da15 PolyT.pow_unary
private theorem products {xs : α → List ℕ} (h : PolyT xs) : PolyT (fun x => (xs x).foldl (·*·) 1) := by
  obtain ⟨s,hs,_,bound⟩ := PolyT.len_bound h
  refine PolyT.foldl_add h (PolyT.const 1) (by fun_prop) ⟨s,hs,fun x c e he => ?_⟩
  exact (PolyT.len_mul_le c e).trans (Nat.add_le_add_left ((Groundwork.len_le_of_mem he).trans (bound x)) _)
private theorem coeff_poly {b : α → Bool} {z q j : α → ℕ} (hb : PolyT b) (hz : PolyT z) (hq : PolyT q) (hj : Unary j) : PolyT (fun x => coeff (b x) (z x) (q x) (j x)) := by
  have fst := PolyT.fst (PolyT.id' (α:=α × ℕ));have hb' := PolyT.comp hb fst;have hz' := PolyT.comp hz fst
  have r := PolyT.range hj
  have a := products (PolyT.map (f:=fun x i => if b x then z x-i else z x+i) (by fun_prop) r)
  have c := products (PolyT.map (f:=fun (_ : α) (i : ℕ) => i+1) (by fun_prop) r)
  simp only [List.foldl_map] at a c
  have ha : PolyT (fun x => magnitude (b x) (z x) (j x)) := PolyT.div a c
  have hj' : PolyT j := (PolyT.length r).congr (by intro x; simp)
  unfold coeff;fun_prop
open Groundwork
attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.id' PolyT.getD PolyT.toNat' PolyT.decide_eq PolyT.ite' PolyT.ofBits PolyT.comp DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly m89_enum_words.fields_poly
private theorem unLen : Unary len := by
  have um : Unary m := by unfold m; apply Unary.of_length; unfold field fld; fun_prop
  exact uadd (uadd (umul (uconst 4) (umul (uconst 2) um)) (uconst 2)) (uconst 1)
private theorem indPoly {α : Type} [Enc α] {n : α → ℕ} {b : α → Bool} (hn : Unary n) (hb : PolyT b) : PolyT (fun x => indicator (n x) (b x)) := by
  apply w5_M6Sort.encode_poly
  apply PolyT.map (f:=fun x (j : ℕ) => if j=0 then (b x).toNat else 0) _ (PolyT.range hn)
  exact PolyT.ite' (PolyT.decide_eq (PolyT.snd PolyT.id') (PolyT.const 0)) (PolyT.toNat' (PolyT.comp hb (PolyT.fst PolyT.id'))) (PolyT.const 0)
attribute [local fun_prop] PolyT.map PolyT.length PolyT.take PolyT.sum PolyT.mul PolyT.add PolyT.mod PolyT.sub PolyT.bits PolyT.decide_le PolyT.decide_lt w5_M6Sort.decode_poly
private abbrev Q := W × ℕ × W
private theorem unPrec : Unary prec := by
  have um : Unary m := by unfold m; apply Unary.of_length; unfold field fld; fun_prop
  have uk : Unary k := by unfold k width; apply Unary.of_length; unfold threshold num nums field fld; fun_prop
  have uw : Unary (fun w => width (2*(2*m w)*groupSize w+2)) := by unfold width; apply Unary.of_length; unfold groupSize num nums field fld; have hm := params.2.1; fun_prop
  exact uadd (uadd (uconst 2) (umul (umul (uconst 4) um) uk)) (umul (uadd (umul (uconst 4) (umul (uconst 2) um)) (uconst 2)) uw)
private theorem finder {α : Type} [Enc α] {l : α → List ℕ} {p : α → ℕ → Bool} (hl : PolyT l) (hp : PolyT (fun z : α × ℕ => p z.1 z.2)) : PolyT fun x => (l x).findIdx (p x) := by
  have A := PolyT.idxOf (PolyT.const true) (PolyT.map (f:=p) hp hl)
  apply A.congr; intro x; simp [List.idxOf,List.findIdx_map,Function.comp_def]
set_option maxHeartbeats 1200000 in
private theorem look {α : Type} [Enc α] {w : α → W} {s : α → ℕ} {a : α → W} (hw : PolyT w) (hs : PolyT s) (ha : PolyT a) : PolyT fun x => lookup (w x) (s x) (a x) := by
  let i x := s x % m (w x)
  let bs x := blocks (w x)
  let l x := (bs x).getD (i x) []
  let cs x := nums (field (w x) 1)
  have hm := PolyT.comp params.2.1 hw
  have hi : PolyT i := PolyT.mod hs hm
  have hb : PolyT bs := by unfold bs blocks nums field fld; fun_prop
  have hl : PolyT l := PolyT.getD hb hi (PolyT.const [])
  have hc : PolyT cs := by unfold cs nums field fld; fun_prop
  have h0 := PolyT.getD hc (PolyT.mul (PolyT.const 2) hi) (PolyT.const 0)
  have h1 := PolyT.getD hc (PolyT.add (PolyT.mul (PolyT.const 2) hi) (PolyT.const 1)) (PolyT.const 0)
  have hp : PolyT (fun x => prime (w x)) := by unfold prime num nums field fld; fun_prop
  let r x := (l x).findIdx (fun v => decide (((cs x).getD (2*i x) 0*v+(cs x).getD (2*i x+1) 0)%prime (w x)=PolyT.bval (a x)))
  have f := PolyT.fst (PolyT.id' (α:=α × ℕ))
  have g := PolyT.snd (PolyT.id' (α:=α × ℕ))
  have hash := PolyT.ofBits ha
  have pred := PolyT.decide_eq (PolyT.mod (PolyT.add (PolyT.mul (PolyT.comp h0 f) g) (PolyT.comp h1 f)) (PolyT.comp hp f)) (PolyT.comp hash f)
  have hr : PolyT r := finder (p:=fun x v => decide (((cs x).getD (2*i x) 0*v+(cs x).getD (2*i x+1) 0)%prime (w x)=PolyT.bval (a x))) hl pred
  let z x := num (field (w x) 3) (((bs x).take (i x) |>.map List.length).sum + r x)
  have hz : PolyT z := by unfold z num nums field fld; fun_prop
  have ul := PolyT.comp (show PolyT (fun w => List.replicate (len w) ()) from unLen) hw
  have up := PolyT.comp (show PolyT (fun w => List.replicate (prec w) ()) from unPrec) hw
  have hq := PolyT.pow_unary (PolyT.const 2) (show Unary (fun x => prec (w x)) from up)
  have hlen := PolyT.comp params.2.2.2.2.2.2 hw
  have ul' := PolyT.comp ul f
  have hu : Unary (fun t : α × ℕ => min t.2 (len (w t.1))) := Unary.of_le (f:=fun t : α × ℕ => min t.2 (len (w t.1))) (g:=fun t => len (w t.1)) ul' (by simp only [Nat.min_def]; have := PolyT.comp hlen f; fun_prop) (fun t => min_le_right ..)
  have hc' := coeff_poly (PolyT.comp (PolyT.decide_le (PolyT.mul (PolyT.const 2) hm) hs) f) (PolyT.comp hz f) (PolyT.comp hq f) hu
  have C := PolyT.map (f:=fun x j => coeff (decide (2*m (w x) ≤ s x)) (z x) (2^prec (w x)) (min j (len (w x)))) hc' (PolyT.range (show Unary (fun x => len (w x)) from ul))
  have H := (w5_M6Sort.encode_poly C).congr (g:=fun x => encodeNatListBin ((List.range (len (w x))).map (coeff (decide (2*m (w x) ≤ s x)) (z x) (2^prec (w x))))) (by intro x; congr 1; apply List.map_congr_left; intro j hj; rw [Nat.min_eq_left (List.mem_range.mp hj).le])
  have F := indPoly (n:=fun x => len (w x)) ul (PolyT.const false)
  have R := PolyT.ite' (PolyT.decide_lt hr (PolyT.length hl)) H F
  exact R
theorem fpEntry_lookup_poly : PolyT (fun z : List Bool × ℕ × List Bool => lookup z.1 z.2.1 z.2.2) := look (by fun_prop) (by fun_prop) (by fun_prop)
end DetDLP.M3A.FpPolyDefs
abbrev solution := DetDLP.M3A.FpPolyDefs.fpEntry_lookup_poly
