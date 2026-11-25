-- Prove2me | solution 1 for DetDLP.M3A.FpPolyDefs.fpEntry_compose
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T01:34:15.898891+00:00
-- url     : https://prove2.me/submissions/9da60f79-cbf7-400f-a8b2-32888f94c424

import Theorems.Thm_DetDLP_M3A_FpPolyDefs_numeric_uniform
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
open Groundwork
attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.id' PolyT.getD PolyT.toNat' PolyT.decide_eq PolyT.ite' PolyT.ofBits PolyT.comp DetDLP_W1_Queries.first_poly DetDLP_W1_Queries.more_poly m89_enum_words.fields_poly
private theorem unLen : Unary len := by
  have um : Unary m := by unfold m; apply Unary.of_length; unfold field fld; fun_prop
  exact uadd (uadd (umul (uconst 4) (umul (uconst 2) um)) (uconst 2)) (uconst 1)
private theorem indPoly {α : Type} [Enc α] {n : α → ℕ} {b : α → Bool} (hn : Unary n) (hb : PolyT b) : PolyT (fun x => indicator (n x) (b x)) := by
  apply w5_M6Sort.encode_poly
  apply PolyT.map (f:=fun x (j : ℕ) => if j=0 then (b x).toNat else 0) _ (PolyT.range hn)
  exact PolyT.ite' (PolyT.decide_eq (PolyT.snd PolyT.id') (PolyT.const 0)) (PolyT.toNat' (PolyT.comp hb (PolyT.fst PolyT.id'))) (PolyT.const 0)
theorem fpEntry_compose
    (hsup : PolyT d ∧ PolyT m ∧ PolyT k ∧ PolyT pre ∧ PolyT sizeField ∧ PolyT prec ∧ PolyT len)
    (hord : PolyT (fun z : List Bool × ℕ × List Bool => indicator (len z.1) (ordinary z.1 z.2.1 z.2.2)))
    (hlu : PolyT (fun z : List Bool × ℕ × List Bool => lookup z.1 z.2.1 z.2.2)) : PolyT fpEntry := by
  obtain ⟨hd,hm,hk,hp,_,_,_⟩ := hsup
  have w : PolyT DetDLP_W1_Queries.first := DetDLP_W1_Queries.pq1
  have v : PolyT (fun z : W => PolyT.bval (DetDLP_W1_Queries.second z)) := by unfold DetDLP_W1_Queries.second; fun_prop
  have a : PolyT DetDLP_W1_Queries.third := by unfold DetDLP_W1_Queries.third DetDLP_W1_Queries.second; fun_prop
  have ⟨ng0,_,_,_,_⟩ := numeric_uniform hm hd hk (PolyT.length hp) (PolyT.const 0)
  have ng := PolyT.comp ng0 w
  have ar := PolyT.sub ng (PolyT.mul (PolyT.const 4) (PolyT.comp hm w))
  have eqA : PolyT (fun z => equal (DetDLP_W1_Queries.third z)) := by
    unfold equal bit; apply PolyT.all _ a; have := PolyT.comp a (PolyT.fst (PolyT.id' (α:=W × Bool))); fun_prop
  have A := PolyT.comp hord (PolyT.prodMk w (PolyT.prodMk v a))
  have B := PolyT.comp hlu (PolyT.prodMk w (PolyT.prodMk (PolyT.sub v ar) a))
  have ul := PolyT.comp (show PolyT (fun z => List.replicate (len z) ()) from unLen) w
  have C := indPoly (n:=fun z => len (DetDLP_W1_Queries.first z)) ul eqA
  have R := PolyT.ite' (PolyT.decide_lt v ar) A (PolyT.ite' (PolyT.decide_lt v ng) B C)
  exact R
end DetDLP.M3A.FpPolyDefs
abbrev solution := DetDLP.M3A.FpPolyDefs.fpEntry_compose
