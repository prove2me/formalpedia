-- Prove2me | solution 1 for DetDLP.d4_rank_walker_v2_step_poly
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T10:11:26.119115+00:00
-- url     : https://prove2.me/submissions/551756bd-0d65-4db2-a336-7a7a5d925aa5

import Definitions.Def_DetDLP_D4RankWalkerV2
import Theorems.Thm_DetDLP_f9a2_b_mul_poly
import Theorems.Thm_Groundwork_PolyT_pow_unary
import Definitions.Def_ToTuring_Lib_List2
import Theorems.Thm_Groundwork_Unary_of_length
set_option autoImplicit false
open DetDLP DetDLP.D4RankWalker Groundwork DetDLP_W1_Queries OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
attribute [local fun_prop] PolyT.const PolyT.fst PolyT.snd PolyT.prodMk PolyT.map PolyT.any PolyT.filter PolyT.flatMap PolyT.idxOf PolyT.length PolyT.mul PolyT.div PolyT.mod PolyT.comp P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_cons__3a60f43a3b86 P2M_Groundwork_PolyT_cond__4c673073da15 P2M_Groundwork_PolyT_ite__226169acf219 P2M_Groundwork_PolyT_size__c8c8eb1b342f w5_M6Sort.encode_poly w5_M6Sort.cw_poly first_poly more_poly frame_poly

private theorem pack_flat (xs : List Wd) : pack xs = xs.flatMap (fun u => true :: frame u) ++ [false] := by
  induction xs with
  | nil => rfl
  | cons u xs ih => change true :: (Encoding.frame u ++ pack xs) = _; simp [ih,List.flatMap,List.append_assoc]

variable {α : Type} [Enc α]
@[local fun_prop] private theorem pp {g : α → List Wd} (hg : PolyT g) : PolyT (fun x => pack (g x)) := by
  simp only [pack_flat]; fun_prop
@[local fun_prop] private theorem uu {g : α → Wd} (hg : PolyT g) : PolyT (fun x => unpack (g x)) := by
  suffices h : PolyT unpack from h.comp hg
  have fold : PolyT (fun x : Wd => x.foldl scan (false,false,[],[])) := by
    refine PolyT.foldl_add (g := fun _ => scan) (by fun_prop) (by fun_prop) (by unfold scan; fun_prop) ?_
    refine ⟨fun _ => 6, PB.const 6, ?_⟩
    rintro x ⟨k,j,w,ws⟩ e _
    cases k <;> cases j <;> cases e <;> simp [scan,len_pair,len_bool,len_bools,len_cons,len_nil] <;> omega
  unfold unpack; fun_prop
@[local fun_prop] private theorem ff {g : α → Wd} {k : α → ℕ} (h : PolyT g) (hk : PolyT k) : PolyT (fun x => fld (g x) (k x)) := by unfold fld; fun_prop
@[local fun_prop] private theorem nn {g : α → Wd} {k : α → ℕ} (h : PolyT g) (hk : PolyT k) : PolyT (fun x => num (g x) (k x)) := by unfold num; fun_prop
@[local fun_prop] private theorem ii {g : α → Wd} (h : PolyT g) : PolyT (fun x => ints (g x)) := w5_M6Sort.decode_poly.comp h
@[local fun_prop] private theorem mm {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => mapped (g x) (h x)) := by unfold mapped; fun_prop
@[local fun_prop] private theorem rr {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => rowAt (g x) (h x)) := by unfold rowAt; fun_prop
@[local fun_prop] private theorem ss {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => small (g x) (h x)) := by unfold small; apply PolyT.or' <;> apply PolyT.decide_le <;> fun_prop
@[local fun_prop] private theorem aa {g h : α → Wd} {j : α → ℕ} (hg : PolyT g) (hh : PolyT h) (hj : PolyT j) : PolyT (fun x => ask (g x) (h x) (j x)) := by unfold ask; fun_prop
@[local fun_prop] private theorem cc {g h : α → Wd} {p : α → ℕ} (hg : PolyT g) (hp : PolyT p) (hh : PolyT h) : PolyT (fun x => childWord (g x) (p x) (h x)) := by unfold childWord; fun_prop
@[local fun_prop] private theorem cs {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => children (g x) (h x)) := by unfold children; fun_prop
@[local fun_prop] private theorem pw {g : α → Wd} {k : α → ℕ} (hg : PolyT g) (hk : PolyT k) : PolyT (fun x => pow2 (g x) (k x)) := by unfold pow2; fun_prop
@[local fun_prop] private theorem multP {g h : α → ℕ} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => AppendixD4.mult (g x) (h x)) := by unfold AppendixD4.mult; fun_prop
@[local fun_prop] private theorem lossP {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => stepLoss (g x) (h x)) := by unfold stepLoss; fun_prop
@[local fun_prop] private theorem finishP {g a : α → Wd} {n : α → ℕ} (hg : PolyT g) (ha : PolyT a) (hn : PolyT n) : PolyT (fun x => finishWt (g x) (a x) (n x)) := by unfold finishWt; fun_prop
@[local fun_prop] private theorem prodP {g a b : α → Wd} (hg : PolyT g) (ha : PolyT a) (hb : PolyT b) : PolyT (fun x => productV2 (g x) (a x) (b x)) := by
  unfold productV2; apply f9a2_b_mul_poly.2.comp; fun_prop
@[local fun_prop] private theorem iss {g h : α → Wd} (hg : PolyT g) (hh : PolyT h) : PolyT (fun x => issue (g x) (h x)) := by unfold issue pair; fun_prop
@[local fun_prop] private theorem dd {ctx acc : α → Wd} {todo done_ : α → List Wd} {b u n : α → ℕ} (hn : PolyT n) (h₁ : PolyT ctx) (h₂ : PolyT todo) (h₃ : PolyT done_) (h₄ : PolyT b) (h₅ : PolyT u) (h₆ : PolyT acc) : PolyT (fun x => dispatchV2 (ctx x) (todo x) (done_ x) (b x) (u x) (acc x) (n x)) := by unfold dispatchV2; fun_prop
@[local fun_prop] private theorem widthP {g : α → ℕ} (hg : PolyT g) : PolyT (fun x => digitWidth (g x)) := by unfold digitWidth; fun_prop
@[local fun_prop] private theorem radixP {g : α → ℕ} (hg : PolyT g) : PolyT (fun x => 2 ^ digitWidth (g x)) := by
  apply PolyT.pow_unary (PolyT.const 2)
  simpa only [digitWidth, Nat.size_eq_bits_len] using (Unary.of_length (PolyT.bits (f := fun x => g x - 1) (by fun_prop)))
@[local fun_prop] private theorem cnt {ctx acc ans : α → Wd} {todo done_ : α → List Wd} {b u n : α → ℕ} (hn : PolyT n) (h₁ : PolyT ctx) (h₂ : PolyT todo) (h₃ : PolyT done_) (h₄ : PolyT b) (h₅ : PolyT u) (h₆ : PolyT acc) (h₇ : PolyT ans) : PolyT (fun x => countPhaseV2 (ctx x) (todo x) (done_ x) (b x) (u x) (acc x) (ans x) (n x)) := by
  unfold countPhaseV2
  apply P2M_Groundwork_PolyT_ite__226169acf219
  · apply PolyT.decide_and
    · apply PolyT.decide_le <;> fun_prop
    · apply PolyT.decide_lt <;> fun_prop
  · fun_prop
  · fun_prop

theorem solution : Groundwork.PolyT DetDLP.D4RankWalker.walkerStepV2 := by unfold walkerStepV2; fun_prop
