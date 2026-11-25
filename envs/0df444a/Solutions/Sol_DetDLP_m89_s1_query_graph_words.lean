-- Prove2me | solution 1 for DetDLP.m89_s1_query_graph_words
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T03:58:51.19667+00:00
-- url     : https://prove2.me/submissions/dbf9e430-6bc7-4130-a10f-9473c811c983

import Definitions.Def_DetDLP_W1_Queries
import Theorems.Thm_DetDLP_s8c_fp_elem_and_pair_queries
import Theorems.Thm_DetDLP_s8c_fp_moment_queries
import Theorems.Thm_DetDLP_s8c_ec_order_and_elem_queries
import Theorems.Thm_DetDLP_s8c_ec_pair_and_moment_queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1 DetDLP.S8C Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace S8CDispatch
abbrev Word := List Bool
abbrev Machine := Word → Word
def tag (w : Word) : ℕ := PolyT.bval (DetDLP_W1_Queries.first w)
@[simp] theorem tag_word (t : ℕ) (base : Word) (payload : List Word) :
    tag (queryWord t base payload) = t := by simp [tag,queryWord]
@[simp] theorem port_first (w : Word) (v : ℕ) (a : Word) :
    DetDLP_W1_Queries.first (encodePortQuery w v a) = w := by simp [encodePortQuery]
def choose (t : ℕ) (a b c d : Word) : Word :=
  if t = 1 then b else if t = 3 then a else if t = 5 then a else if t = 0 then c else if t = 4 then c else d
attribute [local fun_prop] Groundwork.PolyT.const P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 DetDLP_W1_Queries.first_poly
@[local fun_prop] theorem tag_poly {f : List Bool → List Bool} (hf : PolyT f) : PolyT (fun w => tag (f w)) := by unfold tag; fun_prop
theorem choose_poly {t : Word → ℕ} {a b c d : List Bool → List Bool} (ht : PolyT t) (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) :
    PolyT (fun w => choose (t w) (a w) (b w) (c w) (d w)) := by unfold choose; fun_prop

theorem transport {f g F G : Machine} {l L : ℕ} {w : Word} {b n : ℕ}
    (h : Realizes f g l w b n) (hl : l ≤ L) (hf : F w = f w)
    (hg : ∀ v a, G (encodePortQuery w v a) = g (encodePortQuery w v a)) : Realizes F G L w b n := by
  rcases h with ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv,hd,hsiz,hpoly,hm,hp⟩
  refine ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv.trans (Nat.pow_le_pow_right (by omega) hl),hd,?_,?_,hf.trans hm,?_⟩
  · exact hsiz.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
  · exact hpoly.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl))
  · intro v a
    obtain ⟨hz,ha⟩ := hp v a
    exact ⟨hz.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl)),(hg _ _).trans ha⟩

theorem covered {w b n} (h : Query w b n) : ∃ t base payload, w = queryWord t base payload ∧ t < 7 := by
  cases h <;> exact ⟨_,_,_,rfl,by decide⟩
end S8CDispatch
open S8CDispatch

theorem solution : GadgetLaws → ∃ (make port : List Bool → List Bool) (L : ℕ), PolyT make ∧ PolyT port ∧ ∀ w b n, Query w b n → Realizes make port L w b n := by
  intro h
  obtain ⟨f1,g1,l1,hf1,hg1,c1⟩ := DetDLP.s8c_fp_elem_and_pair_queries h
  obtain ⟨f2,g2,l2,hf2,hg2,c2⟩ := DetDLP.s8c_fp_moment_queries h
  obtain ⟨f3,g3,l3,hf3,hg3,c3⟩ := DetDLP.s8c_ec_order_and_elem_queries h
  obtain ⟨f4,g4,l4,hf4,hg4,c4⟩ := DetDLP.s8c_ec_pair_and_moment_queries h
  let F := fun w => choose (tag w) (f1 w) (f2 w) (f3 w) (f4 w)
  let G := fun w => choose (tag (DetDLP_W1_Queries.first w)) (g1 w) (g2 w) (g3 w) (g4 w)
  refine ⟨F,G,l1+l2+l3+l4,choose_poly (tag_poly PolyT.id') hf1 hf2 hf3 hf4,choose_poly (tag_poly DetDLP_W1_Queries.pq1) hg1 hg2 hg3 hg4,?_⟩
  intro w b n hw
  obtain ⟨t,base,payload,rfl,ht⟩ := covered hw
  interval_cases t
  · exact transport (c3 0 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c2 1 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c4 2 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c1 3 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c3 4 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c1 5 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · exact transport (c4 6 (by decide) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
