-- Prove2me | solution 1 for DetDLP.s8c_fp_elem_and_pair_queries
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:43:15.950036+00:00
-- url     : https://prove2.me/submissions/241866a6-7983-4d71-aecc-07a964585aa5

import Theorems.Thm_DetDLP_s8c_fp_elem_query
import Theorems.Thm_DetDLP_s8c_fp_pair_query
import Definitions.Def_DetDLP_W1_Queries
set_option autoImplicit false
open DetDLP DetDLP.M89S1 DetDLP.S8C Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
namespace S8CFpDispatch
abbrev Word := List Bool
abbrev Machine := Word → Word
def tag (w : Word) : ℕ := PolyT.bval (DetDLP_W1_Queries.first w)
@[simp] theorem tag_word (t : ℕ) (base : Word) (payload : List Word) : tag (queryWord t base payload) = t := by simp [tag,queryWord]
@[simp] theorem port_first (w : Word) (v : ℕ) (a : Word) : DetDLP_W1_Queries.first (encodePortQuery w v a) = w := by simp [encodePortQuery]
def choose (t : ℕ) (a b c d e : Word) : Word := if t = 3 then a else b
attribute [local fun_prop] Groundwork.PolyT.const P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 DetDLP_W1_Queries.first_poly
@[local fun_prop] theorem tag_poly {f : List Bool → List Bool} (hf : PolyT f) : PolyT (fun w => tag (f w)) := by unfold tag; fun_prop
theorem choose_poly {t : Word → ℕ} {a b c d e : List Bool → List Bool} (ht : PolyT t) (ha : PolyT a) (hb : PolyT b) (hc : PolyT c) (hd : PolyT d) (he : PolyT e) : PolyT (fun w => choose (t w) (a w) (b w) (c w) (d w) (e w)) := by unfold choose; fun_prop
theorem transport {f g F G : Machine} {l L : ℕ} {w : Word} {b n : ℕ} (h : Realizes f g l w b n) (hl : l ≤ L) (hf : F w = f w) (hg : ∀ v a, G (encodePortQuery w v a) = g (encodePortQuery w v a)) : Realizes F G L w b n := by
  rcases h with ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv,hd,hsiz,hpoly,hm,hp⟩
  refine ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv.trans (Nat.pow_le_pow_right (by omega) hl),hd,?_,?_,hf.trans hm,?_⟩
  · exact hsiz.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
  · exact hpoly.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl))
  · intro v a; obtain ⟨hz,ha⟩ := hp v a; exact ⟨hz.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl)),(hg _ _).trans ha⟩
theorem covered {w b n} (h : Query w b n) : ∃ t base payload, w = queryWord t base payload ∧ t < 7 := by cases h <;> exact ⟨_,_,_,rfl,by decide⟩
end S8CFpDispatch
open S8CFpDispatch
theorem solution : GadgetLaws → TagSpec [3,5] := by
  intro h
  obtain ⟨f3,g3,l3,hf3,hg3,c3⟩ := DetDLP.s8c_fp_elem_query h
  obtain ⟨f5,g5,l5,hf5,hg5,c5⟩ := DetDLP.s8c_fp_pair_query h
  let F := fun w => choose (tag w) (f3 w) (f5 w) ([] : Word) ([] : Word) ([] : Word)
  let G := fun w => choose (tag (DetDLP_W1_Queries.first w)) (g3 w) (g5 w) ([] : Word) ([] : Word) ([] : Word)
  refine ⟨F,G,l3+l5,choose_poly (tag_poly PolyT.id') hf3 hf5 (Groundwork.PolyT.const []) (Groundwork.PolyT.const []) (Groundwork.PolyT.const []),
    choose_poly (tag_poly DetDLP_W1_Queries.pq1) hg3 hg5 (Groundwork.PolyT.const []) (Groundwork.PolyT.const []) (Groundwork.PolyT.const []),?_⟩
  intro t ht base payload b n hw
  simp only [List.mem_cons, List.mem_singleton] at ht
  rcases ht with ht | ht
  · subst t
    exact transport (c3 3 (by simp) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
  · rcases ht with rfl | hnil
    · exact transport (c5 5 (by simp) base payload b n hw) (by omega) (by simp [F,choose]) (by intro v a; simp [G,choose])
    · simp at hnil
