-- Prove2me | solution 1 for DetDLP.s8c_ec_order_and_elem_queries
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:41:27.594802+00:00
-- url     : https://prove2.me/submissions/9d2ef465-7d0d-478b-99e3-f1fccd7ba3f5

import Theorems.Thm_DetDLP_s8h_ec_order_query
import Theorems.Thm_DetDLP_s8h_ec_elem_query
import Definitions.Def_DetDLP_W1_Queries

set_option autoImplicit false
open DetDLP DetDLP.M89S1 DetDLP.S8C Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace ECOrderElemDispatch
abbrev W := List Bool
def tag (w : W) := PolyT.bval (DetDLP_W1_Queries.first w)
@[simp] theorem tag_word (t : ℕ) (b : W) (p : List W) : tag (queryWord t b p) = t := by simp [tag,queryWord]
@[simp] theorem nested (w : W) (v : ℕ) (a : W) : DetDLP_W1_Queries.first (encodePortQuery w v a) = w := by simp [encodePortQuery]

def dispatch (key f g : W → W) (w : W) := if tag (key w) = 0 then f w else g w
attribute [local fun_prop] PolyT.const P2M_Groundwork_PolyT_id__1c5d0f44cc8f P2M_Groundwork_PolyT_ite__226169acf219 DetDLP_W1_Queries.first_poly
theorem uniform {key f g : W → W} (hk : PolyT key) (hf : PolyT f) (hg : PolyT g) : PolyT (dispatch key f g) := by unfold dispatch tag; fun_prop

theorem transport {f g F G : W → W} {l L : ℕ} {w : W} {b n : ℕ} (h : Realizes f g l w b n) (hl : l ≤ L) (hf : F w = f w) (hg : ∀ v a, G (encodePortQuery w v a) = g (encodePortQuery w v a)) : Realizes F G L w b n := by
  rcases h with ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv,hd,hsiz,hpoly,hm,hp⟩
  refine ⟨s,N,T,k,e,R,hpar,hcard,hs,hb,he,hv.trans (Nat.pow_le_pow_right (by omega) hl),hd,?_,?_,hf.trans hm,?_⟩
  · exact hsiz.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
  · exact hpoly.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl))
  · intro v a; obtain ⟨hz,ha⟩ := hp v a; exact ⟨hz.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl)),(hg _ _).trans ha⟩
end ECOrderElemDispatch

open ECOrderElemDispatch
theorem solution : GadgetLaws → TagSpec [0,4] := by
  intro h
  obtain ⟨f,g,l,hf,hg,h0⟩ := DetDLP.s8h_ec_order_query h
  obtain ⟨F,G,L,hF,hG,h4⟩ := DetDLP.s8h_ec_elem_query h
  refine ⟨dispatch id f F,dispatch DetDLP_W1_Queries.first g G,l+L,uniform PolyT.id' hf hF,
    uniform DetDLP_W1_Queries.pq1 hg hG,?_⟩
  intro t ht base payload b n hw
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl | rfl
  · exact transport (h0 0 (by simp) base payload b n hw) (by omega) (by simp [dispatch]) (by intros; simp [dispatch])
  · exact transport (h4 4 (by simp) base payload b n hw) (by omega) (by simp [dispatch]) (by intros; simp [dispatch])
