-- Prove2me | solution 2 for DetDLP.s8c_ec_pair_and_moment_queries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-25T14:07:57.166308+00:00
-- url     : https://prove2.me/submissions/63dfb01f-e525-4917-ae9d-60e80fe2e93a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_ec_moment_uniform_query_program
import Theorems.Thm_DetDLP_s8i_ec_pair_query

set_option autoImplicit false
open DetDLP

private theorem tag2Exact : S8C.GadgetLaws → S8C.TagSpec [2] := by
  intro _
  obtain ⟨make, port, L, _, hm, hp, hquery⟩ := ec_moment_uniform_query_program
  exact S8I.ECMoment.tagIntro make port L hm hp hquery

section
set_option autoImplicit false
open DetDLP DetDLP.M89S1 DetDLP.S8C Groundwork
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

namespace DetDLP.S8C.ECPairMomentJoin

private abbrev Word := List Bool

private def tag (w : Word) : ℕ := PolyT.bval (DetDLP_W1_Queries.first w)

@[local simp] private theorem tag_word (i : ℕ) (base : Word) (payload : List Word) :
    tag (queryWord i base payload) = i := by simp [tag, queryWord]

@[local simp] private theorem port_first (w : Word) (v : ℕ) (a : Word) :
    DetDLP_W1_Queries.first (encodePortQuery w v a) = w := by simp [encodePortQuery]

private def dispatch (i : ℕ) (moment pair : Word) : Word :=
  if i = 2 then moment else pair

attribute [local fun_prop] Groundwork.PolyT.const P2M_Groundwork_PolyT_id__1c5d0f44cc8f
  P2M_Groundwork_PolyT_ite__226169acf219 DetDLP_W1_Queries.first_poly

private theorem tag_poly {f : Word → Word} (hf : PolyT f) : PolyT (fun w => tag (f w)) := by
  unfold tag
  fun_prop

private theorem dispatch_poly {i : Word → ℕ} {moment pair : Word → Word}
    (hi : PolyT i) (hm : PolyT moment) (hp : PolyT pair) :
    PolyT (fun w => dispatch (i w) (moment w) (pair w)) := by
  unfold dispatch
  fun_prop

private theorem transport {make port make' port' : Word → Word} {l L b n : ℕ} {w : Word}
    (h : Realizes make port l w b n) (hl : l ≤ L) (hm : make' w = make w)
    (hp : ∀ v a, port' (encodePortQuery w v a) = port (encodePortQuery w v a)) :
    Realizes make' port' L w b n := by
  rcases h with ⟨s, G, T, k, ext, R, hpar, hcard, hs, hb, he, hv, hd, hsize, hpoly, hmake, hport⟩
  refine ⟨s, G, T, k, ext, R, hpar, hcard, hs, hb, he,
    hv.trans (Nat.pow_le_pow_right (by omega) hl), hd, ?_, ?_, hm.trans hmake, ?_⟩
  · exact hsize.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hl))
  · exact hpoly.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl))
  · intro v a
    obtain ⟨hz, ha⟩ := hport v a
    exact ⟨hz.trans (Nat.mul_le_mul hl (Nat.pow_le_pow_right (by omega) hl)), (hp _ _).trans ha⟩

theorem join (htag2 : GadgetLaws → TagSpec [2]) : GadgetLaws → TagSpec [2, 6] := by
  intro laws
  obtain ⟨make2, port2, l2, hm2, hp2, h2⟩ := htag2 laws
  obtain ⟨make6, port6, l6, hm6, hp6, h6⟩ := DetDLP.s8i_ec_pair_query laws
  let make := fun w => dispatch (tag w) (make2 w) (make6 w)
  let port := fun z => dispatch (tag (DetDLP_W1_Queries.first z)) (port2 z) (port6 z)
  refine ⟨make, port, l2 + l6, dispatch_poly (tag_poly PolyT.id') hm2 hm6,
    dispatch_poly (tag_poly DetDLP_W1_Queries.pq1) hp2 hp6, ?_⟩
  intro i hi base payload b n hw
  rcases (show i = 2 ∨ i = 6 by simpa using hi) with rfl | rfl
  · exact transport (h2 2 (by simp) base payload b n hw) (by omega)
      (by simp [make, dispatch]) (by intro v a; simp [port, dispatch])
  · exact transport (h6 6 (by simp) base payload b n hw) (by omega)
      (by simp [make, dispatch]) (by intro v a; simp [port, dispatch])

end DetDLP.S8C.ECPairMomentJoin
end

theorem solution : DetDLP.S8C.GadgetLaws → DetDLP.S8C.TagSpec [2,6] :=
  DetDLP.S8C.ECPairMomentJoin.join tag2Exact
