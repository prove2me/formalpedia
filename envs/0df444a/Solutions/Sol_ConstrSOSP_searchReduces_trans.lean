-- Prove2me | solution 1 for ConstrSOSP.searchReduces_trans
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Weiqiang
-- created : 2026-11-13T20:48:27.620059+00:00
-- url     : https://prove2.me/submissions/fc17b254-4497-429f-b448-0048029a0bd7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CookPvsNP_polyTimeComputable_comp
import Theorems.Thm_CookPvsNP_polyTimeComputable_pairSnd
import Theorems.Thm_CookPvsNP_stack_transfer
import Theorems.Thm_CookPvsNP_stack_program_polytime
import Theorems.Thm_CookPvsNP_polynomial_absorb
import Theorems.Thm_CookPvsNP_polyTimeComputable_tagged_pair
import Definitions.Def_CardinalMatching_SearchReduces

open CookPvsNP CardinalMatching

private theorem reverse_poly (A : Type) [Fintype A] [DecidableEq A] :
    PolyTimeComputable (List.reverse : List A → List A) := by
  obtain ⟨k,hk⟩ := polynomial_absorb 3 1 1
  apply stack_program_polytime (transferProg false (fun b : Bool => b)) false true _ k
  intro w
  let s : Bool → List A := fun b => if b = false then w else []
  refine ⟨_,_, ?_, stack_transfer false (fun b : Bool => b) s, ?_⟩
  · simpa [s] using (show 3*w.length+1 ≤ w.length^k+k by specialize hk w.length; simp at hk; omega)
  · simp [transferStore,s]

private abbrev Alphabet := Option (Bool ⊕ Bool)
private def swapTag : Alphabet ≃ Alphabet := Equiv.optionCongr (Equiv.sumComm Bool Bool)
private def pair (x y : List Bool) : List Alphabet := x.map (some ∘ Sum.inl) ++ none :: y.map (some ∘ Sum.inr)

private theorem premap {A B C : Type} (e : A ↪ B) (f : List B → List C) (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun w : List A => f (w.map e)) := by
  obtain ⟨Γ,hΓ,i,o,M,k,hm⟩ := hf
  refine ⟨Γ,hΓ,e.trans i,o,M,k,fun x => ?_⟩
  simpa only [List.length_map,List.map_map,Function.Embedding.coe_trans] using hm (x.map e)

private theorem swap_rev (x y : List Bool) :
    ((pair x y).reverse.map swapTag) = pair y.reverse x.reverse := by
  simp [pair, List.reverse_append, List.map_append, List.map_reverse, List.map_map,
    Function.comp_def,swapTag,Equiv.optionCongr,Equiv.sumComm,List.append_assoc]

theorem solution (Q R S : TetrisHard.Rows.SearchProblem) (hQR : SearchReduces Q R)
    (hRS : SearchReduces R S) : SearchReduces Q S := by
  obtain ⟨f,g,hf,hg,hr⟩ := hQR
  obtain ⟨F,G,hF,hG,hs⟩ := hRS
  obtain ⟨snd,hSnd,hpr⟩ := polyTimeComputable_pairSnd Bool Bool
  let aux := fun w : List Alphabet => snd (w.map swapTag)
  have hpAux : PolyTimeComputable aux := premap swapTag.toEmbedding snd hSnd
  let fst := List.reverse ∘ aux ∘ List.reverse
  have hpFst : PolyTimeComputable fst := polyTimeComputable_comp _ _ (polyTimeComputable_comp _ _
    (reverse_poly Alphabet) hpAux) (reverse_poly Bool)
  have hfst (x y : List Bool) : fst (pair x y) = x := by
    change (snd (((pair x y).reverse).map swapTag)).reverse = x
    rw [swap_rev,show snd (pair y.reverse x.reverse) = x.reverse from hpr _ _,List.reverse_reverse]
  have hnext := polyTimeComputable_tagged_pair (f ∘ fst) snd
    (polyTimeComputable_comp _ _ hpFst hf) hSnd
  let mid := fun w => G (pair (f (fst w)) (snd w))
  have hmid : PolyTimeComputable mid := polyTimeComputable_comp _ _ hnext hG
  have hlast := polyTimeComputable_tagged_pair fst mid hpFst hmid
  refine ⟨F ∘ f, fun w => g (pair (fst w) (mid w)), polyTimeComputable_comp _ _ hf hF,
    polyTimeComputable_comp _ _ hlast hg, ?_⟩
  intro x hx
  obtain ⟨hfx,hgx⟩ := hr x hx
  obtain ⟨hFx,hGx⟩ := hs (f x) hfx
  refine ⟨hFx,fun y hy => ?_⟩
  change Q.answer x (g (pair (fst (pair x y)) (mid (pair x y))))
  have hy' : snd (pair x y) = y := hpr x y
  simp only [mid,hfst,hy']
  exact hgx _ (hGx y hy)
