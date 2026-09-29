-- Prove2me | solution 1 for BraidsLinksMCG.artin_centralizer_inner_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T16:05:31.626012+00:00
-- url     : https://prove2.me/submissions/9debb020-afa8-46e6-a348-a85a7db2951c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_centralizer_common_power_v1

open BraidsLinksMCG

theorem solution
    (n : ℕ)
    (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ k : ℤ, ∀ w : FreeGroup (Fin n),
      beta w =
        freeWordProd n ^ k * w * freeWordProd n ^ (-k) := by
  obtain ⟨k, hk⟩ :=
    artin_centralizer_common_power_v1 n hn beta hcentral hword
  have hhom :
      beta.toMonoidHom =
        (MulAut.conj (freeWordProd n ^ k)).toMonoidHom := by
    apply FreeGroup.ext_hom
    intro j
    change beta (FreeGroup.of j) =
      (MulAut.conj (freeWordProd n ^ k)) (FreeGroup.of j)
    simp only [MulAut.conj_apply]
    rw [← zpow_neg]
    exact hk j
  refine ⟨k, ?_⟩
  intro w
  have h := congrArg (fun f : FreeGroup (Fin n) →* FreeGroup (Fin n) => f w) hhom
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← zpow_neg] using h
