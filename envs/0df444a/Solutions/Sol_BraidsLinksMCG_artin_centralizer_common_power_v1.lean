-- Prove2me | solution 1 for BraidsLinksMCG.artin_centralizer_common_power_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T16:50:39.190407+00:00
-- url     : https://prove2.me/submissions/36a11d43-8b46-4c31-b1b7-9a95645d1d63
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_form_v1
import Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_form_common_power_v1

open BraidsLinksMCG

theorem solution
    (n : ℕ)
    (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ k : ℤ, ∀ j : Fin n,
      beta (FreeGroup.of j) =
        (freeWordProd n) ^ k * FreeGroup.of j *
          (freeWordProd n) ^ (-k) := by
  obtain ⟨mu, A, hA⟩ :=
    artin_centralizer_conj_form_v1 n hn beta hcentral hword
  exact
    artin_centralizer_conj_form_common_power_v1 n hn beta hcentral hword
      ⟨mu, A, hA⟩
