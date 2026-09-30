-- Prove2me | solution 1 for BraidsLinksMCG.artin_centralizer_conj_form_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-29T11:55:28.432242+00:00
-- url     : https://prove2.me/submissions/45459071-70d4-44b0-80d0-fa90f402308a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Theorems.Thm_BraidsLinksMCG_artin_centralizer_conj_perm_index_v1

open BraidsLinksMCG

theorem solution
    (n : ℕ)
    (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
      ∀ j : Fin n,
        beta (FreeGroup.of j) =
          A j * FreeGroup.of (mu j) * (A j)⁻¹ := by
  obtain ⟨mu, hmu⟩ :=
    artin_centralizer_conj_perm_index_v1 n hn beta hcentral
  exact ⟨mu, fun j => Classical.choose (hmu j),
    fun j => Classical.choose_spec (hmu j)⟩

theorem artin_centralizer_conj_form_v1
    (n : ℕ)
    (hn : 3 ≤ n)
    (beta : MulAut (FreeGroup (Fin n)))
    (hcentral : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
      beta (artinEndo n i w) = artinEndo n i (beta w))
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
      ∀ j : Fin n,
        beta (FreeGroup.of j) =
          A j * FreeGroup.of (mu j) * (A j)⁻¹ :=
  solution n hn beta hcentral hword
