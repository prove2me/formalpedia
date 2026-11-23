-- Prove2me | solution 1 for CoDecompFO.fold_codes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:42:06.881672+00:00
-- url     : https://prove2.me/submissions/8da7e900-1d15-44c4-8986-ec2d8c70316a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CoDecompFO_AltMatrix
import Definitions.Def_CoDecompFO_Fold
import Definitions.Def_CoDecompFO_CodeFold
import Definitions.Def_CoDecompFO_Codes
import Theorems.Thm_CoDecompFO_codeFold_simulation
import Theorems.Thm_CoDecompFO_numeric_hth_codecs

set_option autoImplicit false

open FirstOrder
open CoDecompFO

/-- **Tables of hypotheticals as numbers** (Bumpus et al., *Co-Decompositions and FO Model Checking*,
arXiv:2611.04658, held file sha256 d550d7af…, Lemma 5.81, p.41: "For fixed signature σ, formula φ, and
width w, the number of reduced hypotheticals that can occur over a bag of size at most w is bounded by a
function of w and |φ|"; proof of Theorem 1.16, p.41; ¶5.80, p.41).

For each `σ` there are primitive recursive functions `leaf`, `join`, `acc` on lists of numbers and a
computable bound `B` such that, for every `φ` and every `T` of width at most `w`: every table of a
bottom-up computation with `leaf` and `join` on the code of `φ` is at most `B(w,|φ|)`; and for a root
table `v`, `acc` on the code of `φ` and `v` is `1` or `0`, and it is `1` iff, when the limit is non-empty,
some root table `H` of the bottom-up computation of hypotheticals over `T°` passes alternating evaluation
of `altMatrix φ`, and, when the limit is empty, `φ` holds in it.

**Formalization Note** No machine occurs. On an empty limit every `∀` holds and the alternating form is not
equivalent to `φ`; the truth of `φ` then depends only on the nullary relations of the bags, which the
tables may carry. -/
theorem solution (σ : Sig) :
    ∃ (leaf join acc : List ℕ → ℕ) (B : ℕ → ℕ → ℕ),
      Primrec leaf ∧ Primrec join ∧ Primrec acc ∧ (∀ l, acc l ≤ 1) ∧ Computable₂ B ∧
      ∀ (T : CoDecomp σ) (φ : σ.lang.Sentence) (w : ℕ), width T ≤ w →
        (∀ (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ),
          T.CodeFold r (encF φ) leaf join t S v → v ≤ B w (sentLen φ)) ∧
        (∀ (r : Fin T.b) (v : ℕ), T.CodeFold r (encF φ) leaf join r Set.univ v →
          (IsEmpty T.Lim → (acc (frame [encF φ, [v] ]) = 1 ↔ T.Lim ⊨ φ)) ∧
          (Nonempty T.Lim →
            ∃ H : HTh (sigmaEq σ) (Fin (T.withEq.bag r).n) (2 * quantCount φ) (quantCount φ),
              T.withEq.IsFold r (2 * quantCount φ) (quantCount φ) r Set.univ H ∧
              (acc (frame [encF φ, [v] ]) = 1 ↔ eval (altMatrix φ) (quantCount φ) H))) := by
  obtain ⟨leaf, join, acc, B, hleaf_rec, hjoin_rec, hacc_rec, hacc_le, hB, hcodecs⟩ :=
    numeric_hth_codecs σ
  refine ⟨leaf, join, acc, B, hleaf_rec, hjoin_rec, hacc_rec, hacc_le, hB, ?_⟩
  intro T φ w hTw
  obtain ⟨code, hleaf, hjoin, hbound, heval, hempty⟩ := hcodecs φ w
  have hsim (r t : Fin T.b) (S : Set (Fin T.b)) (v : ℕ)
      (hfold : T.CodeFold r (encF φ) leaf join t S v) :=
    codeFold_simulation σ φ w (B w (sentLen φ)) leaf join code hleaf hjoin hbound
      T hTw r t S v hfold
  refine ⟨fun r t S v hfold => (hsim r t S v hfold).1, ?_⟩
  intro r v hfold
  obtain ⟨hv, H, hIf, hHv⟩ := hsim r r Set.univ v hfold
  refine ⟨fun hs => hempty T hTw r v hfold hs, ?_⟩
  intro _
  refine ⟨H, hIf, ?_⟩
  rw [← hHv, heval _ H]
