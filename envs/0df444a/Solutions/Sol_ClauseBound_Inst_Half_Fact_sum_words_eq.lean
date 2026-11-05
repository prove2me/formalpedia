-- Prove2me | solution 1 for ClauseBound.Inst.Half.Fact.sum_words_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:25:31.172738+00:00
-- url     : https://prove2.me/submissions/00167aa7-a11b-4924-9c8f-325c5142ff26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfIfc
import Definitions.Def_ClauseBound_Inst_HalfFact
import Theorems.Thm_ClauseBound_Inst_Half_Fact_deltaF_eq
import Theorems.Thm_ClauseBound_Inst_Half_Fact_sOf_eq
import Theorems.Thm_ClauseBound_Inst_Half_Fact_abs_le_of_lt
import Theorems.Thm_ClauseBound_Inst_Half_Fact_cap_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg Finset
open ClauseBound.Inst.Half.Fact
namespace ClauseBound.Inst.Half.Fact
theorem _root_.solution (hW : StWords) (hL : StLabs) (hV : StVal) {c₀ c lam : ℕ} {pad : U} (hl : 1 ≤ lam) (hC : Cst c₀ c lam)
    (hp : 2 ^ (c * lam) ≤ pad.length) (tr : Bool) (h' : ℕ) {i : ℕ} (hi : i < 4 * ClauseBound.Part.hOf lam + 1) (a b a' b' : Pieces.Bits lam) :
    ∑ θ ∈ words ((halfF c₀ c).cap tr h' lam i),
        (halfF c₀ c).top ((pad, tr), (h', i), (bitsOf a, bitsOf b, θ)) * (halfF c₀ c).bot ((pad, tr), (h', i), (bitsOf a', bitsOf b', θ))
      = ∑ j ∈ range (2 * ClauseBound.Part.hOf lam + 1), ∑ τ ∈ ClauseBound.Boson.Pz (wOf tr (ClauseBound.Part.hOf lam) ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) j),
          (bif tr then ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ) τ
            else ClauseBound.Boson.topK (ell (ClauseBound.Part.hOf lam) a) (ClauseBound.Part.hOf lam) j ((i : ℤ) - 2 * ClauseBound.Part.hOf lam - ClauseBound.Part.hOf lam + j)
              τ (ell (ClauseBound.Part.hOf lam) b : Multiset ℕ)) *
          (bif tr then ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              τ (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ)
            else ClauseBound.Boson.botK (ell (ClauseBound.Part.hOf lam) b') (ClauseBound.Part.hOf lam) (ClauseBound.Part.hOf lam - ((i : ℤ) - 2 * ClauseBound.Part.hOf lam) - j)
              (ell (ClauseBound.Part.hOf lam) a' : Multiset ℕ) τ) := by
  have hpad : padLen (ClauseBound.Part.hOf lam) ≤ pad.length := by
    rw [padLen, deltaF_eq]
    exact hC.pad.trans hp
  obtain ⟨hlen, hsum, -⟩ := hL tr (ClauseBound.Part.hOf lam) _ (abs_le_of_lt hi)
  rw [cap_eq hC tr h' hi, ← hsum]
  change ∑ θ ∈ words _, partH c₀ true _ * partH c₀ false _ = _
  simp_rw [hV c₀ lam pad hl hC.h_le hpad, sOf_eq hi]
  rw [hW _ _ _ _ _ (by rw [hlen]; exact Nat.le_pow_clog (by norm_num) _)]
  rfl
end ClauseBound.Inst.Half.Fact
