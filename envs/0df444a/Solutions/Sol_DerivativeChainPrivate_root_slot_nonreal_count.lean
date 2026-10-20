-- Prove2me | solution 1 for DerivativeChainPrivate.root_slot_nonreal_count
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-18T01:49:35.719988+00:00
-- url     : https://prove2.me/submissions/a7108a6b-7ea8-45e1-9fa7-2fe860d06f4d

import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_nonreal_roots_of_real_polynomial

set_option autoImplicit false
open DerivativeChainPrivate

theorem solution {n : ℕ} (a : Fin n → ℂ) (p : Polynomial ℝ)
    (hp : p.map Complex.ofRealHom = fromRoots a) :
    p.natDegree - p.roots.card = nonrealCount a := by
  classical
  have hprod : fromRoots a ≠ 0 := by
    exact (Polynomial.monic_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (a i))).ne_zero
  have hroots : (fromRoots a).roots = Finset.univ.val.map a := by
    unfold fromRoots
    rw [Polynomial.roots_prod _ _ hprod]
    simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  rw [← DerivativeChainPrivate.nonreal_roots_of_real_polynomial p, hp, hroots]
  simp [nonrealCount, Multiset.filter_map, ← Finset.filter_val]
