-- Prove2me | solution 2 for BregmanPPA.ProxMult.theorem8
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-26T14:42:02.788561+00:00
-- url     : https://prove2.me/submissions/5e32122a-b80f-4e84-9bc9-57387f5bfb91

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle
import Theorems.Thm_BregmanPPA_ProxMult_theorem1
import Theorems.Thm_BregmanPPA_ProxMult_K_maximal
import Theorems.Thm_BregmanPPA_ProxMult_sum_bregman
import Theorems.Thm_BregmanPPA_ProxMult_eq13
import Theorems.Thm_BregmanPPA_ProxMult_saddle_iff_zero
import Theorems.Thm_PackedProduct_isBounded_iff

set_option autoImplicit false
open Filter Topology BregmanPPA.ProxMult ThreeOpSplitting.Convergence

/-- Theorem 8, pp. 220-221 (first two sentences): along a run of the nonquadratic proximal
method of multipliers (12), if (10) has a saddle pair (an optimal solution-Lagrange multiplier
pair), then `(x^k, p^k)` converges to one; if it has none, `{x^k}` or `{p^k}` is unbounded. -/
theorem solution {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (Sx : Set (BregmanPPA.IneqMult.E n)) (hx : BregmanPPA.IneqMult.E n → ℝ) (Sp : Set (BregmanPPA.IneqMult.E m)) (hp : BregmanPPA.IneqMult.E m → ℝ)
    (c : ℕ → ℝ) (x : ℕ → BregmanPPA.IneqMult.E n) (p : ℕ → BregmanPPA.IneqMult.E m)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k)
    (hhx : BregmanPPA.Convergence.IsBregmanFunction Sx hx) (hSx : C ⊆ Sx)
    (hhp : BregmanPPA.Convergence.IsBregmanFunction Sp hp) (hSp : BregmanPPA.IneqMult.nonnegOrthant m ⊆ Sp)
    (him : gradient hp '' Sp = Set.univ)
    (hrun : IsProxMultRun C f g Sx hx Sp hp c x p) :
    ((∃ x' p', IsSaddlePair C f g x' p') →
      ∃ x' p', IsSaddlePair C f g x' p' ∧
        Tendsto x atTop (𝓝 x') ∧ Tendsto p atTop (𝓝 p')) ∧
    ((¬ ∃ x' p', IsSaddlePair C f g x' p') →
      ¬ Bornology.IsBounded (Set.range x) ∨ ¬ Bornology.IsBounded (Set.range p)) := by
  -- `sum_bregman` supplies both halves of the reduction to Theorem 1: that `h = hₓ ⊕ hₚ` is a
  -- Bregman function with zone `Sx × Sp`, and that this zone contains `cl dom K`.
  obtain ⟨hprod,hclose⟩ := sum_bregman C f g Sx hx Sp hp hP hhx hSx hhp hSp
  have hdom : dom (opK C f g) ⊆ closure (prodZone Sx Sp) :=
    fun z hz => subset_closure (hclose (subset_closure hz))
  have ht := theorem1 (opK C f g) (prodZone Sx Sp) (sumFn hx hp)
    c (fun k => pair (x k) (p k)) (K_maximal C f g hP) hprod hdom hc hcinf
    (eq13 C f g Sx hx Sp hp c x p hP hc hhx hSx hhp hSp him hrun) (Or.inl hclose)
  constructor
  · rintro ⟨a,b,hs⟩
    have hzero : (zer (opK C f g)).Nonempty :=
      ⟨pair a b,(saddle_iff_zero C f g hP a b).mp hs⟩
    obtain ⟨z,hz,hconv⟩ := ht.1 hzero
    refine ⟨z.ofLp.1,z.ofLp.2,(saddle_iff_zero C f g hP _ _).mpr hz,?_,?_⟩
    · exact ((WithLp.fstL 2 ℝ (BregmanPPA.IneqMult.E n) (BregmanPPA.IneqMult.E m)).continuous.tendsto z).comp hconv
    · exact ((WithLp.sndL 2 ℝ (BregmanPPA.IneqMult.E n) (BregmanPPA.IneqMult.E m)).continuous.tendsto z).comp hconv
  · intro hnone
    have he : zer (opK C f g)=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hnone ⟨z.ofLp.1,z.ofLp.2,(saddle_iff_zero C f g hP _ _).mpr hz⟩
    by_cases hxB : Bornology.IsBounded (Set.range x)
    · right
      intro hpB
      apply ht.2 he hclose
      apply (PackedProduct.isBounded_iff _).mpr
      constructor
      · apply hxB.subset
        rintro _ ⟨z,⟨k,rfl⟩,rfl⟩
        exact ⟨k,rfl⟩
      · apply hpB.subset
        rintro _ ⟨z,⟨k,rfl⟩,rfl⟩
        exact ⟨k,rfl⟩
    · exact Or.inl hxB
