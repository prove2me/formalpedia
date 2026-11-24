-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.mulLast_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:49:17.953678+00:00
-- url     : https://prove2.me/submissions/3db5ab96-7420-4232-81c1-4b1af47de3df

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_nil
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_cons
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wd_snoc
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_raising_criterion_holds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_withTop_shift
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_X
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_last_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset Formalism.CountingSumsFrames
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ)
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (hj : K + 1 ≤ j) (hv : LL.vec (Fin.last K) = true)
    (g : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hg : X (Fin.last K, (0 : Fin r)) * g ∈ YCond p LL j M) :
    g ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
  have hcrit := raising_criterion_holds p (K + 1) r LL j M
  have hcrit' := raising_criterion_holds p (K + 1) r LL j (M + ((-1 : ℤ) : WithTop ℤ))
  have hcomm : ∀ d : Fin r, ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      glAct p LL j 0 d (X (Fin.last K, (0 : Fin r)) * x) =
        X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x +
          (if d = 0 then X (Fin.last K, (0 : Fin r)) * x else 0) := by
    intro d x
    rw [glAct_mul, last_X p LL j hj hv]
    split_ifs
    · ring
    · simp
  have hP : ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ l : List (Fin r), wd p LL j l (X (Fin.last K, (0 : Fin r)) * x) ∈ SuppLE p LL j M) →
      ∀ d : Fin r, ∀ l : List (Fin r),
        wd p LL j l (X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x) ∈ SuppLE p LL j M := by
    intro x hx d l
    have e : X (Fin.last K, (0 : Fin r)) * glAct p LL j 0 d x =
        glAct p LL j 0 d (X (Fin.last K, (0 : Fin r)) * x) -
          (if d = 0 then X (Fin.last K, (0 : Fin r)) * x else 0) := by
      rw [hcomm]; abel
    rw [e, map_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [← wd_snoc]; exact hx _
    · split_ifs
      · exact hx l
      · rw [map_zero]; exact Submodule.zero_mem _
  have hC : ∀ l : List (Fin r), ∀ x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      (∀ l', wd p LL j l' (X (Fin.last K, (0 : Fin r)) * x) ∈ SuppLE p LL j M) →
      ∀ l', wd p LL j l' (X (Fin.last K, (0 : Fin r)) * wd p LL j l x) ∈ SuppLE p LL j M := by
    intro l
    induction l with
    | nil => intro x hx; simpa only [wd_nil] using hx
    | cons d l ih => intro x hx; rw [wd_cons]; exact hP _ (ih x hx) d
  have hB : ∀ y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      X (Fin.last K, (0 : Fin r)) * y ∈ SuppLE p LL j M →
        y ∈ SuppLE p LL j (M + ((-1 : ℤ) : WithTop ℤ)) := by
    intro y hy
    rw [X_mul_mem, mem_restrictSupport_iff] at hy
    rw [mem_restrictSupport_iff]
    refine hy.trans ?_
    intro m hm
    simp only [Set.mem_setOf_eq, last_wt LL j hj hv] at hm ⊢
    rw [← withTop_shift]
    simpa using hm
  have hg0 : ∀ l : List (Fin r), wd p LL j l (X (Fin.last K, (0 : Fin r)) * g) ∈ SuppLE p LL j M :=
    (hcrit _).mp hg
  refine (hcrit' g).mpr fun l => ?_
  have := hC l g hg0 []
  rw [wd_nil] at this
  exact hB _ this
end Formalism.InvariantFactorPaths.L4
