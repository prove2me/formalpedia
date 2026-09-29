-- Prove2me | solution 1 for Chou.noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T19:00:46.469881+00:00
-- url     : https://prove2.me/submissions/9bbcedd3-68b1-4b11-b5cb-bb83360d2715

import Theorems.Thm_Chou_isLocallyFinite_of_elementaryAmenable_of_isMulTorsion
import Definitions.Def_Chou_ElementaryAmenable
import Definitions.Def_Chou_Classes
import Mathlib

/-! # Chou §2: Propositions 2.1 and 2.2

`Constructible` is closed under subgroups and quotients (one structural induction proving both at
once — Chou's transfinite induction), hence coincides with `ElementaryAmenable`. -/

universe u

namespace Chou
namespace Lib

open Subgroup QuotientGroup

end Lib
end Chou

/-! # Chou §2: Theorem 2.3 and Corollary 2.4 -/


namespace Chou
namespace Lib

open Subgroup QuotientGroup

/-! ### Small tools -/

/-! ### Locally finite groups -/

/-! ### Periodic groups lie in NF; NF ∖ EG is nonempty -/

theorem noFreeSubgroupOfRankTwo_of_isMulTorsion' {G : Type*} [Group G] (ht : IsMulTorsion G) :
    NoFreeSubgroupOfRankTwo G := by
  intro f hf
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp (ht (f (FreeGroup.of 0)))
  have h1 : (FreeGroup.of (0 : Fin 2)) ^ n = 1 := hf (by rw [map_pow, hpow, map_one])
  have h2 := congrArg (FreeGroup.lift (fun _ : Fin 2 => Multiplicative.ofAdd (1 : ℤ))) h1
  simp only [map_pow, FreeGroup.lift_apply_of, map_one, ← ofAdd_nsmul, ofAdd_eq_one,
    nsmul_eq_mul, mul_one] at h2
  omega

/-- Theorem 2.3, the step on p. 398: a non-locally finite periodic group lies in `NF \ EG`. -/
theorem noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite' {G : Type u} [Group G]
    (ht : IsMulTorsion G) (hnl : ¬ IsLocallyFinite G) :
    NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G :=
  ⟨noFreeSubgroupOfRankTwo_of_isMulTorsion' ht,
    fun hG => hnl (Chou.isLocallyFinite_of_elementaryAmenable_of_isMulTorsion hG ht)⟩

/-! ### Corollary 2.4 -/

end Lib
end Chou

open Chou

theorem solution {G : Type*} [Group G]
    (ht : IsMulTorsion G) (hnl : ¬ IsLocallyFinite G) :
    NoFreeSubgroupOfRankTwo G ∧ ¬ ElementaryAmenable G :=
  Chou.Lib.noFreeSubgroupOfRankTwo_and_not_elementaryAmenable_of_isMulTorsion_of_not_isLocallyFinite' ht hnl
