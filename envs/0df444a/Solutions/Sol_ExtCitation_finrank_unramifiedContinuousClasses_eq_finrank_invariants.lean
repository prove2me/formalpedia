-- Prove2me | solution 1 for ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e6b89700-4093-5750-8965-a93b89c0329c

import Mathlib
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ExtCitation_LocalLevelSubgroupsPD
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ExtCitation_exists_frobenius_pow_inv_mul_mem_inertia_sup_level
import Theorems.Thm_ExtCitation_exists_level_dvd_of_frobenius_pow_mem_inertia_sup
import Theorems.Thm_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants
p2m_attr_erase "instance" "instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete"

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (q : Nat.Primes)
    (M : Rep (ZMod p) (primeLocalGaloisGroup q)) [FiniteDimensional (ZMod p) M]
    (hsm : ∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      FiniteDimensional ℚ F ∧
        ∀ s, primeLocalToGlobal q s ∈ F.fixingSubgroup → M.ρ s m = m)
    (adm_ur : Submodule (ZMod p) (H1 M)) [FiniteDimensional (ZMod p) adm_ur]
    (hadm_ur : ∀ x, x ∈ adm_ur ↔ ∃ c : cocycles₁ M,
      (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ (g s : primeLocalGaloisGroup q),
          primeLocalToGlobal q s ∈ F.fixingSubgroup → c.val (g * s) = c.val g)
      ∧ (∃ m : M, ∀ g : primeLocalGaloisGroup q,
          primeLocalToGlobal q g ∈ (primeLocalPlace q).inertiaSubgroupIn ℚ → c.val g = M.ρ g m - m)
      ∧ (H1π M).hom c = x) :
    finrank (ZMod p) adm_ur = finrank (ZMod p) M.ρ.invariants := by
  obtain ⟨φ, hφ⟩ := ExtCitation.exists_isFrobeniusAt_apply_primeLocalToGlobal q
  refine ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth
    q M hsm φ ?_ ?_ adm_ur hadm_ur
  ·
    intro F _ _ x
    induction x using QuotientGroup.induction_on with | H g =>
    obtain ⟨n, hn⟩ := ExtCitation.exists_frobenius_pow_inv_mul_mem_inertia_sup_level q φ hφ F g
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq]
    exact hn
  ·
    intro F₀ hF₀ n hn
    haveI := hF₀
    obtain ⟨F, hF₀F, hFfin, hdiv⟩ :=
      ExtCitation.exists_level_dvd_of_frobenius_pow_mem_inertia_sup q φ hφ F₀ n hn
    haveI := hFfin
    haveI : Normal ℚ (AlgebraicClosure ℚ) := by
      convert @IsAlgClosure.normal ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) inferInstance
      rfl
    refine ⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ),
      normalClosure.is_finiteDimensional ℚ F _, normalClosure.normal ℚ F _,
      hF₀F.trans (IntermediateField.le_normalClosure F), fun j hj => hdiv j ?_⟩
    exact (sup_le_sup_left (Subgroup.comap_mono
      (IntermediateField.fixingSubgroup_antitone (IntermediateField.le_normalClosure F))) _) hj

end S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants
end P2MW
export P2MW.S_ExtCitation_finrank_unramifiedContinuousClasses_eq_finrank_invariants (solution)
