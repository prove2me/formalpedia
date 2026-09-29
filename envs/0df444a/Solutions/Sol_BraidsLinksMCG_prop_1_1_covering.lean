-- Prove2me | solution 1 for BraidsLinksMCG.prop_1_1_covering
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:45:58.229991+00:00
-- url     : https://prove2.me/submissions/2649b691-fd9e-4276-8a40-311542b9fc9d

import Theorems.Thm_BraidsLinksMCG_configProj_isCoveringMap
import Theorems.Thm_TarchaBraids_exists_perm_hom_halfTwist
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG TarchaBraids

/-- The permutations underlying adjacent half-twists generate the symmetric group. -/
private theorem cov_perm_gen (n : ℕ) :
    Subgroup.closure (Set.range (fun i : Fin (n - 1) =>
      Equiv.swap (strandIdx i) (strandIdxSucc i))) = (⊤ : Subgroup (Equiv.Perm (Fin n))) := by
  rcases n with _ | m
  · rw [Subgroup.eq_top_iff']
    intro x
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx]
    exact one_mem _
  · rw [Subgroup.eq_top_iff']
    intro x
    have h1 := Equiv.Perm.mclosure_swap_castSucc_succ m
    have hx : x ∈ Submonoid.closure
        (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [h1]; trivial
    have hsub : Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)
        ≤ (Subgroup.closure (Set.range (fun i : Fin (m + 1 - 1) =>
            Equiv.swap (strandIdx i) (strandIdxSucc i)))).toSubmonoid := by
      refine Submonoid.closure_le.mpr ?_
      rintro y ⟨i, rfl⟩
      refine Subgroup.subset_closure ⟨i, ?_⟩
      have e1 : strandIdx (n := m + 1) i = i.castSucc := by apply Fin.ext; simp [strandIdx]
      have e2 : strandIdxSucc (n := m + 1) i = i.succ := by apply Fin.ext; simp [strandIdxSucc]
      simp only [e1, e2]
    exact hsub hx

theorem _root_.solution (n : ℕ) :
    IsCoveringMap (configProj n) ∧
      ∃ nu : GeomBraidGroup n →* Equiv.Perm (Fin n),
        Function.Surjective nu ∧
        nu.ker = (FundamentalGroup.map (configProj n) (baseOrdered n)).range := by
  refine ⟨BraidsLinksMCG.configProj_isCoveringMap n, ?_⟩
  obtain ⟨nu, hnu, hker⟩ := TarchaBraids.exists_perm_hom_halfTwist n
  refine ⟨nu, ?_, hker⟩
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← cov_perm_gen n]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨i, rfl⟩
  exact ⟨halfTwistBraid n i, hnu i⟩

#print axioms solution
