-- Prove2me | solution 1 for BookProof.ChapterA.System.schur_normal_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:37:52.23029+00:00
-- url     : https://prove2.me/submissions/cbf15fc4-7cfa-44a3-a0ca-724645bfae27

import Mathlib
import Definitions.Def_ChapterA
open BookProof.ChapterA BookProof.ChapterA.System
open scoped ComplexConjugate InnerProductSpace
variable {𝔽 : Type*} [RCLike 𝔽] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V]

private lemma orthogonal_subsystem (M : System 𝔽 V) (hM : IsNormal M)
    {W : Submodule 𝔽 V} (hW : IsSubsystem M W) : IsSubsystem M Wᗮ := by
  refine ⟨W.isClosed_orthogonal, ?_⟩
  intro m hm w hw
  rw [Submodule.mem_orthogonal] at hw ⊢
  intro v hv
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hw _ (hW.2 _ (hM m hm) _ hv)

theorem solution (M : System 𝔽 V) (hM : IsNormal M)
    (hSchur : ∀ S : V →L[𝔽] V, M.Commutes S → IsSelfAdjoint S →
      ∃ c : 𝔽, S = c • (1 : V →L[𝔽] V)) : IsIrreducible M := by
  intro W hW
  let : CompleteSpace W := hW.1.completeSpace_coe
  have hc : M.Commutes W.starProjection := by
    intro m hm
    ext x
    change W.starProjection (m x) = m (W.starProjection x)
    apply Submodule.eq_starProjection_of_mem_orthogonal
      (hW.2 m hm _ (W.starProjection_apply_mem x))
    have ho := (orthogonal_subsystem M hM hW).2 m hm
      (x - W.starProjection x) (W.sub_starProjection_mem_orthogonal x)
    simpa only [map_sub] using ho
  obtain ⟨c, hc⟩ := hSchur W.starProjection hc (isSelfAdjoint_starProjection W)
  by_cases hb : W = ⊥
  · exact Or.inl hb
  · right
    obtain ⟨w, hw, hn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    have he : c • w = w := by
      simpa using (congrArg (fun T : V →L[𝔽] V => T w) hc).symm.trans
        (W.starProjection_eq_self_iff.mpr hw)
    have hz : (c - 1) • w = 0 := by rw [sub_smul, one_smul, he, sub_self]
    have hc1 : c = 1 := sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_right hn)
    apply top_unique
    intro x hx
    apply W.starProjection_eq_self_iff.mp
    simp [hc, hc1]

#print axioms solution
