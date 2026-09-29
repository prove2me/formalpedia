-- Prove2me | solution 1 for BraidsLinksMCG.artin_action_conj_perm
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T11:58:49.123449+00:00
-- url     : https://prove2.me/submissions/a713ef96-e881-4054-80b2-6d094e30a76f

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

open BraidsLinksMCG in
theorem solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (b : ArtinBraidGroup n) (j : Fin n) :
    ∃ A : FreeGroup (Fin n),
      xi b (FreeGroup.of j) = A * FreeGroup.of (pi b j) * A⁻¹ := by
  have happ : ∀ (g h : ArtinBraidGroup n) (x : FreeGroup (Fin n)),
      xi (g * h) x = xi g (xi h x) := by
    intro g h x
    rw [map_mul, MulAut.mul_apply]
  have hinv : ∀ (g : ArtinBraidGroup n) (x : FreeGroup (Fin n)), xi g⁻¹ (xi g x) = x := by
    intro g x
    rw [← happ, inv_mul_cancel, map_one]
    rfl
  have hpinv : ∀ (g : ArtinBraidGroup n) (k : Fin n), pi g ((pi g⁻¹) k) = k := by
    intro g k
    simp
  let S : Subgroup (ArtinBraidGroup n) :=
    { carrier := {c | ∀ k : Fin n, ∃ A : FreeGroup (Fin n),
        xi c (FreeGroup.of k) = A * FreeGroup.of (pi c k) * A⁻¹}
      one_mem' := by
        intro k
        exact ⟨1, by simp⟩
      mul_mem' := by
        rintro c d hc hd k
        obtain ⟨B, hB⟩ := hd k
        obtain ⟨A, hA⟩ := hc (pi d k)
        refine ⟨xi c B * A, ?_⟩
        rw [happ, hB, map_mul, map_mul, map_inv, hA]
        simp [map_mul, mul_assoc]
      inv_mem' := by
        rintro c hc k
        obtain ⟨B, hB⟩ := hc ((pi c⁻¹) k)
        rw [hpinv] at hB
        refine ⟨(xi c⁻¹ B)⁻¹, ?_⟩
        have h2 : FreeGroup.of ((pi c⁻¹) k)
            = xi c⁻¹ B * xi c⁻¹ (FreeGroup.of k) * (xi c⁻¹ B)⁻¹ := by
          have e := congrArg (fun x => xi c⁻¹ x) hB
          rw [hinv] at e
          rw [e, map_mul (xi c⁻¹), map_mul (xi c⁻¹), map_inv (xi c⁻¹)]
        rw [h2]
        group }
  have hgen : ∀ i : Fin (n - 1), sigma i ∈ S := by
    intro i k
    have h1 := hxi i (FreeGroup.of k)
    rw [hpi i]
    simp only [artinEndo, FreeGroup.lift_apply_of] at h1
    by_cases hk : k = strandIdx i
    · subst hk
      refine ⟨FreeGroup.of (strandIdx i), ?_⟩
      rw [h1]
      simp [Equiv.swap_apply_left]
    · by_cases hk2 : k = strandIdxSucc i
      · subst hk2
        refine ⟨1, ?_⟩
        rw [h1]
        simp [hk, Equiv.swap_apply_right]
      · refine ⟨1, ?_⟩
        rw [h1]
        simp [hk, hk2, Equiv.swap_apply_of_ne_of_ne hk hk2]
  have hclos : Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i)) = ⊤ := by
    unfold sigma
    exact PresentedGroup.closure_range_of _
  have hle : Subgroup.closure (Set.range (fun i : Fin (n - 1) => sigma i)) ≤ S :=
    (Subgroup.closure_le S).mpr (by rintro x ⟨i, rfl⟩; exact hgen i)
  have hb : b ∈ S := by
    apply hle
    rw [hclos]
    trivial
  exact hb j
