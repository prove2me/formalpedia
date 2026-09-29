-- Prove2me | solution 1 for BraidsLinksMCG.center_le_ker_perm
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:48:35.508699+00:00
-- url     : https://prove2.me/submissions/5cb084a2-ca81-448e-84d2-6a2747828b43

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace CenterPure

/-- The symmetric group on at least three letters has trivial centre. -/
theorem perm_center_eq_bot (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.center (Equiv.Perm (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, s a ≠ a := by
    by_contra h
    push_neg at h
    exact hne (Equiv.ext h)
  obtain ⟨c, hc⟩ : ∃ c : Fin n, c ∉ ({a, s a} : Finset (Fin n)) := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {a, s a} := fun x _ => h x
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    have h2 : ({a, s a} : Finset (Fin n)).card ≤ 2 := by
      refine (Finset.card_insert_le _ _).trans ?_
      simp
    omega
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  have hcomm := (Subgroup.mem_center_iff.mp hs) (Equiv.swap (s a) c)
  have happ := congrArg (fun e : Equiv.Perm (Fin n) => e a) hcomm
  simp only [Equiv.Perm.mul_apply] at happ
  rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hca),
    Equiv.swap_apply_left] at happ
  exact hcb happ

/-- The permutations underlying adjacent half-twists generate the symmetric group. -/
private theorem adj_perm_gen (n : ℕ) :
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


theorem perm_hom_surjective (n : ℕ)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i)) :
    Function.Surjective pi := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← adj_perm_gen n]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨i, rfl⟩
  exact ⟨sigma i, hpi i⟩

end CenterPure

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i)) :
    Subgroup.center (ArtinBraidGroup n) ≤ pi.ker := by
  intro b hb
  rw [MonoidHom.mem_ker]
  have hsurj := CenterPure.perm_hom_surjective n pi hpi
  have hcen : pi b ∈ Subgroup.center (Equiv.Perm (Fin n)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := hsurj g
    rw [← map_mul, ← map_mul]
    exact congrArg pi (Subgroup.mem_center_iff.mp hb a)
  rw [CenterPure.perm_center_eq_bot n hn, Subgroup.mem_bot] at hcen
  exact hcen

#print axioms solution
