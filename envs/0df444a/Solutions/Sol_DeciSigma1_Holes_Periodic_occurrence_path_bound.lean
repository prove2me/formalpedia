-- Prove2me | solution 1 for DeciSigma1.Holes.Periodic.occurrence_path_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:41:03.122153+00:00
-- url     : https://prove2.me/submissions/5eb8c98d-d159-4020-9ad6-513529c90ec3

module
public import Mathlib.Tactic.Positivity.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Deletion
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Periodic_Bound
public import Theorems.Thm_DeciSigma1_Holes_Periodic_simplePath_le_pow_split

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Periodic
open DeciSigma1.Arithmetic DeciSigma1.Words
variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α} {ρ : List α}
variable {N : ℕ} {z : {P // P ∈ piecesOf W ρ} → ℤ}
namespace DeciSigma1.Holes.Periodic
theorem _root_.solution {h t : ℕ} (split : OccurrenceSplit W ρ h t)
    (p : List {P // P ∈ piecesOf W ρ}) (hnd : p.Nodup)
    (hp : p.IsChain (fun P Q => FollowerEdge P.val Q.val)) :
    p.length ≤ (t + 1) * 2 ^ h - 1 := by
  classical
  let head : {P // P ∈ piecesOf W ρ} → Prop := fun P => split.head P.val
  have hb := simplePath_le_pow_split (fun P : {P // P ∈ piecesOf W ρ} => P.val.follower)
    head h p hnd hp (by
      intro c _ hc hcomp
      let c' := c.image (fun P => P.val)
      have hcard : c'.card = c.card := Finset.card_image_of_injective _ Subtype.val_injective
      rw [← hcard]
      apply split.head_bound c'
      · intro P hP
        obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
        exact Q.property
      · intro P hP
        obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
        exact hc Q hQ
      · intro P hP Q hQ
        obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
        obtain ⟨Q', hQ', rfl⟩ := Finset.mem_image.mp hQ
        exact hcomp P' hP' Q' hQ')
  let q := p.filter (fun P => decide (¬ head P))
  have hqnd : q.Nodup := hnd.filter _
  have ht : q.length ≤ t := by
    let c := q.toFinset.image (fun P => P.val)
    have hc : c.card = q.length := by
      rw [Finset.card_image_of_injective _ Subtype.val_injective, List.toFinset_card_of_nodup hqnd]
    rw [← hc]
    apply split.tail_bound c
    · intro P hP
      obtain ⟨Q, _, rfl⟩ := Finset.mem_image.mp hP
      exact Q.property
    · intro P hP
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
      have := List.mem_filter.mp (List.mem_toFinset.mp hQ)
      exact of_decide_eq_true this.2
  have hmul := Nat.mul_le_mul_right (2 ^ h) (Nat.add_le_add_right ht 1)
  change p.length + 1 ≤ (q.length + 1) * 2 ^ h at hb
  omega
end DeciSigma1.Holes.Periodic
