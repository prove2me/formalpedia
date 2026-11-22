-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.ray_prefix_hole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:11.404814+00:00
-- url     : https://prove2.me/submissions/db30cac4-b073-4994-8a48-3b6c6e594ab2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_ray_state_reduce
public import Theorems.Thm_DeciSigma1_Holes_Tail_sat_raySys_iff
public import Theorems.Thm_DeciSigma1_Holes_Tail_onset_le_maxOnset
public import Theorems.Thm_DeciSigma1_Holes_Tail_period_le_maxPeriod
public import Theorems.Thm_DeciSigma1_Holes_Tail_mem_pathChannel_rays
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution [DecidableEq S] (st : ι → S) (Ω : ι → Ray α) (J L : ι → ℕ)
    (hK : ∀ j b p, b ≤ L j → M.admitted p (rayState M (st j) (Ω j) b) = true → b ≤ J j)
    (hlong : ∀ j, J j + maxOnset Ω + 2 * maxPeriod Ω < L j)
    (hself : ∀ i a b, b ≤ J i → a ≤ b →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st i) (Ω i) b) = true →
      ¬ ∀ t, (Ω i).stream (a + t) = (Ω i).stream (b + t))
    (hsat : (raySystem M st Ω J).Sat (fun i => (L i : ℤ))) :
    ∀ i j, ∀ pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
      (streamPrefix (Ω j).stream (L j)), M.admitted pq.1 pq.2 = false := by
  intro i j pq hpq
  rw [mem_pathChannel_rays] at hpq
  obtain ⟨a, ha, b, hb, hlen, hagree, rfl⟩ := hpq
  by_contra hadm
  rw [Bool.not_eq_false] at hadm
  have hbJ := hK j b _ hb hadm
  -- the long agreement is an equality of infinite suffixes
  have hinf : ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
    apply Ray.stream_suffix_eq_of_prefix_eq
    intro t ht
    have h1 := onset_le_maxOnset Ω i
    have h2 := onset_le_maxOnset Ω j
    have h3 := period_le_maxPeriod Ω i
    have h4 := period_le_maxPeriod Ω j
    have h5 := hlong j
    exact (hagree t (by omega)).symm
  by_cases hij : i = j
  · subst hij
    exact hself i a b hbJ (by omega) hadm hinf
  · -- reduce the host cut below the horizon
    obtain ⟨a', ha', hha', hst, hsuf⟩ := ray_state_reduce (M := M) (st i) (Ω i) a
    have := (sat_raySys_iff.mp hsat) i j hij a' hha' b hbJ (by rw [hst]; exact hadm)
      (fun t => (hsuf t).trans (hinf t))
    omega
end DeciSigma1.Holes.Tail
