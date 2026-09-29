-- Prove2me | solution 1 for BraidsLinksMCG.artin_conjugators_trivializable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:25:23.279726+00:00
-- url     : https://prove2.me/submissions/a7051f0d-bb8b-4e65-b2e9-f575537386fe

import Theorems.Thm_BraidsLinksMCG_artin_conjugator_norm_reduction
import Theorems.Thm_BraidsLinksMCG_artin_action_conj_perm
import Theorems.Thm_BraidsLinksMCG_artin_action_fixes_word
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace TrivSol

/-- Precomposing an Artin-type endomorphism with a braid action preserves the
"generator goes to a conjugate of a generator" condition. -/
theorem comp_conj (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i))
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (c : ArtinBraidGroup n) :
    ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
      ∀ i : Fin n, ((xi c).toMonoidHom.comp beta) (FreeGroup.of i)
        = A i * FreeGroup.of (mu i) * (A i)⁻¹ := by
  classical
  obtain ⟨mu, A, hA⟩ := hconj
  choose B hB using fun j : Fin n =>
    BraidsLinksMCG.artin_action_conj_perm n xi hxi pi hpi c j
  refine ⟨(pi c) * mu, fun i => xi c (A i) * B (mu i), fun i => ?_⟩
  show xi c (beta (FreeGroup.of i)) = _
  rw [hA i, map_mul, map_mul, map_inv, hB (mu i)]
  simp only [Equiv.Perm.mul_apply]
  group

/-- Precomposing preserves the condition of fixing `x₁ ⋯ xₙ`. -/
theorem comp_word (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hword : beta (freeWordProd n) = freeWordProd n)
    (c : ArtinBraidGroup n) :
    ((xi c).toMonoidHom.comp beta) (freeWordProd n) = freeWordProd n := by
  show xi c (beta (freeWordProd n)) = freeWordProd n
  rw [hword]
  exact BraidsLinksMCG.artin_action_fixes_word n xi hxi c

end TrivSol

open TrivSol

/-- Induction on the total reduced length of the generator images. -/
theorem aux (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (pi : ArtinBraidGroup n →* Equiv.Perm (Fin n))
    (hpi : ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i)) :
    ∀ (N : ℕ) (beta : FreeGroup (Fin n) →* FreeGroup (Fin n)),
      (∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹) →
      beta (freeWordProd n) = freeWordProd n →
      (∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i))) ≤ N →
      ∃ b : ArtinBraidGroup n, ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, xi b (beta (FreeGroup.of i)) = FreeGroup.of (nu i) := by
  intro N
  induction N with
  | zero =>
    intro beta hconj hword hle
    by_cases hperm : ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)
    · obtain ⟨nu, hnu⟩ := hperm
      refine ⟨1, nu, fun i => ?_⟩
      rw [hnu i, map_one]
      rfl
    · exfalso
      obtain ⟨c, hc⟩ := BraidsLinksMCG.artin_conjugator_norm_reduction n xi hxi beta
        hconj hword hperm
      omega
  | succ N ih =>
    intro beta hconj hword hle
    by_cases hperm : ∃ nu : Equiv.Perm (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = FreeGroup.of (nu i)
    · obtain ⟨nu, hnu⟩ := hperm
      refine ⟨1, nu, fun i => ?_⟩
      rw [hnu i, map_one]
      rfl
    · obtain ⟨c, hc⟩ := BraidsLinksMCG.artin_conjugator_norm_reduction n xi hxi beta
        hconj hword hperm
      have hle' : (∑ i : Fin n,
          FreeGroup.norm (((xi c).toMonoidHom.comp beta) (FreeGroup.of i))) ≤ N := by omega
      obtain ⟨b', nu, hb'⟩ := ih ((xi c).toMonoidHom.comp beta)
        (TrivSol.comp_conj n xi hxi pi hpi beta hconj c)
        (TrivSol.comp_word n xi hxi beta hword c) hle'
      refine ⟨b' * c, nu, fun i => ?_⟩
      have := hb' i
      rw [map_mul]
      show xi b' (xi c (beta (FreeGroup.of i))) = _
      exact this

theorem _root_.solution (n : ℕ)
    (xi : ArtinBraidGroup n →* MulAut (FreeGroup (Fin n)))
    (hxi : ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n), xi (sigma i) w = artinEndo n i w)
    (beta : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (hconj : ∃ mu : Equiv.Perm (Fin n), ∃ A : Fin n → FreeGroup (Fin n),
        ∀ i : Fin n, beta (FreeGroup.of i) = A i * FreeGroup.of (mu i) * (A i)⁻¹)
    (hword : beta (freeWordProd n) = freeWordProd n) :
    ∃ b : ArtinBraidGroup n, ∃ nu : Equiv.Perm (Fin n),
      ∀ i : Fin n, xi b (beta (FreeGroup.of i)) = FreeGroup.of (nu i) := by
  obtain ⟨pi, hpi⟩ := BraidsLinksMCG.braid_perm_hom n
  exact aux n xi hxi pi hpi (∑ i : Fin n, FreeGroup.norm (beta (FreeGroup.of i)))
    beta hconj hword le_rfl

#print axioms solution
