-- Prove2me | solution 1 for BraidsLinksMCG.full_twist_not_of_fin_order
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-29T10:55:19.045543+00:00
-- url     : https://prove2.me/submissions/0f12fbef-3047-44da-9c7f-1b5876907e2c

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option autoImplicit false

open BraidsLinksMCG

/-- The full twist `(σ₁⋯σₙ₋₁)ⁿ` is not of finite order for `n ≥ 3`.

The exponent-sum homomorphism `ε : Bₙ →* Multiplicative ℤ` (the relator
check below is verbatim from the ACCEPTED proof of the in-mission node
`BraidsLinksMCG.braid_exponent_sum_hom`, Gabewhigham 2026-09-14, submission
`7c980466`) sends each Artin generator to `ofAdd 1`, so
`ε ((sigmaProd n) ^ n) = ofAdd (n * (n - 1)) ≠ 1` for `n ≥ 3`.  A
finite-order element would have to map to `1` under any monoid hom —
contradiction. -/
theorem solution (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsOfFinOrder ((sigmaProd n) ^ n) := by
  have hrel : ∀ r ∈ braidRels n,
      (FreeGroup.lift fun _ : Fin (n - 1) => (Multiplicative.ofAdd (1 : ℤ))) r = 1 := by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩) <;>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of] <;> group
  obtain ⟨eps, heps⟩ :
      ∃ eps : ArtinBraidGroup n →* Multiplicative ℤ,
        ∀ i : Fin (n - 1), eps (sigma i) = Multiplicative.ofAdd (1 : ℤ) :=
    ⟨PresentedGroup.toGroup hrel, fun i => PresentedGroup.toGroup.of hrel⟩
  have hofAdd_pow : ∀ (c : ℤ) (m : ℕ),
      (Multiplicative.ofAdd c) ^ m = Multiplicative.ofAdd (m • c) := by
    intro c m
    induction m with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, ← ofAdd_add, succ_nsmul]
  have h1 : eps (sigmaProd n) = ∏ i : Fin (n - 1), eps (sigma i) := by
    simp only [sigmaProd, map_list_prod, List.map_ofFn, List.prod_ofFn,
      Function.comp_apply]
  have hprod : eps (sigmaProd n) = Multiplicative.ofAdd ((n - 1 : ℕ) : ℤ) := by
    rw [h1]
    simp only [heps, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      hofAdd_pow]
    congr 1
    simp
  have hval : eps ((sigmaProd n) ^ n)
      = Multiplicative.ofAdd ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) := by
    rw [map_pow, hprod, hofAdd_pow]
    congr 1
  intro hfin
  obtain ⟨k, hk_pos, hk1⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have h2 := congrArg eps hk1
  rw [map_pow, hval, map_one, hofAdd_pow] at h2
  have h0 : (k : ℤ) * ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) = 0 := by
    have h4 : k • ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) = 0 := ofAdd_eq_one.mp h2
    simpa using h4
  have hpos : (0 : ℤ) < (k : ℤ) * ((n : ℤ) * ((n - 1 : ℕ) : ℤ)) :=
    mul_pos (by exact_mod_cast hk_pos)
      (mul_pos (by exact_mod_cast (by omega : 0 < n))
        (by exact_mod_cast (by omega : 0 < n - 1)))
  exact (ne_of_gt hpos) h0

namespace BraidsLinksMCG

/-- Alias under the published node name: the platform verifier looks up
    `BraidsLinksMCG.full_twist_not_of_fin_order`; `solution` above carries
    the proof.  The type ascription is load-bearing (a bare
    `theorem <name> := solution` fails the server parser). -/
theorem full_twist_not_of_fin_order (n : ℕ) (hn : 3 ≤ n) :
    ¬ IsOfFinOrder ((sigmaProd n) ^ n) :=
  solution n hn

end BraidsLinksMCG
