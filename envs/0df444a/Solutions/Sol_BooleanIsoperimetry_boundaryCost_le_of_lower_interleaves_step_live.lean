-- Prove2me | solution 1 for BooleanIsoperimetry.boundaryCost_le_of_lower_interleaves_step_live
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:50:02.239971+00:00
-- url     : https://prove2.me/submissions/4c2b03ea-5b9e-4912-8f56-6e5ba7c4aa4d

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Macaulay
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Shadow
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_Harper
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_q_zero_total_le_one
public import Theorems.Thm_BooleanIsoperimetry_H_ge_self
public import Theorems.Thm_BooleanIsoperimetry_H_shadow_GT_sum
public import Theorems.Thm_BooleanIsoperimetry_H_shadow_LE_sum
public import Theorems.Thm_BooleanIsoperimetry_canonical_boundaryCost_eq_H_add
public import Theorems.Thm_BooleanIsoperimetry_cascade_p_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_q_le
public import Theorems.Thm_BooleanIsoperimetry_cascade_split_add


set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry
namespace BooleanIsoperimetry
theorem _root_.solution
    (n p q a b p0 p1 q0 q1 a0 a1 b0 b1 : ℕ)
    (_ : ∀ m, m < n + 1 → ∀ x y, x ≤ 2 ^ m → y ≤ 2 ^ m →
            H (m + 1) (x + y) ≤ max (H m x) y + max (H m y) x)
    (ha_cap : a ≤ 2 ^ (n + 1)) (hb_cap : b ≤ 2 ^ (n + 1))
    (hba : b ≤ a)
    (hpq_casc : CascadeSplit (n + 1) (a + b) p q)
    (hp : CascadeSplit n p p0 p1) (hq : CascadeSplit n q q0 q1)
    (_ : CascadeSplit n a a0 a1) (hb : CascadeSplit n b b0 b1)
    (_ : ∀ l,
      splitPrefixMass n a0 b0 (l + 1) + splitPrefixMass n a1 b1 l
        ≤ splitPrefixMass n p0 q0 (l + 1) + splitPrefixMass n p1 q1 l) :
    max (H (n + 1) p) q + max (H (n + 1) q) p ≤
      max (H (n + 1) a) b + max (H (n + 1) b) a := by
  -- A IS NOW PROVED (cycle16 manual branch) from the upper-shadow / Macaulay
  -- layer in `BooleanIsoperimetry/Shadow.lean`: the max-form boundary step
  -- collapses (sorry-free) to the two scalar Macaulay shadow-sum leaves
  -- `BooleanIsoperimetry.H_shadow_LE_sum` (LE regime) and
  -- `BooleanIsoperimetry.H_shadow_GT_sum` (GT regime), exactly as in
  -- `boundaryCost_le_of_LE_GT_sums` but routed through the new shadow leaves
  -- instead of through this lemma (so the dependency is acyclic).  The remaining
  -- sorries live only in those two named PDF-layer leaves, which via
  -- `H_shadow_closed_form` are pure `upperShadow` (Kruskal–Katona/Macaulay)
  -- inequalities — see `H_shadow_LE_sum_as_upperShadow`.  The slice/profile data
  -- (`hp hq ha hb h_lower`) is not needed for this collapse and is retained only
  -- to preserve the public signature.
  --
  -- HISTORICAL OBSTRUCTION NOTE (kept for context; the shadow layer is the way
  -- past it).  Earlier cycles established that the max-form leaf is genuinely
  -- 2-dimensional:
  -- This was the single load-bearing sorry: `harper_macaulay_exchange_step`,
  -- `harper_macaulay_LE_sum(_pos)`, `harper_macaulay_GT_sum`,
  -- `boundaryCost_le_of_LE_GT_sums`, `boundaryCost_le_of_interleaves_core` and
  -- `harper_macaulay_joint` all reduce to it; there is no independent route.
  -- The statement is TRUE (exhaustive cascade model of `H`, no violation for all
  -- capacity-bounded `a,b` with split dimension `n+1 ≤ 4`).  The remaining gap is
  -- formalization depth, not falsity.  Three natural routes are provably blocked
  -- with current infrastructure:
  --
  -- (1) ABEL-SUMMATION ROUTE IS DEAD.  The cascade Abel lemma
  --     `int_sum_mul_le_of_prefix_le_of_antitone_weight` would close A if the
  --     boundary cost `H (n+1) p + H (n+1) q` were a fixed antitone-weighted sum
  --     of the `splitPrefixMass` quantities that `h_lower` controls.  It is NOT:
  --     `H` is not any fixed-weight linear function of the split prefix masses
  --     (best-fit weights have strictly positive residual at every `n`, and are
  --     neither nonnegative nor antitone).  This is the precise sense of the file
  --     note "prefix masses alone do not determine boundary cost".
  -- (2) VERTICAL/HORIZONTAL MISMATCH.  `H (n+1) p = max (H n p0) p1 + max (H n p1) p0`
  --     couples a block with its OWN two level-`n` slices ("vertical"), whereas
  --     `h_lower` and the cascade domination couple the `0`-slices `(p0,q0)` and
  --     `1`-slices `(p1,q1)` across blocks ("horizontal").  The transpose
  --     regrouping `bc_n(p0,p1)+bc_n(q0,q1) ≤ bc_n(p0,q0)+bc_n(p1,q1)` is FALSE
  --     (counterexamples already at `n=2`), so the two level-`n` `ih`/`harper_extremal_n`
  --     applications cannot be combined by a one-directional exchange.  This is
  --     why single-step `IsUpMove`/`blockDist` descent (cycle14) and rowwise
  --     recombination were shown insufficient.
  -- (3) NO KRUSKAL–KATONA BRIDGE.  The honest proof needs the Macaulay shadow
  --     closed form `H N (binomPrefix N r + t) = binomPrefix N (r+1) + Δ(N,r,t)`,
  --     where `Δ` is the upper-shadow size of the first `t` rank-`r` vertices, plus
  --     the KK extremality of colex/simplicial initial segments for that shadow.
  --     mathlib's `Finset.kruskal_katona` lives over `Finset (Finset (Fin n))`
  --     colex shadows, with no bridge to this repo's `Cube`/`neighborhood`/`H`.
  --
  -- MINIMAL NEXT LEMMAS that would make A closeable (all currently MISSING, all
  -- empirically checkable against the cascade model):
  --   (a) `H_shadow_closed_form`:  H N (binomPrefix N r + t) = binomPrefix N (r+1)
  --        + upperShadow N r t,  with `upperShadow` defined and shown monotone in `t`.
  --   (b) `upperShadow_kruskal_katona`:  the cascade (KK) lower bound on `upperShadow`
  --        / its superadditivity under merging two layer-initial segments.
  --   (c) `boundaryCost_eq_layerSum`:  a representation of `H (n+1) p + H (n+1) q`
  --        as a sum over layers of `upperShadow` contributions of the DOUBLY-canonical
  --        profile `(p0,p1,q0,q1)` (which is canonical in both directions: verified
  --        that `(p0,q0)` and `(p1,q1)` are each canonical level-`n` cascade splits),
  --        reducing A to a per-layer shadow comparison driven by `h_lower`.
  -- See AGENT_RESULT_CURRENT.md for the full analysis and empirical evidence.
  --
  -- PROOF.  Collapse the outer boundary `max`s and dispatch to the shadow leaves.
  have hp_cap : p ≤ 2 ^ (n + 1) := cascade_p_le hpq_casc
  have hq_cap : q ≤ 2 ^ (n + 1) := cascade_q_le hpq_casc
  by_cases hq_zero : q = 0
  · subst hq_zero
    have htot : a + b ≤ 1 := cascade_split_q_zero_total_le_one hpq_casc
    have hb0 : b = 0 := by omega
    subst hb0
    have ha_eq_p : a = p := by
      have hsum := cascade_split_add hpq_casc
      omega
    subst ha_eq_p
    exact le_rfl
  · have hq_pos : 1 ≤ q := Nat.pos_of_ne_zero hq_zero
    rw [canonical_boundaryCost_eq_H_add hp_cap hq_cap hq_pos hpq_casc]
    by_cases hcase : a ≤ H (n + 1) b
    · have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha_cap)
      rw [max_eq_left hbHa, max_eq_left hcase]
      exact BooleanIsoperimetry.H_shadow_LE_sum ha_cap hb_cap hpq_casc hq_pos hba hcase
    · push Not at hcase
      have hbHa : b ≤ H (n + 1) a := le_trans hba (H_ge_self (n + 1) a ha_cap)
      rw [max_eq_left hbHa, max_eq_right (le_of_lt hcase)]
      exact BooleanIsoperimetry.H_shadow_GT_sum ha_cap hb_cap hpq_casc hq_pos hba hcase
end BooleanIsoperimetry
