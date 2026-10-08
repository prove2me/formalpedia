-- Prove2me | solution 1 for BertsekasShreve.Contraction.fixed_point_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T20:13:39.310377+00:00
-- url     : https://prove2.me/submissions/ce565400-4a0e-4eb3-8fe1-94f23c4fb8a5

import Mathlib

set_option autoImplicit false

open Filter Topology in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Bbar : Set E) (hclosed : IsClosed Bbar) (hne : Bbar.Nonempty)
    (L : Bbar → Bbar) (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hL : ∀ z z' : Bbar, ‖((L^[m] z : Bbar) : E) - ((L^[m] z' : Bbar) : E)‖ ≤
      ρ * ‖(z : E) - (z' : E)‖) :
    ∃ zs : Bbar, L zs = zs ∧ (∀ z : Bbar, L z = z → z = zs) ∧
      ∀ z : Bbar, Tendsto (fun N : ℕ => ‖((L^[N] z : Bbar) : E) - (zs : E)‖) atTop (𝓝 0) := by
  have : CompleteSpace Bbar := hclosed.completeSpace_coe
  have : Nonempty Bbar := hne.to_subtype
  have hdist : ∀ a b : Bbar, dist a b = ‖(a : E) - (b : E)‖ := fun a b => by
    rw [Subtype.dist_eq, dist_eq_norm]
  set K : NNReal := ⟨ρ, hρ0.le⟩ with hKdef
  have hK : (K : ℝ) = ρ := rfl
  have hLip : LipschitzWith K (L^[m]) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [hdist, hdist, hK]; exact hL a b
  have hc : ContractingWith K (L^[m]) := ⟨by rw [← NNReal.coe_lt_coe, hK]; simpa using hρ1, hLip⟩
  set x := hc.fixedPoint (L^[m]) with hx
  have hfix : L x = x := hc.isFixedPt_fixedPoint_iterate
  have hxm : ∀ q : ℕ, (L^[m])^[q] x = x := fun q =>
    Function.iterate_fixed hc.fixedPoint_isFixedPt q
  refine ⟨x, hfix, ?_, ?_⟩
  · intro z hz
    apply hc.fixedPoint_unique
    exact Function.iterate_fixed hz m
  · intro z
    set C : ℝ := ∑ r ∈ Finset.range m, dist (L^[r] z) x
    have hbound : ∀ N : ℕ, ‖((L^[N] z : Bbar) : E) - (x : E)‖ ≤ ρ ^ (N / m) * C := by
      intro N
      rw [← hdist]
      have hN : L^[N] z = (L^[m])^[N / m] (L^[N % m] z) := by
        rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.div_add_mod]
      rw [hN]
      calc dist ((L^[m])^[N / m] (L^[N % m] z)) x
          = dist ((L^[m])^[N / m] (L^[N % m] z)) ((L^[m])^[N / m] x) := by rw [hxm]
        _ ≤ (K : ℝ) ^ (N / m) * dist (L^[N % m] z) x := by
            have := (hLip.iterate (N / m)).dist_le_mul (L^[N % m] z) x
            simpa [NNReal.coe_pow] using this
        _ ≤ ρ ^ (N / m) * C := by
            rw [hK]
            gcongr
            exact Finset.single_le_sum (f := fun r => dist (L^[r] z) x)
              (fun r _ => dist_nonneg) (Finset.mem_range.2 (Nat.mod_lt N hm))
    have hdiv : Tendsto (fun N : ℕ => N / m) atTop atTop := by
      refine tendsto_atTop_atTop.2 fun b => ⟨b * m, fun n hn => ?_⟩
      exact (Nat.le_div_iff_mul_le hm).2 hn
    have hlim : Tendsto (fun N : ℕ => ρ ^ (N / m) * C) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).comp hdiv).mul_const C
      simpa using this
    exact squeeze_zero (fun N => norm_nonneg _) hbound hlim
